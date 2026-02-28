#!/usr/bin/env python3
"""Minimal stdio MCP server framework with no third-party dependencies.

Implements a pragmatic subset used by Codex MCP clients:
- initialize
- ping
- tools/list
- tools/call

Transport: JSON-RPC 2.0 over stdio with Content-Length framing.
Also accepts line-delimited JSON requests as a fallback.
"""

from __future__ import annotations

import json
import sys
import traceback
from dataclasses import dataclass
from typing import Any, Callable, Dict, Optional

JSON = Dict[str, Any]


@dataclass
class ToolSpec:
    name: str
    description: str
    input_schema: JSON
    handler: Callable[[JSON], Any]


class MCPServer:
    def __init__(self, name: str, version: str = "0.1.0", instructions: str = "") -> None:
        self.name = name
        self.version = version
        self.instructions = instructions
        self.tools: Dict[str, ToolSpec] = {}
        self.client_protocol_version: Optional[str] = None

    def add_tool(
        self,
        *,
        name: str,
        description: str,
        input_schema: JSON,
        handler: Callable[[JSON], Any],
    ) -> None:
        self.tools[name] = ToolSpec(
            name=name,
            description=description,
            input_schema=input_schema,
            handler=handler,
        )

    def run(self) -> None:
        while True:
            msg = self._read_message()
            if msg is None:
                return
            self._handle_message(msg)

    def _handle_message(self, msg: JSON) -> None:
        method = msg.get("method")
        msg_id = msg.get("id", None)

        if method is None:
            if msg_id is not None:
                self._send_error(msg_id, -32600, "Invalid Request: missing method")
            return

        # Notifications have no id.
        is_notification = msg_id is None

        try:
            if method == "initialize":
                result = self._handle_initialize(msg.get("params", {}))
                if not is_notification:
                    self._send_result(msg_id, result)
                return

            if method == "initialized":
                return

            if method == "ping":
                if not is_notification:
                    self._send_result(msg_id, {})
                return

            if method == "tools/list":
                result = {
                    "tools": [
                        {
                            "name": t.name,
                            "description": t.description,
                            "inputSchema": t.input_schema,
                        }
                        for t in self.tools.values()
                    ]
                }
                if not is_notification:
                    self._send_result(msg_id, result)
                return

            if method == "tools/call":
                params = msg.get("params", {})
                tool_name = params.get("name")
                args = params.get("arguments", {})
                if tool_name not in self.tools:
                    if not is_notification:
                        self._send_result(
                            msg_id,
                            {
                                "isError": True,
                                "content": [
                                    {
                                        "type": "text",
                                        "text": f"Unknown tool: {tool_name}",
                                    }
                                ],
                            },
                        )
                    return

                tool = self.tools[tool_name]
                try:
                    payload = tool.handler(args if isinstance(args, dict) else {})
                    result = self._tool_result(payload, is_error=False)
                except Exception as exc:  # pylint: disable=broad-except
                    tb = traceback.format_exc()
                    result = self._tool_result(
                        {
                            "error": str(exc),
                            "traceback": tb,
                        },
                        is_error=True,
                    )
                if not is_notification:
                    self._send_result(msg_id, result)
                return

            if not is_notification:
                self._send_error(msg_id, -32601, f"Method not found: {method}")
        except Exception as exc:  # pylint: disable=broad-except
            if not is_notification:
                self._send_error(msg_id, -32000, f"Server error: {exc}")

    def _handle_initialize(self, params: JSON) -> JSON:
        self.client_protocol_version = params.get("protocolVersion")
        protocol = self.client_protocol_version or "2025-06-18"
        return {
            "protocolVersion": protocol,
            "capabilities": {
                "tools": {
                    "listChanged": False,
                }
            },
            "serverInfo": {
                "name": self.name,
                "version": self.version,
            },
            "instructions": self.instructions,
        }

    @staticmethod
    def _tool_result(payload: Any, is_error: bool) -> JSON:
        if isinstance(payload, str):
            return {
                "isError": is_error,
                "content": [{"type": "text", "text": payload}],
            }
        text = json.dumps(payload, ensure_ascii=False, indent=2)
        out: JSON = {
            "isError": is_error,
            "content": [{"type": "text", "text": text}],
        }
        if isinstance(payload, (dict, list)):
            out["structuredContent"] = payload
        return out

    def _send_result(self, msg_id: Any, result: JSON) -> None:
        self._write_message(
            {
                "jsonrpc": "2.0",
                "id": msg_id,
                "result": result,
            }
        )

    def _send_error(self, msg_id: Any, code: int, message: str) -> None:
        self._write_message(
            {
                "jsonrpc": "2.0",
                "id": msg_id,
                "error": {
                    "code": code,
                    "message": message,
                },
            }
        )

    @staticmethod
    def _write_message(obj: JSON) -> None:
        # Codex MCP client expects line-delimited JSON on stdio transport.
        data = json.dumps(obj, ensure_ascii=False)
        sys.stdout.write(data + "\n")
        sys.stdout.flush()

    @staticmethod
    def _read_message() -> Optional[JSON]:
        line = sys.stdin.buffer.readline()
        if not line:
            return None

        # Fallback: newline-delimited JSON.
        if line[:1] == b"{":
            try:
                return json.loads(line.decode("utf-8", errors="replace"))
            except json.JSONDecodeError:
                return None

        headers: Dict[str, str] = {}
        while line not in (b"\r\n", b"\n", b""):
            if b":" in line:
                k, v = line.decode("ascii", errors="replace").split(":", 1)
                headers[k.strip().lower()] = v.strip()
            line = sys.stdin.buffer.readline()
            if not line:
                return None

        try:
            length = int(headers.get("content-length", "0"))
        except ValueError:
            return None

        if length <= 0:
            return None

        body = sys.stdin.buffer.read(length)
        if not body:
            return None

        try:
            return json.loads(body.decode("utf-8", errors="replace"))
        except json.JSONDecodeError:
            return None
