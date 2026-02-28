#!/usr/bin/env python3
from __future__ import annotations

import argparse
import shutil
from pathlib import Path
from typing import Any, Dict, List

from mcp_stdio import MCPServer
from common import resolve_under, run_cmd, workspace_root


def main() -> None:
    ap = argparse.ArgumentParser(description="repo-index MCP server")
    ap.add_argument("--workspace", default=None)
    args = ap.parse_args()

    root = workspace_root(args.workspace)

    server = MCPServer(
        name="repo-index",
        version="0.1.0",
        instructions=(
            "Search and read repository files. All paths are constrained to the configured workspace."
        ),
    )

    def search(args: Dict[str, Any]) -> Dict[str, Any]:
        pattern = args.get("pattern", "")
        if not pattern:
            raise ValueError("pattern is required")
        rel_root = args.get("root", ".")
        scan_root = resolve_under(root, rel_root)
        glob = args.get("glob")
        max_results = int(args.get("max_results", 200))
        context = int(args.get("context", 0))

        if shutil.which("rg"):
            cmd: List[str] = [
                "rg",
                "-n",
                "--hidden",
                "--no-ignore-vcs",
                "--max-count",
                str(max_results),
            ]
            if context > 0:
                cmd.extend(["-C", str(context)])
            if glob:
                cmd.extend(["-g", str(glob)])
            cmd.append(pattern)
            cmd.append(str(scan_root))
        else:
            cmd = [
                "grep",
                "-RInE",
                "--binary-files=without-match",
                pattern,
                str(scan_root),
            ]

        res = run_cmd(cmd, cwd=root, timeout_sec=int(args.get("timeout_sec", 120)))
        return res

    def list_files(args: Dict[str, Any]) -> Dict[str, Any]:
        rel_root = args.get("root", ".")
        scan_root = resolve_under(root, rel_root)
        glob = args.get("glob")
        max_files = int(args.get("max_files", 1000))

        if shutil.which("rg"):
            cmd: List[str] = ["rg", "--files", str(scan_root)]
            if glob:
                cmd.extend(["-g", str(glob)])
            res = run_cmd(cmd, cwd=root, timeout_sec=int(args.get("timeout_sec", 120)))
            files = [ln for ln in res["stdout"].splitlines() if ln.strip()]
        else:
            find_cmd: List[str] = ["find", str(scan_root), "-type", "f"]
            if glob:
                find_cmd.extend(["-name", glob])
            res = run_cmd(find_cmd, cwd=root, timeout_sec=int(args.get("timeout_sec", 120)))
            files = [ln for ln in res["stdout"].splitlines() if ln.strip()]
        files = files[:max_files]
        res["files"] = files
        return res

    def read_file(args: Dict[str, Any]) -> Dict[str, Any]:
        path = args.get("path")
        if not path:
            raise ValueError("path is required")
        file_path = resolve_under(root, path)
        text = file_path.read_text(encoding="utf-8", errors="ignore")

        start_line = int(args.get("start_line", 1))
        end_line = int(args.get("end_line", 0))
        max_chars = int(args.get("max_chars", 20000))

        lines = text.splitlines()
        s = max(1, start_line)
        e = len(lines) if end_line <= 0 else min(len(lines), end_line)
        snippet = "\n".join(lines[s - 1 : e])
        if len(snippet) > max_chars:
            snippet = snippet[:max_chars]

        return {
            "path": str(file_path),
            "start_line": s,
            "end_line": e,
            "content": snippet,
        }

    server.add_tool(
        name="search",
        description="Regex search in workspace via ripgrep.",
        input_schema={
            "type": "object",
            "properties": {
                "pattern": {"type": "string"},
                "root": {"type": "string"},
                "glob": {"type": "string"},
                "max_results": {"type": "integer"},
                "context": {"type": "integer"},
                "timeout_sec": {"type": "integer"},
            },
            "required": ["pattern"],
            "additionalProperties": False,
        },
        handler=search,
    )

    server.add_tool(
        name="list_files",
        description="List files in workspace (optionally filtered by glob).",
        input_schema={
            "type": "object",
            "properties": {
                "root": {"type": "string"},
                "glob": {"type": "string"},
                "max_files": {"type": "integer"},
                "timeout_sec": {"type": "integer"},
            },
            "required": [],
            "additionalProperties": False,
        },
        handler=list_files,
    )

    server.add_tool(
        name="read_file",
        description="Read file content with optional line range.",
        input_schema={
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "start_line": {"type": "integer"},
                "end_line": {"type": "integer"},
                "max_chars": {"type": "integer"},
            },
            "required": ["path"],
            "additionalProperties": False,
        },
        handler=read_file,
    )

    server.run()


if __name__ == "__main__":
    main()
