#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict


def write_msg(proc: subprocess.Popen, obj: Dict[str, Any]) -> None:
    data = json.dumps(obj, ensure_ascii=False) + "\n"
    assert proc.stdin is not None
    proc.stdin.write(data.encode("utf-8"))
    proc.stdin.flush()


def read_msg(proc: subprocess.Popen) -> Dict[str, Any]:
    assert proc.stdout is not None
    line = proc.stdout.readline()
    if not line:
        raise RuntimeError("EOF while reading response line")
    return json.loads(line.decode("utf-8", errors="replace"))


def smoke(server_cmd: list[str]) -> Dict[str, Any]:
    proc = subprocess.Popen(
        server_cmd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        write_msg(
            proc,
            {
                "jsonrpc": "2.0",
                "id": 1,
                "method": "initialize",
                "params": {"protocolVersion": "2025-06-18", "capabilities": {}, "clientInfo": {}},
            },
        )
        init = read_msg(proc)
        write_msg(proc, {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
        tools = read_msg(proc)
        return {"initialize": init, "tools": tools}
    finally:
        proc.kill()


def main() -> None:
    root = Path(__file__).resolve().parents[3]
    servers = {
        "repo-index": ["python3", str(root / "theme/mcp/servers/repo_index_server.py"), "--workspace", str(root)],
        "tex-parser": ["python3", str(root / "theme/mcp/servers/tex_parser_server.py"), "--workspace", str(root)],
        "lake-build": ["python3", str(root / "theme/mcp/servers/lake_build_server.py"), "--workspace", str(root)],
        "lean-lsp": ["python3", str(root / "theme/mcp/servers/lean_lsp_server.py"), "--workspace", str(root)],
    }

    out: Dict[str, Any] = {}
    for name, cmd in servers.items():
        out[name] = smoke(cmd)

    print(json.dumps(out, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
