#!/usr/bin/env python3
from __future__ import annotations

import argparse
import shutil
from pathlib import Path
from typing import Any, Dict, List

from common import parse_lean_diagnostics, resolve_under, run_cmd, workspace_root
from mcp_stdio import MCPServer


def main() -> None:
    ap = argparse.ArgumentParser(description="lake-build MCP server")
    ap.add_argument("--workspace", default=None)
    args = ap.parse_args()

    root = workspace_root(args.workspace)

    server = MCPServer(
        name="lake-build",
        version="0.1.0",
        instructions="Build and hygiene tools for Lean projects using lake/lean CLI.",
    )

    def build(params: Dict[str, Any]) -> Dict[str, Any]:
        workspace = resolve_under(root, params.get("workspace", "."))
        timeout_sec = int(params.get("timeout_sec", 1200))
        target = params.get("target", "")

        cmd: List[str] = ["lake", "build"]
        if target:
            cmd.append(str(target))

        res = run_cmd(cmd, cwd=workspace, timeout_sec=timeout_sec)
        combo = (res.get("stdout", "") + "\n" + res.get("stderr", "")).strip()
        res["diagnostics"] = parse_lean_diagnostics(combo)
        return res

    def lean_file(params: Dict[str, Any]) -> Dict[str, Any]:
        workspace = resolve_under(root, params.get("workspace", "."))
        file_path = params.get("file")
        if not file_path:
            raise ValueError("file is required")
        file_abs = resolve_under(workspace, file_path)
        timeout_sec = int(params.get("timeout_sec", 600))

        cmd = ["lake", "env", "lean", str(file_abs)]
        res = run_cmd(cmd, cwd=workspace, timeout_sec=timeout_sec)
        combo = (res.get("stdout", "") + "\n" + res.get("stderr", "")).strip()
        res["diagnostics"] = parse_lean_diagnostics(combo)
        return res

    def hygiene_scan(params: Dict[str, Any]) -> Dict[str, Any]:
        workspace = resolve_under(root, params.get("workspace", "."))
        scan_root = resolve_under(workspace, params.get("scan_root", "."))

        if shutil.which("rg"):
            sorry = run_cmd(["rg", "-n", "\\bsorry\\b", str(scan_root)], cwd=workspace)
            axiom = run_cmd(["rg", "-n", "^\\s*axiom\\b", str(scan_root)], cwd=workspace)
        else:
            sorry = run_cmd(
                ["grep", "-RInE", "--include=*.lean", "([^A-Za-z0-9_]|^)sorry([^A-Za-z0-9_]|$)", str(scan_root)],
                cwd=workspace,
            )
            axiom = run_cmd(
                ["grep", "-RInE", "--include=*.lean", "^[[:space:]]*axiom([[:space:]]|$)", str(scan_root)],
                cwd=workspace,
            )

        sorry_hits = [ln for ln in sorry["stdout"].splitlines() if ln.strip()]
        axiom_hits = [ln for ln in axiom["stdout"].splitlines() if ln.strip()]

        return {
            "scan_root": str(scan_root),
            "sorry_count": len(sorry_hits),
            "axiom_count": len(axiom_hits),
            "sorry_hits": sorry_hits,
            "axiom_hits": axiom_hits,
        }

    server.add_tool(
        name="build",
        description="Run `lake build` (optionally with target) and return diagnostics.",
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {"type": "string"},
                "target": {"type": "string"},
                "timeout_sec": {"type": "integer"},
            },
            "required": [],
            "additionalProperties": False,
        },
        handler=build,
    )

    server.add_tool(
        name="lean_file",
        description="Type-check one Lean file via `lake env lean <file>`.",
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {"type": "string"},
                "file": {"type": "string"},
                "timeout_sec": {"type": "integer"},
            },
            "required": ["file"],
            "additionalProperties": False,
        },
        handler=lean_file,
    )

    server.add_tool(
        name="hygiene_scan",
        description="Scan Lean files for sorry/axiom usage.",
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {"type": "string"},
                "scan_root": {"type": "string"},
            },
            "required": [],
            "additionalProperties": False,
        },
        handler=hygiene_scan,
    )

    server.run()


if __name__ == "__main__":
    main()
