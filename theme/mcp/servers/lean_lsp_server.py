#!/usr/bin/env python3
from __future__ import annotations

import argparse
import shutil
from pathlib import Path
from typing import Any, Dict, List

from common import parse_lean_diagnostics, resolve_under, run_cmd, workspace_root
from mcp_stdio import MCPServer


def read_line_window(path: Path, center_line: int, radius: int = 4) -> str:
    text = path.read_text(encoding="utf-8", errors="ignore")
    lines = text.splitlines()
    c = max(1, center_line)
    s = max(1, c - radius)
    e = min(len(lines), c + radius)
    out = []
    for i in range(s, e + 1):
        marker = ">" if i == c else " "
        out.append(f"{marker}{i:5d}: {lines[i - 1]}")
    return "\n".join(out)


def main() -> None:
    ap = argparse.ArgumentParser(description="lean-lsp compatibility MCP server")
    ap.add_argument("--workspace", default=None)
    args = ap.parse_args()

    root = workspace_root(args.workspace)

    server = MCPServer(
        name="lean-lsp",
        version="0.1.0",
        instructions=(
            "Lean diagnostics/search compatibility server. "
            "Note: get_goal is best-effort via CLI diagnostics, not a full interactive LSP goal state."
        ),
    )

    def get_diagnostics(params: Dict[str, Any]) -> Dict[str, Any]:
        workspace = resolve_under(root, params.get("workspace", "."))
        timeout_sec = int(params.get("timeout_sec", 600))
        file_path = params.get("file")

        if file_path:
            file_abs = resolve_under(workspace, file_path)
            cmd = ["lake", "env", "lean", str(file_abs)]
        else:
            cmd = ["lake", "build"]

        res = run_cmd(cmd, cwd=workspace, timeout_sec=timeout_sec)
        combo = (res.get("stdout", "") + "\n" + res.get("stderr", "")).strip()
        diags = parse_lean_diagnostics(combo)
        return {
            "cmd": cmd,
            "workspace": str(workspace),
            "exit_code": res["exit_code"],
            "diagnostics": diags,
            "stdout": res["stdout"],
            "stderr": res["stderr"],
        }

    def find_symbol(params: Dict[str, Any]) -> Dict[str, Any]:
        workspace = resolve_under(root, params.get("workspace", "."))
        query = params.get("query", "")
        if not query:
            raise ValueError("query is required")

        kinds = params.get("kinds", [
            "theorem", "lemma", "def", "irreducible_def",
            "structure", "class", "abbrev",
        ])
        if not isinstance(kinds, list) or not kinds:
            kinds = [
                "theorem", "lemma", "def", "irreducible_def",
                "structure", "class", "abbrev",
            ]
        kind_alt = "|".join(str(k) for k in kinds)

        # Modifiers (protected/noncomputable/private/unsafe/partial/nonrec)
        # may appear before the declaration keyword and must not block the
        # match — `protected irreducible_def Measure.pi` and `noncomputable
        # irreducible_def MeasureTheory.condExp` are core Mathlib APIs that
        # the previous pattern silently missed. czy ba49507 fix ported to
        # SDK-bridge per CZY_NEW_PUSH_AUDIT §4.E (S2 NEW HIGH-VALUE).
        modifier_prefix = (
            r"(?:protected\s+|noncomputable\s+|private\s+|unsafe\s+|"
            r"partial\s+|nonrec\s+)*"
        )
        regex = rf"^\s*{modifier_prefix}({kind_alt})\s+.*{query}"
        if shutil.which("rg"):
            cmd = ["rg", "-n", "--hidden", "--no-ignore-vcs", regex, str(workspace)]
        else:
            cmd = [
                "grep",
                "-RInE",
                "--binary-files=without-match",
                "--include=*.lean",
                regex,
                str(workspace),
            ]
        res = run_cmd(
            cmd,
            cwd=workspace,
            timeout_sec=int(params.get("timeout_sec", 120)),
        )
        hits = [ln for ln in res["stdout"].splitlines() if ln.strip()]
        return {
            "query": query,
            "hits": hits,
            "exit_code": res["exit_code"],
        }

    def get_goal(params: Dict[str, Any]) -> Dict[str, Any]:
        workspace = resolve_under(root, params.get("workspace", "."))
        file_path = params.get("file")
        line = int(params.get("line", 1))
        col = int(params.get("col", 1))
        if not file_path:
            raise ValueError("file is required")

        file_abs = resolve_under(workspace, file_path)

        # Best-effort fallback: run checker and report nearest diagnostic + local source window.
        res = run_cmd(
            ["lake", "env", "lean", str(file_abs)],
            cwd=workspace,
            timeout_sec=int(params.get("timeout_sec", 600)),
        )
        combo = (res.get("stdout", "") + "\n" + res.get("stderr", "")).strip()
        diags = parse_lean_diagnostics(combo)
        same_file = [d for d in diags if Path(d["file"]).name == file_abs.name]

        nearest = None
        if same_file:
            nearest = min(same_file, key=lambda d: abs(int(d["line"]) - line) + abs(int(d["col"]) - col))

        try:
            snippet = read_line_window(file_abs, line)
        except Exception:
            snippet = ""

        return {
            "note": (
                "Best-effort goal approximation only. "
                "For true interactive goals, connect a full Lean LSP MCP implementation."
            ),
            "file": str(file_abs),
            "line": line,
            "col": col,
            "nearest_diagnostic": nearest,
            "source_window": snippet,
        }

    server.add_tool(
        name="get_diagnostics",
        description="Run Lean checks and return parsed diagnostics.",
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {"type": "string"},
                "file": {"type": "string"},
                "timeout_sec": {"type": "integer"},
            },
            "required": [],
            "additionalProperties": False,
        },
        handler=get_diagnostics,
    )

    server.add_tool(
        name="find_symbol",
        description="Find theorem/lemma/def-like declarations with regex search.",
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {"type": "string"},
                "query": {"type": "string"},
                "kinds": {
                    "type": "array",
                    "items": {"type": "string"},
                },
                "timeout_sec": {"type": "integer"},
            },
            "required": ["query"],
            "additionalProperties": False,
        },
        handler=find_symbol,
    )

    server.add_tool(
        name="get_goal",
        description="Best-effort goal context around a file position (compatibility fallback).",
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {"type": "string"},
                "file": {"type": "string"},
                "line": {"type": "integer"},
                "col": {"type": "integer"},
                "timeout_sec": {"type": "integer"},
            },
            "required": ["file", "line", "col"],
            "additionalProperties": False,
        },
        handler=get_goal,
    )

    server.run()


if __name__ == "__main__":
    main()
