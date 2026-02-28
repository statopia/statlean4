#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

from common import resolve_under, workspace_root
from mcp_stdio import MCPServer

DEFAULT_ENVS = ["theorem", "lemma", "corollary", "proposition", "definition"]


def extract_blocks(tex: str, envs: List[str]) -> List[Dict[str, Any]]:
    env_alt = "|".join(re.escape(x) for x in envs)
    begin_pat = re.compile(r"\\begin\{(" + env_alt + r")\}(?:\[([^\]]*)\])?", re.IGNORECASE)
    blocks: List[Dict[str, Any]] = []
    starts = list(begin_pat.finditer(tex))

    for i, m in enumerate(starts):
        env = m.group(1).lower()
        title = (m.group(2) or "").strip()
        start = m.end()
        end_pat = re.compile(r"\\end\{" + re.escape(env) + r"\}", re.IGNORECASE)
        end_m = end_pat.search(tex, pos=start)
        if not end_m:
            continue

        statement = tex[start:end_m.start()].strip()
        next_start = starts[i + 1].start() if i + 1 < len(starts) else len(tex)
        proof_pat = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.IGNORECASE | re.DOTALL)
        proof_m = proof_pat.search(tex, pos=end_m.end(), endpos=next_start)
        proof = proof_m.group(1).strip() if proof_m else ""

        blocks.append(
            {
                "index": i + 1,
                "kind": env,
                "title": title or f"{env.title()} {i + 1}",
                "statement": statement,
                "proof": proof,
                "statement_chars": len(statement),
                "proof_chars": len(proof),
            }
        )
    return blocks


def main() -> None:
    ap = argparse.ArgumentParser(description="tex-parser MCP server")
    ap.add_argument("--workspace", default=None)
    args = ap.parse_args()

    root = workspace_root(args.workspace)
    self_dir = Path(__file__).resolve().parent
    from_tex_script = (self_dir.parent.parent / "scripts" / "from_tex.py").resolve()

    server = MCPServer(
        name="tex-parser",
        version="0.1.0",
        instructions="Parse theorem blocks from TeX and optionally generate theme/input package files.",
    )

    def extract_theorems(params: Dict[str, Any]) -> Dict[str, Any]:
        tex_path = params.get("tex_path")
        if not tex_path:
            raise ValueError("tex_path is required")
        path = resolve_under(root, tex_path)
        envs = params.get("theorem_envs", DEFAULT_ENVS)
        if not isinstance(envs, list) or not envs:
            envs = DEFAULT_ENVS

        tex = path.read_text(encoding="utf-8", errors="ignore")
        blocks = extract_blocks(tex, [str(x) for x in envs])
        return {
            "tex_path": str(path),
            "count": len(blocks),
            "items": blocks,
        }

    def build_input_package(params: Dict[str, Any]) -> Dict[str, Any]:
        tex_path = params.get("tex_path")
        input_dir = params.get("input_dir")
        if not tex_path or not input_dir:
            raise ValueError("tex_path and input_dir are required")

        path = resolve_under(root, tex_path)
        out_dir = resolve_under(root, input_dir)
        namespace = str(params.get("namespace", "Formalization.Imported"))
        layer = str(params.get("layer", "formalization"))

        cmd = [
            sys.executable,
            str(from_tex_script),
            str(path),
            str(out_dir),
            "--namespace",
            namespace,
            "--layer",
            layer,
        ]
        proc = subprocess.run(cmd, cwd=str(root), text=True, capture_output=True, check=False)
        return {
            "exit_code": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "input_dir": str(out_dir),
            "files": [
                str(out_dir / "paper.tex"),
                str(out_dir / "theorems.yaml"),
                str(out_dir / "notation.yaml"),
                str(out_dir / "scope.yaml"),
            ],
        }

    def detect_math_commands(params: Dict[str, Any]) -> Dict[str, Any]:
        tex_path = params.get("tex_path")
        if not tex_path:
            raise ValueError("tex_path is required")
        path = resolve_under(root, tex_path)
        text = path.read_text(encoding="utf-8", errors="ignore")

        cmds: Dict[str, int] = {}
        for m in re.finditer(r"\\([A-Za-z]+)", text):
            k = m.group(1)
            cmds[k] = cmds.get(k, 0) + 1

        top_n = int(params.get("top_n", 50))
        items = sorted(cmds.items(), key=lambda kv: kv[1], reverse=True)[:top_n]
        return {
            "tex_path": str(path),
            "top": [{"command": c, "count": n} for c, n in items],
        }

    server.add_tool(
        name="extract_theorems",
        description="Extract theorem-like blocks and adjacent proof text from a tex file.",
        input_schema={
            "type": "object",
            "properties": {
                "tex_path": {"type": "string"},
                "theorem_envs": {
                    "type": "array",
                    "items": {"type": "string"},
                },
            },
            "required": ["tex_path"],
            "additionalProperties": False,
        },
        handler=extract_theorems,
    )

    server.add_tool(
        name="build_input_package",
        description="Generate theme input files (paper/theorems/notation/scope) from a tex file.",
        input_schema={
            "type": "object",
            "properties": {
                "tex_path": {"type": "string"},
                "input_dir": {"type": "string"},
                "namespace": {"type": "string"},
                "layer": {"type": "string", "enum": ["statlib", "formalization"]},
            },
            "required": ["tex_path", "input_dir"],
            "additionalProperties": False,
        },
        handler=build_input_package,
    )

    server.add_tool(
        name="detect_math_commands",
        description="Count top LaTeX commands used in a tex file.",
        input_schema={
            "type": "object",
            "properties": {
                "tex_path": {"type": "string"},
                "top_n": {"type": "integer"},
            },
            "required": ["tex_path"],
            "additionalProperties": False,
        },
        handler=detect_math_commands,
    )

    server.run()


if __name__ == "__main__":
    main()
