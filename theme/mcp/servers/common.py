#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Any, Dict, List


def workspace_root(path: str | None) -> Path:
    if path:
        return Path(path).expanduser().resolve()
    return Path.cwd().resolve()


def resolve_under(root: Path, p: str) -> Path:
    target = Path(p).expanduser()
    if not target.is_absolute():
        target = (root / target)
    target = target.resolve()
    try:
        target.relative_to(root)
    except ValueError as exc:
        raise ValueError(f"Path escapes workspace: {target}") from exc
    return target


def run_cmd(cmd: List[str], cwd: Path, timeout_sec: int = 120) -> Dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        capture_output=True,
        timeout=timeout_sec,
        check=False,
        env=os.environ.copy(),
    )
    return {
        "cmd": cmd,
        "cwd": str(cwd),
        "exit_code": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def parse_lean_diagnostics(text: str) -> List[Dict[str, Any]]:
    import re

    out: List[Dict[str, Any]] = []
    # path:line:col: severity: message
    pat = re.compile(r"^(.*\.lean):(\d+):(\d+):\s*(error|warning|info):\s*(.*)$")
    for line in text.splitlines():
        m = pat.match(line.strip())
        if not m:
            continue
        out.append(
            {
                "file": m.group(1),
                "line": int(m.group(2)),
                "col": int(m.group(3)),
                "severity": m.group(4),
                "message": m.group(5),
            }
        )
    return out


def json_text(obj: Any) -> str:
    return json.dumps(obj, ensure_ascii=False, indent=2)
