"""Shared single-tactic attempt helper.

Mechanical extraction of `_try_tactic` from `verify_citation.py:102-178`
(E11 slice). Two callers as of M5:

  - `verify_citation.py` (E11) — citation-verify library path runs the
    4-tactic ladder via this helper.
  - `auto_tactic_pre_pass.py` (M5) — auto_tactic pre-pass runs the
    9-tactic ladder via this helper.

No behavior change vs the pre-extraction copy in verify_citation.py.
Layer 1 invariant (Rule 3): only the sorry body line is mutated; on
FAIL the file is reverted to its pre-call bytes (locked theorem
signature stays untouched on PASS by construction — substitution
matches `\\bsorry\\b` only on the targeted body line).

The single mutation/revert/lake-build cycle here is *the* per-attempt
unit. Both callers wrap it in a per-tactic loop (E11: 4 ladders;
M5: 9 ladders). Tests mock this helper directly.
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path
from typing import Optional, Tuple


def _try_tactic(
    file_path: Path,
    sorry_line: int,
    tactic: str,
    module_path: Optional[str] = None,
) -> Tuple[bool, str]:
    """Attempt one tactic: replace `:= sorry` (or `sorry`) on `sorry_line`
    with the tactic, run `lake build`, return (passed, output_excerpt).

    On FAIL: ALWAYS reverts the file mutation before returning. The
    source tree is byte-identical to its pre-call state on FAIL —
    matches the contract of czy's `replace_sorry` `[REPLACE-FAIL]`
    branch (`toolRunner.ts:1184`).

    On PASS: file is left with the tactic in place. State=DONE rows
    are not re-attacked, so the post-mutation source IS what
    `lake build` and downstream pipeline want.

    Tests mock this helper directly. Real-mode invokes
    `subprocess.run(['lake', 'build', module_path or ''])`.
    """
    if not file_path.is_file():
        return False, f"file not found: {file_path}"
    original_bytes = file_path.read_bytes()
    try:
        # Apply edit
        lines = original_bytes.decode("utf-8").splitlines(keepends=True)
        if sorry_line < 1 or sorry_line > len(lines):
            return False, f"sorry_line {sorry_line} out of range (1..{len(lines)})"
        # Replace the FIRST occurrence of `sorry` on the target line.
        # Prefer matching `:= by sorry` → `:= by <tactic>` so block-tactic
        # context is preserved; fall back to bare `sorry` → `by <tactic>`.
        target = lines[sorry_line - 1]
        if "sorry" not in target:
            return False, f"no `sorry` on line {sorry_line}"
        # Substitute first occurrence only
        new_target = re.sub(r"\bsorry\b", f"by {tactic}", target, count=1)
        # If the target already had `by`, the agent's tactic context
        # belongs inside the same `by` block; collapse the redundant
        # `by by`.
        new_target = new_target.replace("by by ", "by ")
        lines[sorry_line - 1] = new_target
        file_path.write_text("".join(lines), encoding="utf-8")

        # Run lake build
        cmd = ["lake", "build"]
        if module_path:
            cmd.append(module_path)
        proc = subprocess.run(
            cmd,
            cwd=str(file_path.parent.parent.resolve()
                    if file_path.parent.name == "Statlean"
                    else file_path.parent.resolve()),
            capture_output=True,
            text=True,
            timeout=60,
        )
        if proc.returncode == 0:
            return True, "lake build clean"
        # Revert on fail
        file_path.write_bytes(original_bytes)
        excerpt = (proc.stderr or proc.stdout or "")[-200:]
        return False, excerpt
    except subprocess.TimeoutExpired:
        # Defensive: revert if we can
        try:
            file_path.write_bytes(original_bytes)
        except OSError:
            pass
        return False, "lake build timed out (60s)"
    except Exception as e:
        try:
            file_path.write_bytes(original_bytes)
        except OSError:
            pass
        return False, f"exception: {e}"
