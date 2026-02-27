#!/usr/bin/env python3
"""Autonomous Lean 4 sorry-elimination loop for StatLean project.

Finds sorrys in Lean files, asks Claude to prove them, tests compilation,
commits progress, and loops until all sorrys are eliminated.
"""

import subprocess
import sys
import time
import re
import json
import os
import shutil
from pathlib import Path
from datetime import datetime

PROJ_DIR = Path("/home/gavin/statlean")
STATLEAN_DIR = PROJ_DIR / "Statlean"
LOG_FILE = PROJ_DIR / "scripts" / "auto_prove_log.jsonl"
STATE_FILE = PROJ_DIR / "scripts" / "auto_prove_state.json"

MAX_ATTEMPTS_PER_SORRY = 4
MAX_TOTAL_ITERS = 60
CLAUDE_TIMEOUT = 180  # seconds
BUILD_TIMEOUT = 300   # seconds

# Sorrys known to be fundamentally blocked (need missing Mathlib infrastructure).
# We still attempt them, but record and skip after MAX_ATTEMPTS.
# Sorrys known to be fundamentally blocked (need missing Mathlib infrastructure).
# Updated for v10 architecture (mathematical-object organization).
HARD_SORRYS_CONTEXT = [
    "efron_stein_condVar_le_of_condExp",        # Variance/EfronStein.lean
    "hg_bound",                                  # Variance/EfronStein.lean
    "gaussian_poincare_1d_core",                 # Gaussian/Poincare.lean
    "gaussian_poincare_coord_bound_core",        # Gaussian/Poincare.lean
    "hasSubgaussianMGF_centered_of_lipschitz",   # SubGaussian/Herbst.lean
    "gaussian_lsi_1d_core",                      # Entropy/LogSobolev.lean
    "tensorization_lsi_core",                    # Entropy/LogSobolev.lean
]


def log(entry: dict):
    entry["ts"] = datetime.now().isoformat()
    with open(LOG_FILE, "a") as f:
        f.write(json.dumps(entry) + "\n")
    print(f"[{entry['ts'][:19]}] {entry.get('msg', entry)}", flush=True)


def run(cmd, cwd=None, timeout=60, input_text=None):
    result = subprocess.run(
        cmd,
        cwd=cwd or PROJ_DIR,
        capture_output=True,
        text=True,
        timeout=timeout,
        input=input_text,
    )
    return result.returncode, result.stdout, result.stderr


def find_sorrys():
    """Return list of (file_path, line_num, sorry_line_content)."""
    sorrys = []
    for lean_file in sorted(STATLEAN_DIR.rglob("*.lean")):
        if "AutoPromoted" in str(lean_file) or "AutoStable" in str(lean_file):
            continue
        lines = lean_file.read_text().splitlines()
        for i, line in enumerate(lines, 1):
            stripped = line.strip()
            if stripped == "sorry" or stripped.endswith(":= by\n  sorry") or (
                stripped == "sorry" and True
            ):
                # Check it's an actual proof sorry, not in a comment
                if not line.strip().startswith("--") and not line.strip().startswith("/-"):
                    sorrys.append((str(lean_file), i, line))
    return sorrys


def get_context(file_path: str, line_num: int, before=80, after=30) -> str:
    lines = Path(file_path).read_text().splitlines()
    start = max(0, line_num - before - 1)
    end = min(len(lines), line_num + after)
    numbered = [f"{i+1:4d} | {l}" for i, l in enumerate(lines[start:end], start)]
    return "\n".join(numbered)


def get_theorem_context(file_path: str, line_num: int) -> str:
    """Get the theorem/lemma/def that contains the sorry."""
    lines = Path(file_path).read_text().splitlines()
    sorry_idx = line_num - 1

    # Walk backward to find theorem start
    theorem_start = sorry_idx
    for i in range(sorry_idx, max(0, sorry_idx - 200), -1):
        l = lines[i].strip()
        if l.startswith(("theorem ", "lemma ", "private theorem ", "private lemma ",
                         "def ", "noncomputable def ")):
            theorem_start = i
            break

    # Walk forward to find theorem end (simplified: go 30 lines past sorry)
    theorem_end = min(len(lines), sorry_idx + 30)

    return "\n".join(lines[theorem_start:theorem_end])


def build_file(file_rel: str) -> tuple[bool, str]:
    """Build a specific lean module."""
    # Convert path like Statlean/Concentration/EfronStein.lean -> Statlean.Concentration.EfronStein
    module = file_rel.replace("/", ".").replace(".lean", "")
    rc, out, err = run(["lake", "build", module], timeout=BUILD_TIMEOUT)
    output = out + err
    success = rc == 0 and "error:" not in output
    return success, output


def build_all() -> tuple[bool, str]:
    rc, out, err = run(["lake", "build"], timeout=BUILD_TIMEOUT)
    output = out + err
    success = rc == 0 and "error:" not in output
    return success, output


def extract_lean_code(response: str) -> str | None:
    """Extract lean code from Claude's response."""
    # Look for ```lean ... ``` block
    patterns = [
        r"```lean\n(.*?)```",
        r"```\n(.*?)```",
    ]
    for pattern in patterns:
        m = re.search(pattern, response, re.DOTALL)
        if m:
            return m.group(1).strip()
    # If no code block, check if the whole response looks like tactics
    lines = response.strip().splitlines()
    if lines and any(
        l.strip().startswith(("exact ", "simp", "rfl", "linarith", "norm_num",
                               "apply ", "have ", "intro", "constructor", "use "))
        for l in lines
    ):
        return response.strip()
    return None


def make_proof_prompt(file_path: str, line_num: int) -> str:
    file_rel = os.path.relpath(file_path, PROJ_DIR)
    context = get_context(file_path, line_num, before=100, after=20)
    thm_ctx = get_theorem_context(file_path, line_num)

    # Read imports section
    lines = Path(file_path).read_text().splitlines()
    imports = "\n".join(l for l in lines[:20] if l.startswith("import"))

    return f"""You are a Lean 4 / Mathlib expert. Lean version: 4.28.0-rc1, Mathlib v4.28.0-rc1.

File: {file_rel}
Line {line_num} has a `sorry` that must be replaced with a valid proof.

Imports:
{imports}

Theorem context (the theorem containing the sorry):
```lean
{thm_ctx}
```

Surrounding file context (line numbers shown):
```
{context}
```

API search strategy (use in order):
1. Read theme/mathlib_api_index.md — pre-built index of ~650 Mathlib APIs by topic
2. Use #check / exact? for precise lookup if needed
3. Search Statlean/ (Gaussian/, Variance/, Entropy/, SubGaussian/, CharFun/, SPD/) for project API

TASK: Replace the `sorry` on line {line_num} with a correct Lean 4 proof.

Requirements:
1. Output ONLY the replacement tactic(s) inside a ```lean code block
2. The replacement must be valid Lean 4 / Mathlib tactics
3. If the sorry genuinely requires Mathlib infrastructure that doesn't exist yet
   (e.g., product-measure Fubini for condExp), output a detailed `sorry` with a comment
   explaining exactly what Mathlib lemma is needed
4. Do NOT output the full theorem - just the replacement for the `sorry` line

Output format:
```lean
<replacement tactics here>
```
"""


def apply_proof(file_path: str, line_num: int, proof: str) -> str:
    """Replace the sorry at line_num with the proof. Returns original content."""
    path = Path(file_path)
    content = path.read_text()
    lines = content.splitlines(keepends=True)

    # Find the sorry line
    sorry_line = lines[line_num - 1]
    sorry_indent = len(sorry_line) - len(sorry_line.lstrip())
    indent = " " * sorry_indent

    # Format proof with proper indentation
    proof_lines = proof.splitlines()
    indented_proof = "\n".join(
        (indent + l if l.strip() else l) for l in proof_lines
    )

    # Replace
    lines[line_num - 1] = indented_proof + "\n"
    path.write_text("".join(lines))
    return content


def revert_file(file_path: str, original: str):
    Path(file_path).write_text(original)


def load_state() -> dict:
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text())
    return {"attempted": {}, "solved": [], "failed": []}


def save_state(state: dict):
    STATE_FILE.write_text(json.dumps(state, indent=2))


def commit_progress(message: str):
    run(["git", "add", "-A"], timeout=30)
    run(["git", "commit", "-m", message + "\n\nCo-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>"],
        timeout=30)
    run(["git", "push"], timeout=60)


def call_claude(prompt: str) -> str:
    """Call claude -p with the given prompt."""
    rc, out, err = run(
        ["claude", "-p", "--dangerously-skip-permissions"],
        input_text=prompt,
        timeout=CLAUDE_TIMEOUT,
    )
    if rc != 0:
        log({"msg": f"Claude returned rc={rc}", "stderr": err[:500]})
    return out


def main():
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    log({"msg": "Starting autonomous proof loop", "max_iters": MAX_TOTAL_ITERS})

    state = load_state()

    for iteration in range(MAX_TOTAL_ITERS):
        sorrys = find_sorrys()
        if not sorrys:
            log({"msg": "ALL SORRYS ELIMINATED! Project fully proved.", "iteration": iteration})
            commit_progress("🎉 All sorrys eliminated - full formalization complete")
            break

        log({"msg": f"Iteration {iteration}: found {len(sorrys)} sorrys",
             "sorrys": [(f, l) for f, l, _ in sorrys]})

        made_progress = False

        for file_path, line_num, line_content in sorrys:
            key = f"{file_path}:{line_num}"
            attempts = state["attempted"].get(key, 0)

            if attempts >= MAX_ATTEMPTS_PER_SORRY:
                log({"msg": f"Skipping {key} (max attempts reached)", "attempts": attempts})
                continue

            log({"msg": f"Attempting sorry at {key}", "attempt": attempts + 1})

            # Build prompt
            prompt = make_proof_prompt(file_path, line_num)

            # Call Claude
            response = call_claude(prompt)
            log({"msg": f"Got Claude response for {key}", "length": len(response)})

            # Extract code
            proof = extract_lean_code(response)
            if proof is None:
                log({"msg": f"No code extracted from response for {key}"})
                state["attempted"][key] = attempts + 1
                save_state(state)
                continue

            # Check if Claude returned another sorry (with or without comment)
            if proof.strip() == "sorry" or proof.strip().startswith("sorry --"):
                log({"msg": f"Claude returned sorry for {key} - improving comment"})
                # Still apply the improved comment if it has more info
                # Skip if no improvement
                state["attempted"][key] = attempts + 1
                save_state(state)
                continue

            # Apply the proof
            original_content = apply_proof(file_path, line_num, proof)

            # Test compilation
            file_rel = os.path.relpath(file_path, PROJ_DIR)
            success, build_output = build_file(file_rel)

            if success:
                log({"msg": f"SUCCESS: Proved sorry at {key}", "proof": proof[:200]})
                state["solved"].append({"key": key, "iteration": iteration, "proof": proof[:500]})
                made_progress = True

                # Check how many sorrys remain
                remaining = find_sorrys()
                commit_progress(
                    f"Prove sorry in {os.path.relpath(file_path, PROJ_DIR)} line {line_num}\n\n"
                    f"Remaining sorrys: {len(remaining)}"
                )
                break  # restart the sorry scan after each success
            else:
                # Revert
                revert_file(file_path, original_content)
                errors = [l for l in build_output.splitlines() if "error:" in l][:5]
                log({"msg": f"FAILED: proof for {key}", "errors": errors})
                state["attempted"][key] = attempts + 1

            save_state(state)

        if not made_progress:
            # No progress this iteration - try harder or give up
            all_attempted = all(
                state["attempted"].get(f"{fp}:{ln}", 0) >= MAX_ATTEMPTS_PER_SORRY
                for fp, ln, _ in sorrys
            )
            if all_attempted:
                log({"msg": "All remaining sorrys exhausted max attempts. Stopping.",
                     "remaining_sorrys": len(sorrys)})
                break
            # Otherwise just continue to next iteration

        time.sleep(5)

    # Final summary
    sorrys = find_sorrys()
    log({
        "msg": "Proof loop complete",
        "solved": len(state.get("solved", [])),
        "remaining_sorrys": len(sorrys),
        "remaining": [(f, l) for f, l, _ in sorrys],
    })

    if state.get("solved"):
        print(f"\n=== SOLVED {len(state['solved'])} sorrys ===")
        for s in state["solved"]:
            print(f"  {s['key']}")

    print(f"\n=== REMAINING: {len(sorrys)} sorrys ===")
    for fp, ln, _ in sorrys:
        print(f"  {os.path.relpath(fp, PROJ_DIR)}:{ln}")


if __name__ == "__main__":
    main()
