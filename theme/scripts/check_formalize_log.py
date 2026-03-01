#!/usr/bin/env python3
"""Verify that an agent followed the formalize_playbook.md steps.

Usage:
    python3 theme/scripts/check_formalize_log.py [logfile]
    # default logfile: theme/out/formalize_checkpoint.jsonl

Exit code 0 = all steps present and passed.
Exit code 1 = missing or failed steps.
"""

import json
import sys
from pathlib import Path

REQUIRED_STEPS = {
    0: "输入解析",
    1: "获取数学内容",
    2: "检查已有代码",
    3: "设计 Lean 签名",
    4: "写证明",
    5: "编译验证",
    6: "诚实性检查",
    7: "收尾",
}

# Step 6 required fields for honesty check
HONESTY_FIELDS = ["honesty_check", "trivial_wrappers", "hidden_sorry"]


def main():
    logfile = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("theme/out/formalize_checkpoint.jsonl")

    if not logfile.exists():
        print(f"FAIL: log file not found: {logfile}")
        print("  Agent did not write any checkpoint — likely did not follow the playbook.")
        sys.exit(1)

    entries = []
    for i, line in enumerate(logfile.read_text().strip().splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        try:
            entries.append(json.loads(line))
        except json.JSONDecodeError as e:
            print(f"WARN: line {i} is not valid JSON: {e}")

    if not entries:
        print(f"FAIL: log file is empty: {logfile}")
        sys.exit(1)

    steps_found = {}
    for e in entries:
        step = e.get("step")
        if step is not None:
            steps_found[step] = e

    # Check completeness
    missing = []
    failed = []
    warnings = []

    for step_num, step_name in REQUIRED_STEPS.items():
        if step_num not in steps_found:
            missing.append((step_num, step_name))
        else:
            entry = steps_found[step_num]
            status = entry.get("status", "unknown")
            if status != "done":
                failed.append((step_num, step_name, status))

    # Special checks
    if 2 in steps_found:
        existing = steps_found[2].get("existing", "")
        if existing == "":
            warnings.append("Step 2: 'existing' field is empty — did the agent actually grep?")

    if 3 in steps_found:
        decls = steps_found[3].get("declarations", [])
        if not decls:
            warnings.append("Step 3: no declarations listed — what did the agent design?")

    if 5 in steps_found:
        build = steps_found[5].get("build", "")
        if build != "pass":
            failed.append((5, "编译验证", f"build={build}"))

    if 6 in steps_found:
        e6 = steps_found[6]
        for f in HONESTY_FIELDS:
            if f not in e6:
                warnings.append(f"Step 6: missing '{f}' field — honesty check incomplete")
        if e6.get("trivial_wrappers", 0) > 0:
            failed.append((6, "诚实性检查", f"trivial_wrappers={e6['trivial_wrappers']}"))
        if e6.get("hidden_sorry", 0) > 0:
            failed.append((6, "诚实性检查", f"hidden_sorry={e6['hidden_sorry']}"))

    # Report
    print("=" * 60)
    print("Formalize Playbook Compliance Report")
    print("=" * 60)

    total = len(REQUIRED_STEPS)
    done = sum(1 for s in REQUIRED_STEPS if s in steps_found and steps_found[s].get("status") == "done")

    print(f"\nSteps completed: {done}/{total}")

    if 3 in steps_found:
        decls = steps_found[3].get("declarations", [])
        print(f"Declarations: {', '.join(decls) if decls else '(none)'}")
        print(f"Target file: {steps_found[3].get('file', '(not specified)')}")

    if 4 in steps_found:
        print(f"Sorry count: {steps_found[4].get('sorry_count', '?')}")

    if 5 in steps_found:
        print(f"Build: {steps_found[5].get('build', '?')} (errors={steps_found[5].get('errors', '?')}, warnings={steps_found[5].get('warnings', '?')})")

    if missing:
        print(f"\nMISSING steps ({len(missing)}):")
        for num, name in missing:
            print(f"  Step {num}: {name}")

    if failed:
        print(f"\nFAILED steps ({len(failed)}):")
        for item in failed:
            if len(item) == 3:
                num, name, reason = item
                print(f"  Step {num}: {name} — {reason}")

    if warnings:
        print(f"\nWARNINGS ({len(warnings)}):")
        for w in warnings:
            print(f"  {w}")

    if not missing and not failed:
        print("\nRESULT: PASS ✓")
        print("Agent followed all 8 steps of the formalize playbook.")
        sys.exit(0)
    else:
        print(f"\nRESULT: FAIL ✗")
        if missing:
            print(f"  {len(missing)} steps skipped — agent did not follow the full playbook.")
        if failed:
            print(f"  {len(failed)} steps failed — see details above.")
        sys.exit(1)


if __name__ == "__main__":
    main()
