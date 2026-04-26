#!/usr/bin/env python3
"""validate_decomposition.py — size-monotone check for sub-lemma decomposition.

Per Rule 3 / U4-B in `website/docs/CLI_WEB_CONFORMANCE.md` §0.3:
A *healthy* decomposition strictly reduces complexity at each step.
Pathological decomposition pushes the same difficulty around without
shrinking it ("pushing the pea").

Invariants enforced (any one fails → REJECT):
  · max(child.estimated_lines) < parent.estimated_lines * RATIO  (default 0.8)
  · all(child.goal_pp_lines < parent.goal_pp_lines)              (when both > 0)
  · all(child.deps_count <= parent.deps_count)                   (when parent > 0)

Exit 0 = decomposition healthy, allowed.
Exit 1 = decomposition rejected; stderr lists which invariants failed.
Exit 2 = bad input.

Per CLAUDE.md Rule 9 Q3 (determinism gate): the size-monotone rule is a
deterministic mathematical check — no LLM judgment needed once parent +
children metrics are reported. Replaces the original (rejected) "depth
≥ 3 cap" idea, which would have wrongly blocked legitimate Bourbaki-
style proofs that go 5-6 deep with each level genuinely smaller.
"""
from __future__ import annotations

import argparse
import json
import sys

LINES_RATIO = 0.8


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Reject pathological sub-lemma decompositions"
    )
    ap.add_argument(
        "--parent-metrics",
        required=True,
        help='JSON: {"goal_pp_lines": N, "estimated_lines": N, "deps_count": N}',
    )
    ap.add_argument(
        "--children-metrics",
        required=True,
        help="JSON array of objects with same keys as --parent-metrics",
    )
    ap.add_argument(
        "--lines-ratio",
        type=float,
        default=LINES_RATIO,
        help=f"Max child / parent estimated_lines ratio (default {LINES_RATIO})",
    )
    args = ap.parse_args()

    try:
        parent = json.loads(args.parent_metrics)
        children = json.loads(args.children_metrics)
    except json.JSONDecodeError as e:
        print(f"[validate_decomposition] bad JSON: {e}", file=sys.stderr)
        sys.exit(2)

    if not isinstance(parent, dict):
        print("[validate_decomposition] --parent-metrics must be a JSON object",
              file=sys.stderr)
        sys.exit(2)
    if not isinstance(children, list) or not children:
        print("[validate_decomposition] --children-metrics must be a non-empty list",
              file=sys.stderr)
        sys.exit(2)

    p_est = float(parent.get("estimated_lines") or 0)
    p_pp = float(parent.get("goal_pp_lines") or 0)
    p_deps = float(parent.get("deps_count") or 0)

    failures: list[str] = []
    for i, c in enumerate(children):
        if not isinstance(c, dict):
            failures.append(f"child[{i}] is not an object")
            continue
        c_est = float(c.get("estimated_lines") or 0)
        c_pp = float(c.get("goal_pp_lines") or 0)
        c_deps = float(c.get("deps_count") or 0)

        if p_est > 0 and c_est >= p_est * args.lines_ratio:
            failures.append(
                f"child[{i}].estimated_lines={c_est:g} >= "
                f"parent.estimated_lines={p_est:g} × {args.lines_ratio} "
                f"= {p_est * args.lines_ratio:.0f} — not strictly smaller"
            )
        if p_pp > 0 and c_pp >= p_pp:
            failures.append(
                f"child[{i}].goal_pp_lines={c_pp:g} >= "
                f"parent.goal_pp_lines={p_pp:g} — not smaller"
            )
        if p_deps > 0 and c_deps > p_deps:
            failures.append(
                f"child[{i}].deps_count={c_deps:g} > "
                f"parent.deps_count={p_deps:g} — adding dependencies"
            )

    if failures:
        print(
            "[validate_decomposition] REJECTED — pushing the pea, not splitting:",
            file=sys.stderr,
        )
        for f in failures:
            print(f"  · {f}", file=sys.stderr)
        sys.exit(1)

    print(f"[validate_decomposition] OK — {len(children)} children all "
          f"strictly smaller than parent")


if __name__ == "__main__":
    main()
