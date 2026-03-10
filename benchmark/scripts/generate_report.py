#!/usr/bin/env python3
"""Generate comparison reports from benchmark results.

Usage:
    python generate_report.py                          # all results
    python generate_report.py --run-id 20260303-001    # specific run
    python generate_report.py --format csv             # CSV output
"""

import argparse
import csv
import io
import sys
from collections import defaultdict
from pathlib import Path

import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from harness.metrics import (
    MetricsRecorder,
    RunResult,
    compute_aggregate_stats,
    compute_repeat_stats,
)

CONFIG_DIR = Path(__file__).resolve().parent.parent / "config"


def _load_difficulty_map(results: list | None = None) -> dict[str, str]:
    """Load problem_id → difficulty from problems.yaml.

    If results are provided and contain a problems_config_path, use that path
    instead of the default to ensure consistency with the actual run config.
    """
    path = CONFIG_DIR / "problems.yaml"

    # Try to use the actual config path from run metadata
    if results:
        for r in results:
            p = getattr(r, "problems_config_path", "") or ""
            if p and Path(p).exists():
                path = Path(p)
                break

    if not path.exists():
        return {}
    with open(path) as f:
        data = yaml.safe_load(f)
    return {p["problem_id"]: p.get("difficulty", "unknown") for p in data.get("problems", [])}


def _fmt_cost(val) -> str:
    """Format cost value, handling None and 0.0 correctly."""
    if val is None:
        return "N/A"
    return f"${val:.4f}"


def _fmt_float(val, fmt=".1f", suffix="") -> str:
    if val is None:
        return "N/A"
    return f"{val:{fmt}}{suffix}"


def _fmt_pct(val) -> str:
    if val is None:
        return "N/A"
    return f"{val:.0%}"


def generate_markdown_report(
    results: list[RunResult], difficulty_map: dict[str, str] | None = None
) -> str:
    """Generate a full markdown comparison report."""
    stats = compute_aggregate_stats(results)
    if difficulty_map is None:
        difficulty_map = _load_difficulty_map(results)
    lines = []

    lines.append("# StatLean Benchmark Report\n")
    lines.append(f"**Total experiments**: {len(results)}")
    solved = sum(1 for r in results if r.solved)
    lines.append(f"**Solved**: {solved}/{len(results)} ({solved/len(results):.1%})\n")

    # --- Model Comparison Table (with three cost metrics) ---
    lines.append("## Model Comparison\n")
    lines.append(
        "| Model | Completion | Adj. Completion | Avg Cost (all) | "
        "Avg Cost (solved) | Exp. Cost/Success | Median Rounds | First-Pass |"
    )
    lines.append(
        "|-------|-----------|-----------------|----------------|"
        "-------------------|-------------------|---------------|------------|"
    )

    model_rows = []
    for model_id, ms in stats["models"].items():
        sort_key = ms["expected_cost_per_success"] if ms["expected_cost_per_success"] is not None else float("inf")
        row = (
            f"| {model_id} "
            f"| {_fmt_pct(ms['completion_rate'])} "
            f"| {_fmt_pct(ms['adjusted_completion_rate'])} "
            f"| {_fmt_cost(ms['avg_cost_all_runs'])} "
            f"| {_fmt_cost(ms['avg_cost_solved_only'])} "
            f"| {_fmt_cost(ms['expected_cost_per_success'])} "
            f"| {_fmt_float(ms['median_rounds'], '.0f')} "
            f"| {_fmt_pct(ms['first_pass_rate'])} |"
        )
        model_rows.append((sort_key, row))

    for _, row in sorted(model_rows):
        lines.append(row)
    lines.append("")

    # --- Model Comparison by Round Budget ---
    models_by_rounds = stats.get("models_by_rounds", {})
    if models_by_rounds:
        lines.append("## Model Comparison by Round Budget\n")
        lines.append(
            "| Model | MaxR | Completion | Adj. Compl. | Avg Cost (all) | "
            "Exp. Cost/Success | First-Pass |"
        )
        lines.append(
            "|-------|------|-----------|-------------|----------------|"
            "-------------------|------------|"
        )
        mbr_rows = []
        for (model_id, max_rounds), ms in models_by_rounds.items():
            sort_key = (model_id, max_rounds)
            row = (
                f"| {model_id} "
                f"| {max_rounds} "
                f"| {_fmt_pct(ms['completion_rate'])} "
                f"| {_fmt_pct(ms['adjusted_completion_rate'])} "
                f"| {_fmt_cost(ms['avg_cost_all_runs'])} "
                f"| {_fmt_cost(ms['expected_cost_per_success'])} "
                f"| {_fmt_pct(ms['first_pass_rate'])} |"
            )
            mbr_rows.append((sort_key, row))
        for _, row in sorted(mbr_rows):
            lines.append(row)
        lines.append("")

    # --- Failure Breakdown ---
    lines.append("## Failure Breakdown\n")
    lines.append("| Model | Success | Compile Error | Sorry Left | Parser Error | Infra Error | Timeout |")
    lines.append("|-------|---------|---------------|------------|--------------|-------------|---------|")
    for model_id, ms in stats["models"].items():
        fb = ms.get("failure_breakdown", {})
        lines.append(
            f"| {model_id} "
            f"| {fb.get('success', 0)} "
            f"| {fb.get('compile_error', 0)} "
            f"| {fb.get('sorry_remaining', 0)} "
            f"| {fb.get('parser_error', 0)} "
            f"| {fb.get('infra_error', 0)} "
            f"| {fb.get('timeout', 0)} |"
        )
    lines.append("")

    # --- Per-Problem Results ---
    lines.append("## Per-Problem Results\n")

    by_problem = defaultdict(list)
    for r in results:
        by_problem[r.problem_id].append(r)

    for problem_id, prob_results in sorted(by_problem.items()):
        diff = difficulty_map.get(problem_id, "?")
        lines.append(f"### {problem_id} [{diff}]\n")
        lines.append("| Model | Condition | Rounds | Cost | Solved | Error |")
        lines.append("|-------|-----------|--------|------|--------|-------|")
        for r in sorted(prob_results, key=lambda x: (x.model_id, x.condition)):
            error = ""
            if not r.solved and r.rounds:
                last_err = r.rounds[-1].error_snippet or ""
                error = last_err[:60].replace("|", "\\|")
            lines.append(
                f"| {r.model_id} | {r.condition} | {r.total_rounds} | "
                f"${r.total_cost_usd:.4f} | {'Y' if r.solved else 'N'} | {error} |"
            )
        lines.append("")

    # --- Skill Ablation ---
    if stats.get("skill_ablation"):
        lines.append("## Skill Ablation\n")
        lines.append(
            "| Model | Bare Exp. Cost | Skill Exp. Cost | Cost Reduction | "
            "Bare Completion | Skill Completion |"
        )
        lines.append(
            "|-------|----------------|-----------------|----------------|"
            "-----------------|------------------|"
        )
        for model_id, abl in stats["skill_ablation"].items():
            lines.append(
                f"| {model_id} "
                f"| {_fmt_cost(abl['bare_expected_cost'])} "
                f"| {_fmt_cost(abl['skill_expected_cost'])} "
                f"| {_fmt_pct(abl.get('cost_reduction'))} "
                f"| {_fmt_pct(abl['bare_completion_rate'])} "
                f"| {_fmt_pct(abl['skill_completion_rate'])} |"
            )
        lines.append("")

    # --- Cost by Difficulty (real data, not placeholder) ---
    if difficulty_map:
        lines.append("## Cost by Difficulty\n")
        difficulties = ["easy", "medium", "hard", "open"]
        model_ids = sorted(stats["models"].keys())

        # Group results by (model, difficulty)
        by_md = defaultdict(list)
        for r in results:
            diff = difficulty_map.get(r.problem_id, "unknown")
            by_md[(r.model_id, diff)].append(r)

        lines.append(
            "| Model | "
            + " | ".join(f"{d.capitalize()} (solved/n, avg$/prob)" for d in difficulties)
            + " |"
        )
        lines.append("|-------|" + "|".join("-" * 28 for _ in difficulties) + "|")

        for model_id in model_ids:
            cols = []
            for diff in difficulties:
                runs = by_md.get((model_id, diff), [])
                if not runs:
                    cols.append("-")
                else:
                    n = len(runs)
                    s = sum(1 for r in runs if r.solved)
                    avg_cost = sum(r.total_cost_usd for r in runs) / n
                    cols.append(f"{s}/{n}, ${avg_cost:.4f}")
            lines.append(f"| {model_id} | " + " | ".join(cols) + " |")
        lines.append("")

    # --- Repeat Statistics (if repeats present) ---
    repeat_ids = set(r.repeat_id for r in results)
    if len(repeat_ids) > 1:
        lines.append("## Repeat Statistics\n")
        repeat_stats = compute_repeat_stats(results)
        lines.append(
            "| Model | Problem | Condition | MaxR | N | "
            "Mean Cost +/- CI95 | Completion [CI95] |"
        )
        lines.append(
            "|-------|---------|-----------|------|---|"
            "--------------------|-------------------|"
        )
        for (model_id, problem_id, condition, max_rounds), rs in sorted(repeat_stats.items()):
            cost_str = f"${rs['mean_cost']:.4f} +/- ${rs['ci95_cost']:.4f}"
            rate_str = (
                f"{rs['completion_rate']:.0%} "
                f"[{rs['ci95_rate_lower']:.0%}-{rs['ci95_rate_upper']:.0%}]"
            )
            lines.append(
                f"| {model_id} | {problem_id} | {condition} | {max_rounds} | {rs['n_repeats']} | "
                f"{cost_str} | {rate_str} |"
            )
        lines.append("")

    return "\n".join(lines)


def generate_csv_report(results: list[RunResult]) -> str:
    """Generate CSV report for further analysis."""
    difficulty_map = _load_difficulty_map(results)
    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow([
        "run_id", "problem_id", "difficulty", "model_id", "condition",
        "repeat_id", "max_rounds", "total_rounds", "total_cost_usd",
        "total_time_s", "total_input_tokens", "total_output_tokens",
        "solved", "first_round_success", "last_failure_type",
    ])

    for r in results:
        first_pass = r.rounds[0].compile_success if r.rounds else False
        last_ft = r.rounds[-1].failure_type if r.rounds else ""
        diff = difficulty_map.get(r.problem_id, "unknown")
        writer.writerow([
            r.run_id, r.problem_id, diff, r.model_id, r.condition,
            r.repeat_id, r.max_rounds, r.total_rounds,
            f"{r.total_cost_usd:.6f}", f"{r.total_time_s:.2f}",
            r.total_input_tokens, r.total_output_tokens,
            r.solved, first_pass, last_ft,
        ])

    return output.getvalue()


def main():
    parser = argparse.ArgumentParser(description="Generate benchmark reports")
    parser.add_argument("--run-id", type=str, default=None, help="Specific run ID")
    parser.add_argument(
        "--format", choices=["markdown", "csv", "both"], default="markdown",
        help="Output format"
    )
    parser.add_argument(
        "--results-dir", type=str, default=None,
        help="Results directory (default: benchmark/results/raw)"
    )
    parser.add_argument(
        "--output", "-o", type=str, default=None,
        help="Output file (default: stdout)"
    )

    args = parser.parse_args()

    results_dir = args.results_dir or str(
        Path(__file__).resolve().parent.parent / "results" / "raw"
    )
    recorder = MetricsRecorder(results_dir)
    results = recorder.load_results(args.run_id)

    if not results:
        print("No results found.", file=sys.stderr)
        return 1

    outputs = []

    if args.format in ("markdown", "both"):
        md = generate_markdown_report(results)
        outputs.append(("md", md))

    if args.format in ("csv", "both"):
        csv_text = generate_csv_report(results)
        outputs.append(("csv", csv_text))

    for ext, content in outputs:
        if args.output:
            out_path = args.output if len(outputs) == 1 else f"{args.output}.{ext}"
            Path(out_path).write_text(content)
            print(f"Report written to {out_path}", file=sys.stderr)
        else:
            print(content)

    return 0


if __name__ == "__main__":
    sys.exit(main())
