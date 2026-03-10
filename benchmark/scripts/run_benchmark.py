#!/usr/bin/env python3
"""CLI entry point for running StatLean benchmark experiments.

Usage:
    # Run a single model on all problems
    python run_benchmark.py --models claude-sonnet-4.6

    # Run specific problems with skill condition only
    python run_benchmark.py --models claude-sonnet-4.6 --problems rao_blackwell_mse scheffe \
        --conditions skill --max-rounds 4

    # Dry run (skip compilation)
    python run_benchmark.py --models claude-sonnet-4.6 --dry-run

    # Full 2x2 matrix for one model
    python run_benchmark.py --models claude-sonnet-4.6 --full-matrix

    # Multiple models with 3 repeats
    python run_benchmark.py --models claude-sonnet-4.6 gpt-5.2 --repeats 3

    # Multiple models
    python run_benchmark.py --models claude-sonnet-4.6 gpt-5.2 deepseek-v3.2-chat
"""

import argparse
import logging
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from harness.runner import run_experiment_matrix
from harness.metrics import MetricsRecorder, compute_aggregate_stats


def main():
    parser = argparse.ArgumentParser(
        description="StatLean Benchmark — LLM formalization proof evaluation"
    )
    parser.add_argument(
        "--models", nargs="+", required=True,
        help="Model names from config/models.yaml"
    )
    parser.add_argument(
        "--problems", nargs="*", default=None,
        help="Problem IDs to run (default: all)"
    )
    parser.add_argument(
        "--conditions", nargs="+", default=None,
        choices=["bare", "skill"],
        help="Conditions to test (default: both)"
    )
    parser.add_argument(
        "--max-rounds", type=int, default=None,
        help="Override max rounds (default: run both single=1 and multi=4)"
    )
    parser.add_argument(
        "--full-matrix", action="store_true",
        help="Run full 2x2 matrix (bare/skill x single/multi)"
    )
    parser.add_argument(
        "--repeats", type=int, default=1,
        help="Number of times to repeat each experiment (default: 1)"
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Skip compilation (useful for testing prompt generation)"
    )
    parser.add_argument(
        "--output-dir", type=str, default=None,
        help="Output directory for results"
    )
    parser.add_argument(
        "--problems-yaml", type=str, default=None,
        help="Path to problems.yaml"
    )
    parser.add_argument(
        "--verbose", "-v", action="store_true",
        help="Enable debug logging"
    )

    args = parser.parse_args()

    # Setup logging
    level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(
        level=level,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    # Determine round configurations
    if args.max_rounds is not None:
        max_rounds_map = {"custom": args.max_rounds}
    elif args.full_matrix:
        max_rounds_map = {"single": 1, "multi": 4}
    else:
        max_rounds_map = {"multi": 4}

    # Determine conditions
    conditions = args.conditions
    if conditions is None:
        conditions = ["bare", "skill"] if args.full_matrix else ["skill"]

    # Run experiments
    logging.info("=" * 60)
    logging.info("StatLean Benchmark")
    logging.info(f"Models: {args.models}")
    logging.info(f"Conditions: {conditions}")
    logging.info(f"Round configs: {max_rounds_map}")
    logging.info(f"Repeats: {args.repeats}")
    logging.info(f"Dry run: {args.dry_run}")
    logging.info("=" * 60)

    results = run_experiment_matrix(
        model_names=args.models,
        problem_ids=args.problems,
        conditions=conditions,
        max_rounds_map=max_rounds_map,
        output_dir=args.output_dir,
        skip_compile=args.dry_run,
        problems_path=Path(args.problems_yaml) if args.problems_yaml else None,
        repeats=args.repeats,
    )

    # Print summary
    if results:
        stats = compute_aggregate_stats(results)
        print("\n" + "=" * 60)
        print("SUMMARY")
        print("=" * 60)

        for model_id, model_stats in stats["models"].items():
            print(f"\n{model_id}:")
            print(f"  Completion rate: {model_stats['completion_rate']:.1%}")
            print(f"  Adjusted completion (excl. infra errors): "
                  f"{model_stats['adjusted_completion_rate']:.1%}")
            if model_stats["avg_cost_all_runs"] is not None:
                print(f"  Avg cost (all runs): ${model_stats['avg_cost_all_runs']:.4f}")
            if model_stats["avg_cost_solved_only"] is not None:
                print(f"  Avg cost (solved only): ${model_stats['avg_cost_solved_only']:.4f}")
            if model_stats["expected_cost_per_success"] is not None:
                print(f"  Expected cost per success: ${model_stats['expected_cost_per_success']:.4f}")
            if model_stats["median_rounds"] is not None:
                print(f"  Median rounds: {model_stats['median_rounds']}")
            print(f"  First-pass rate: {model_stats['first_pass_rate']:.1%}")

            # Failure breakdown
            fb = model_stats.get("failure_breakdown", {})
            if fb:
                failures = {k: v for k, v in fb.items() if k != "success"}
                if failures:
                    print(f"  Failures: {dict(failures)}")

        if stats.get("skill_ablation"):
            print("\nSkill Ablation:")
            for model_id, ablation in stats["skill_ablation"].items():
                print(f"\n  {model_id}:")
                if ablation.get("cost_reduction") is not None:
                    print(f"    Cost reduction: {ablation['cost_reduction']:.1%}")
                print(f"    Bare completion: {ablation['bare_completion_rate']:.1%}")
                print(f"    Skill completion: {ablation['skill_completion_rate']:.1%}")

    else:
        print("\nNo results generated.")

    return 0 if results else 1


if __name__ == "__main__":
    sys.exit(main())
