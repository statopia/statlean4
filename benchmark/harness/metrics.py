"""Metrics recording and computation for benchmark runs."""

from __future__ import annotations

import json
import math
import os
import uuid
from dataclasses import asdict, dataclass, field
from datetime import datetime
from pathlib import Path


# --- Failure taxonomy ---

class FailureType:
    """Categorize failures for fair model evaluation."""
    SUCCESS = "success"
    COMPILE_ERROR = "compile_error"    # model produced wrong Lean code
    SORRY_REMAINING = "sorry_remaining"  # model left sorry in proof
    PARSER_ERROR = "parser_error"      # harness failed to extract proof from response
    INFRA_ERROR = "infra_error"        # API timeout, rate limit, network error
    TIMEOUT = "timeout"                # compilation timed out


@dataclass
class RoundMetrics:
    """Metrics for a single generation-compile round."""
    round: int
    input_tokens: int
    output_tokens: int
    cost_usd: float
    latency_s: float
    compile_success: bool
    compile_time_s: float = 0.0
    error_snippet: str | None = None
    sorry_count: int = 0
    failure_type: str = "success"  # from FailureType
    sampling_params: dict = field(default_factory=dict)  # temperature, seed, etc.


@dataclass
class RunResult:
    """Complete result of one (model, problem, condition) experiment."""
    run_id: str
    problem_id: str
    model_id: str
    condition: str  # "bare" or "skill"
    max_rounds: int
    repeat_id: int = 0  # which repeat (0-indexed)
    rounds: list[RoundMetrics] = field(default_factory=list)
    solved: bool = False
    total_cost_usd: float = 0.0
    total_rounds: int = 0
    total_time_s: float = 0.0
    total_input_tokens: int = 0
    total_output_tokens: int = 0
    timestamp: str = ""
    notes: str = ""
    problems_config_path: str = ""  # path to problems.yaml used for this run

    def finalize(self):
        """Compute aggregate metrics from rounds."""
        self.total_rounds = len(self.rounds)
        self.total_cost_usd = sum(r.cost_usd for r in self.rounds)
        self.total_time_s = sum(r.latency_s + r.compile_time_s for r in self.rounds)
        self.total_input_tokens = sum(r.input_tokens for r in self.rounds)
        self.total_output_tokens = sum(r.output_tokens for r in self.rounds)
        self.solved = any(r.compile_success for r in self.rounds)
        if not self.timestamp:
            self.timestamp = datetime.now().isoformat()


class MetricsRecorder:
    """Records experiment results to JSONL files."""

    def __init__(self, output_dir: str | Path):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def record(self, result: RunResult):
        """Append a run result to the JSONL log file."""
        result.finalize()
        filename = f"run_{result.run_id}.jsonl"
        filepath = self.output_dir / filename

        record = asdict(result)
        with open(filepath, "a") as f:
            f.write(json.dumps(record, ensure_ascii=False) + "\n")

    def load_results(self, run_id: str | None = None) -> list[RunResult]:
        """Load results from JSONL files."""
        results = []
        pattern = f"run_{run_id}.jsonl" if run_id else "run_*.jsonl"

        for filepath in sorted(self.output_dir.glob(pattern)):
            with open(filepath) as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    data = json.loads(line)
                    rounds = [RoundMetrics(**r) for r in data.pop("rounds", [])]
                    result = RunResult(**data, rounds=rounds)
                    results.append(result)
        return results


def generate_run_id() -> str:
    """Generate a unique run ID: timestamp + uuid suffix to avoid collisions."""
    ts = datetime.now().strftime("%Y%m%d-%H%M%S")
    suffix = uuid.uuid4().hex[:8]
    return f"{ts}-{suffix}"


def compute_aggregate_stats(results: list[RunResult]) -> dict:
    """Compute aggregate statistics across multiple runs.

    Returns dict with:
    - per-(model, max_rounds) stats (three cost metrics, completion rate, rounds)
    - combined per-model stats (for overview, not ranking)
    - skill ablation
    - failure type breakdown
    """
    from collections import defaultdict

    by_model = defaultdict(list)
    by_model_rounds = defaultdict(list)
    by_model_condition = defaultdict(list)

    for r in results:
        by_model[r.model_id].append(r)
        by_model_rounds[(r.model_id, r.max_rounds)].append(r)
        by_model_condition[(r.model_id, r.condition)].append(r)

    stats = {"models": {}, "models_by_rounds": {}, "skill_ablation": {}}

    for model_id, runs in by_model.items():
        solved = [r for r in runs if r.solved]
        total_cost_all = sum(r.total_cost_usd for r in runs)
        total_cost_solved = sum(r.total_cost_usd for r in solved)

        # Failure type breakdown (only count model-attributable failures)
        failure_counts = defaultdict(int)
        for r in runs:
            if r.solved:
                failure_counts[FailureType.SUCCESS] += 1
            elif r.rounds:
                last_ft = r.rounds[-1].failure_type
                failure_counts[last_ft] += 1
            else:
                failure_counts[FailureType.INFRA_ERROR] += 1

        # Infra failures only: API errors, rate limits, timeouts
        # (parser_error = model returned nothing extractable → model's fault, not infra)
        infra_failures = (
            failure_counts.get(FailureType.INFRA_ERROR, 0)
            + failure_counts.get(FailureType.TIMEOUT, 0)
        )
        # Adjusted completion rate: exclude infra failures from denominator
        model_relevant = len(runs) - infra_failures
        adjusted_completion = (
            len(solved) / model_relevant if model_relevant > 0 else 0
        )

        stats["models"][model_id] = {
            "total_runs": len(runs),
            "completion_rate": len(solved) / len(runs) if runs else 0,
            "adjusted_completion_rate": adjusted_completion,
            # Three cost metrics (survivor bias correction)
            "avg_cost_all_runs": total_cost_all / len(runs) if runs else None,
            "avg_cost_solved_only": total_cost_solved / len(solved) if solved else None,
            "expected_cost_per_success": (
                total_cost_all / len(solved) if solved else None
            ),
            "median_rounds": _median([r.total_rounds for r in solved]) if solved else None,
            "avg_time_s": (
                sum(r.total_time_s for r in solved) / len(solved) if solved else None
            ),
            "first_pass_rate": (
                sum(1 for r in runs if r.rounds and r.rounds[0].compile_success) / len(runs)
                if runs else 0
            ),
            "failure_breakdown": dict(failure_counts),
        }

    # Per-(model, max_rounds) stats for fair comparison
    for (model_id, max_rounds), runs in by_model_rounds.items():
        solved = [r for r in runs if r.solved]
        total_cost_all = sum(r.total_cost_usd for r in runs)
        total_cost_solved = sum(r.total_cost_usd for r in solved)

        failure_counts = defaultdict(int)
        for r in runs:
            if r.solved:
                failure_counts[FailureType.SUCCESS] += 1
            elif r.rounds:
                failure_counts[r.rounds[-1].failure_type] += 1
            else:
                failure_counts[FailureType.INFRA_ERROR] += 1

        # Infra failures only: API errors, timeouts (NOT parser_error —
        # parser_error means model returned nothing extractable, model's fault)
        infra_failures = (
            failure_counts.get(FailureType.INFRA_ERROR, 0)
            + failure_counts.get(FailureType.TIMEOUT, 0)
        )
        model_relevant = len(runs) - infra_failures

        stats["models_by_rounds"][(model_id, max_rounds)] = {
            "total_runs": len(runs),
            "max_rounds": max_rounds,
            "completion_rate": len(solved) / len(runs) if runs else 0,
            "adjusted_completion_rate": (
                len(solved) / model_relevant if model_relevant > 0 else 0
            ),
            "avg_cost_all_runs": total_cost_all / len(runs) if runs else None,
            "avg_cost_solved_only": total_cost_solved / len(solved) if solved else None,
            "expected_cost_per_success": (
                total_cost_all / len(solved) if solved else None
            ),
            "median_rounds": _median([r.total_rounds for r in solved]) if solved else None,
            "first_pass_rate": (
                sum(1 for r in runs if r.rounds and r.rounds[0].compile_success) / len(runs)
                if runs else 0
            ),
            "failure_breakdown": dict(failure_counts),
        }

    # Skill ablation
    model_ids = set(r.model_id for r in results)
    for model_id in model_ids:
        bare = by_model_condition.get((model_id, "bare"), [])
        skill = by_model_condition.get((model_id, "skill"), [])
        if bare and skill:
            bare_total = sum(r.total_cost_usd for r in bare)
            skill_total = sum(r.total_cost_usd for r in skill)
            bare_solved = sum(1 for r in bare if r.solved)
            skill_solved = sum(1 for r in skill if r.solved)
            bare_exp = bare_total / bare_solved if bare_solved else None
            skill_exp = skill_total / skill_solved if skill_solved else None
            stats["skill_ablation"][model_id] = {
                "bare_avg_cost": bare_total / bare_solved if bare_solved else None,
                "skill_avg_cost": skill_total / skill_solved if skill_solved else None,
                "bare_expected_cost": bare_exp,
                "skill_expected_cost": skill_exp,
                "bare_completion_rate": bare_solved / len(bare),
                "skill_completion_rate": skill_solved / len(skill),
                "cost_reduction": (
                    (bare_exp - skill_exp) / bare_exp
                    if bare_exp is not None and skill_exp is not None and bare_exp > 0
                    else None
                ),
            }

    return stats


def compute_repeat_stats(results: list[RunResult]) -> dict:
    """Compute mean/std/CI across repeated runs.

    Groups by (model_id, problem_id, condition, max_rounds) and computes
    stats across repeat_id values.
    """
    from collections import defaultdict

    groups = defaultdict(list)
    for r in results:
        key = (r.model_id, r.problem_id, r.condition, r.max_rounds)
        groups[key].append(r)

    repeat_stats = {}
    for key, runs in groups.items():
        model_id, problem_id, condition, max_rounds = key
        costs = [r.total_cost_usd for r in runs]
        solved_flags = [1 if r.solved else 0 for r in runs]
        rounds_list = [r.total_rounds for r in runs if r.solved]

        n = len(costs)
        mean_cost = sum(costs) / n
        std_cost = _std(costs) if n > 1 else 0
        ci95_cost = 1.96 * std_cost / math.sqrt(n) if n > 1 else 0

        completion_rate = sum(solved_flags) / n
        # Wilson score interval for completion rate
        ci95_rate = _wilson_ci(sum(solved_flags), n) if n > 0 else (0, 0)

        repeat_stats[key] = {
            "n_repeats": n,
            "mean_cost": mean_cost,
            "std_cost": std_cost,
            "ci95_cost": ci95_cost,
            "completion_rate": completion_rate,
            "ci95_rate_lower": ci95_rate[0],
            "ci95_rate_upper": ci95_rate[1],
            "mean_rounds": _mean(rounds_list) if rounds_list else None,
        }

    return repeat_stats


def _median(values: list[float | int]) -> float:
    if not values:
        return 0
    s = sorted(values)
    n = len(s)
    if n % 2 == 1:
        return s[n // 2]
    return (s[n // 2 - 1] + s[n // 2]) / 2


def _mean(values: list[float | int]) -> float:
    return sum(values) / len(values) if values else 0


def _std(values: list[float | int]) -> float:
    if len(values) < 2:
        return 0
    m = _mean(values)
    return math.sqrt(sum((v - m) ** 2 for v in values) / (len(values) - 1))


def _wilson_ci(successes: int, total: int, z: float = 1.96) -> tuple[float, float]:
    """Wilson score confidence interval for a proportion."""
    if total == 0:
        return (0.0, 0.0)
    p = successes / total
    denom = 1 + z * z / total
    centre = p + z * z / (2 * total)
    spread = z * math.sqrt((p * (1 - p) + z * z / (4 * total)) / total)
    lower = max(0.0, (centre - spread) / denom)
    upper = min(1.0, (centre + spread) / denom)
    return (lower, upper)
