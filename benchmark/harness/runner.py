"""Main experiment runner — orchestrates model × problem × condition experiments."""

from __future__ import annotations

import logging
import re
import time
from pathlib import Path

import yaml

from .compiler import CompileResult, LeanCompiler
from .metrics import (
    FailureType,
    MetricsRecorder,
    RoundMetrics,
    RunResult,
    generate_run_id,
)
from .model_adapter import ModelAdapter, create_adapter
from .problem_extractor import (
    Problem,
    build_prompt_for_problem,
    build_retry_prompt,
    extract_problem,
)
from .skill_builder import build_skill_context, load_retry_template

logger = logging.getLogger(__name__)

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
CONFIG_DIR = Path(__file__).resolve().parent.parent / "config"


def load_problems(problems_path: Path | None = None) -> list[dict]:
    """Load problem definitions from problems.yaml."""
    if problems_path is None:
        problems_path = CONFIG_DIR / "problems.yaml"
    with open(problems_path) as f:
        data = yaml.safe_load(f)
    return data.get("problems", [])


def extract_proof_from_response(response_text: str) -> tuple[str, bool]:
    """Extract Lean proof body from model response.

    Returns:
        (proof_body, parse_ok): The extracted proof and whether extraction
        found a proper code block (vs raw text fallback).
    """
    # Try ```lean ... ```
    lean_blocks = re.findall(r"```lean\s*\n(.*?)```", response_text, re.DOTALL)
    if lean_blocks:
        return lean_blocks[-1].strip(), True

    # Try any ``` block
    any_blocks = re.findall(r"```\s*\n(.*?)```", response_text, re.DOTALL)
    if any_blocks:
        return any_blocks[-1].strip(), True

    # Fallback: strip common prefixes and return raw text
    text = response_text.strip()
    if not text:
        return "", False
    for prefix in [":= by\n", ":= by ", "by\n", "by "]:
        if text.lower().startswith(prefix):
            text = text[len(prefix):]
            break
    return text.strip(), False


def _classify_failure(
    compile_result: CompileResult | None,
    gen_error: Exception | None = None,
    parse_ok: bool = True,
) -> str:
    """Classify a failure into a FailureType category.

    Priority: gen_error > compile_result > parse_ok > fallback.

    Key rule: if compilation was actually attempted (compile_result exists and
    error_message != skipped), the result is ALWAYS a compile-level classification
    (SUCCESS / COMPILE_ERROR / SORRY_REMAINING / TIMEOUT), regardless of parse_ok.
    PARSER_ERROR is reserved for cases where no proof could be extracted at all
    (proof_body empty → compilation never attempted).
    """
    if gen_error is not None:
        err_str = str(gen_error).lower()
        if "timeout" in err_str or "timed out" in err_str:
            return FailureType.TIMEOUT
        if any(kw in err_str for kw in ["rate limit", "429", "quota", "connection"]):
            return FailureType.INFRA_ERROR
        return FailureType.INFRA_ERROR

    if compile_result is not None:
        if compile_result.success:
            return FailureType.SUCCESS
        if "sorry" in compile_result.error_message.lower():
            return FailureType.SORRY_REMAINING
        if "timed out" in compile_result.error_message.lower():
            return FailureType.TIMEOUT
        # Compile actually ran and failed — always COMPILE_ERROR,
        # even if parse_ok=False (the extracted text compiled but failed).
        return FailureType.COMPILE_ERROR

    # No compile result and no gen error → extraction failed entirely
    if not parse_ok:
        return FailureType.PARSER_ERROR

    return FailureType.INFRA_ERROR


def run_single_experiment(
    adapter: ModelAdapter,
    problem: Problem,
    condition: str,
    max_rounds: int = 4,
    compiler: LeanCompiler | None = None,
    run_id: str | None = None,
    repeat_id: int = 0,
    skip_compile: bool = False,
) -> RunResult:
    """Run one experiment: (model, problem, condition).

    Args:
        adapter: Model adapter to use
        problem: Benchmark problem
        condition: "bare" or "skill"
        max_rounds: Maximum generation-compile rounds
        compiler: LeanCompiler instance (creates one if None)
        run_id: Experiment run ID
        repeat_id: Which repeat this is (0-indexed)
        skip_compile: If True, skip compilation (for dry runs)

    Returns:
        RunResult with all round metrics.
    """
    if compiler is None:
        compiler = LeanCompiler()
    if run_id is None:
        run_id = generate_run_id()

    result = RunResult(
        run_id=run_id,
        problem_id=problem.problem_id,
        model_id=adapter.model_id,
        condition=condition,
        max_rounds=max_rounds,
        repeat_id=repeat_id,
    )

    # Build skill context if needed
    skill_context = None
    if condition == "skill":
        skill_context = build_skill_context({
            "categories": problem.categories,
            "api_sections": problem.api_sections,
            "keywords": problem.keywords,
        })

    # Build initial prompt
    messages = build_prompt_for_problem(problem, skill_context)
    retry_template = load_retry_template() if max_rounds > 1 else None

    for round_num in range(1, max_rounds + 1):
        logger.info(
            f"  Round {round_num}/{max_rounds}: "
            f"{problem.problem_id} × {adapter.model_id} ({condition})"
        )

        # Generate
        gen_error = None
        gen_result = None
        try:
            gen_result = adapter.generate(messages)
        except Exception as e:
            gen_error = e
            logger.error(f"  Generation failed: {e}")
            failure_type = _classify_failure(None, gen_error=e)
            result.rounds.append(RoundMetrics(
                round=round_num,
                input_tokens=0,
                output_tokens=0,
                cost_usd=0.0,
                latency_s=0.0,
                compile_success=False,
                error_snippet=f"Generation error: {e}",
                failure_type=failure_type,
            ))
            break

        # Extract proof from response
        proof_body, parse_ok = extract_proof_from_response(gen_result.text)
        logger.debug(f"  Extracted proof ({len(proof_body)} chars, parse_ok={parse_ok})")

        # If extraction failed completely, record and continue
        if not proof_body:
            failure_type = FailureType.PARSER_ERROR
            result.rounds.append(RoundMetrics(
                round=round_num,
                input_tokens=gen_result.input_tokens,
                output_tokens=gen_result.output_tokens,
                cost_usd=gen_result.cost_usd,
                latency_s=gen_result.latency_s,
                compile_success=False,
                error_snippet="Failed to extract proof from model response",
                failure_type=failure_type,
            ))
            if round_num < max_rounds:
                messages.append({"role": "assistant", "content": gen_result.text})
                messages.append({
                    "role": "user",
                    "content": (
                        "I could not find a proof in your response. "
                        "Please provide the proof body wrapped in a ```lean code block."
                    ),
                })
            continue

        # Compile (or skip in dry-run mode)
        if skip_compile:
            # Dry-run: record one round with generation output, then stop.
            # No compilation means no meaningful success/failure signal.
            result.rounds.append(RoundMetrics(
                round=round_num,
                input_tokens=gen_result.input_tokens,
                output_tokens=gen_result.output_tokens,
                cost_usd=gen_result.cost_usd,
                latency_s=gen_result.latency_s,
                compile_success=False,
                compile_time_s=0.0,
                error_snippet="(dry-run: compilation skipped)",
                failure_type=FailureType.INFRA_ERROR,
                sampling_params=gen_result.sampling_params,
            ))
            logger.info("  Dry-run: skipping compilation, stopping after round 1")
            break

        compile_result = compiler.check_proof(
            problem.lean_file, problem.theorem_name, proof_body
        )
        logger.info(
            f"  Compile: {'OK' if compile_result.success else 'FAIL'} "
            f"({compile_result.wall_time_s:.1f}s)"
        )

        # Classify failure type
        failure_type = _classify_failure(compile_result, parse_ok=parse_ok)

        # Record round metrics
        round_metrics = RoundMetrics(
            round=round_num,
            input_tokens=gen_result.input_tokens,
            output_tokens=gen_result.output_tokens,
            cost_usd=gen_result.cost_usd,
            latency_s=gen_result.latency_s,
            compile_success=compile_result.success,
            compile_time_s=compile_result.wall_time_s,
            error_snippet=(
                compile_result.error_message[:500]
                if compile_result.error_message else None
            ),
            sorry_count=compile_result.sorry_count,
            failure_type=failure_type,
            sampling_params=gen_result.sampling_params,
        )
        result.rounds.append(round_metrics)

        # Success → done
        if compile_result.success:
            logger.info(f"  SOLVED in round {round_num}!")
            break

        # Prepare retry prompt
        if round_num < max_rounds:
            messages.append({"role": "assistant", "content": gen_result.text})
            retry_msg = build_retry_prompt(
                compile_result.error_message, proof_body, retry_template
            )
            messages.append(retry_msg)

    result.finalize()
    return result


def run_experiment_matrix(
    model_names: list[str],
    problem_ids: list[str] | None = None,
    conditions: list[str] | None = None,
    max_rounds_map: dict[str, int] | None = None,
    output_dir: str | Path | None = None,
    skip_compile: bool = False,
    problems_path: Path | None = None,
    repeats: int = 1,
) -> list[RunResult]:
    """Run the full experiment matrix: models × problems × conditions × repeats.

    Args:
        model_names: List of model keys from models.yaml
        problem_ids: Problem IDs to run (None = all)
        conditions: ["bare", "skill"] or subset
        max_rounds_map: {"single": 1, "multi": 4} round configurations
        output_dir: Directory for result files
        skip_compile: Skip compilation (dry run)
        problems_path: Custom problems.yaml path
        repeats: Number of times to repeat each experiment
    """
    if conditions is None:
        conditions = ["bare", "skill"]
    if max_rounds_map is None:
        max_rounds_map = {"single": 1, "multi": 4}
    if output_dir is None:
        output_dir = Path(__file__).resolve().parent.parent / "results" / "raw"

    recorder = MetricsRecorder(output_dir)
    compiler = LeanCompiler()
    run_id = generate_run_id()

    # Resolve actual problems config path for metadata
    actual_problems_path = str(
        problems_path if problems_path else CONFIG_DIR / "problems.yaml"
    )

    # Load problems
    all_problems_config = load_problems(problems_path)
    if problem_ids:
        all_problems_config = [
            p for p in all_problems_config if p["problem_id"] in problem_ids
        ]

    if not all_problems_config:
        logger.warning("No problems matched the filter!")
        return []

    # Extract Problem objects
    problems: list[Problem] = []
    for pc in all_problems_config:
        try:
            p = extract_problem(
                lean_file=pc["lean_file"],
                theorem_name=pc["theorem_name"],
                problem_id=pc["problem_id"],
                difficulty=pc.get("difficulty", "medium"),
                categories=pc.get("categories", []),
                api_sections=pc.get("api_sections", []),
                keywords=pc.get("keywords", []),
            )
            problems.append(p)
        except Exception as e:
            logger.error(f"Failed to extract problem {pc.get('problem_id', '?')}: {e}")

    total_experiments = (
        len(model_names) * len(problems) * len(conditions)
        * len(max_rounds_map) * repeats
    )
    logger.info(
        f"Loaded {len(problems)} problems, {len(model_names)} models, "
        f"{len(conditions)} conditions, {len(max_rounds_map)} round configs, "
        f"{repeats} repeats = {total_experiments} total experiments"
    )

    all_results = []

    for model_name in model_names:
        logger.info(f"\n=== Model: {model_name} ===")
        try:
            adapter = create_adapter(model_name)
        except Exception as e:
            logger.error(f"Failed to create adapter for {model_name}: {e}")
            continue

        for problem in problems:
            for condition in conditions:
                for round_label, max_rounds in max_rounds_map.items():
                    for rep in range(repeats):
                        rep_suffix = f" rep={rep}" if repeats > 1 else ""
                        logger.info(
                            f"\n--- {problem.problem_id} | {condition} | "
                            f"R={max_rounds}{rep_suffix} ---"
                        )
                        result = run_single_experiment(
                            adapter=adapter,
                            problem=problem,
                            condition=condition,
                            max_rounds=max_rounds,
                            compiler=compiler,
                            run_id=run_id,
                            repeat_id=rep,
                            skip_compile=skip_compile,
                        )
                        result.problems_config_path = actual_problems_path
                        recorder.record(result)
                        all_results.append(result)

                        status = "SOLVED" if result.solved else "FAILED"
                        logger.info(
                            f"  -> {status} | ${result.total_cost_usd:.4f} | "
                            f"{result.total_rounds} rounds | {result.total_time_s:.1f}s"
                        )

    logger.info(f"\n{'='*60}")
    logger.info(f"Total experiments: {len(all_results)}")
    logger.info(f"Results saved to: {output_dir}/run_{run_id}.jsonl")

    return all_results
