#!/usr/bin/env python3
"""Extract benchmark problems from StatLean .lean files into problems.yaml.

Usage:
    python extract_problems.py                  # extract all defined problems
    python extract_problems.py --verify         # verify ground truth compiles
    python extract_problems.py --single scheffe # extract one problem
"""

import argparse
import sys
from pathlib import Path

import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from harness.problem_extractor import extract_problem, problem_to_yaml
from harness.compiler import LeanCompiler

# Problem definitions — the canonical list
PROBLEM_DEFINITIONS = [
    # === EASY (5) ===
    {
        "problem_id": "slutsky_div",
        "theorem_name": "slutsky_div",
        "lean_file": "Statlean/LimitTheorems/Slutsky.lean",
        "difficulty": "easy",
        "categories": ["convergence", "arithmetic"],
        "api_sections": ["Convergence", "Filter"],
        "keywords": ["tendsto", "div", "InProbability"],
    },
    {
        "problem_id": "gauss_markov",
        "theorem_name": "gauss_markov",
        "lean_file": "Statlean/Regression/GaussMarkov.lean",
        "difficulty": "easy",
        "categories": ["algebra", "integral"],
        "api_sections": ["Variance", "Integral"],
        "keywords": ["BLUE", "regression", "variance"],
    },
    {
        "problem_id": "unbiased_risk_eq_variance",
        "theorem_name": "mse_eq_variance_of_unbiased",
        "lean_file": "Statlean/Estimator/Basic.lean",
        "difficulty": "easy",
        "categories": ["integral", "algebra"],
        "api_sections": ["Variance", "Integral"],
        "keywords": ["risk", "bias", "variance"],
    },
    {
        "problem_id": "basu_theorem",
        "theorem_name": "basu_theorem",
        "lean_file": "Statlean/Sufficiency/Basu.lean",
        "difficulty": "easy",
        "categories": ["independence", "measurability"],
        "api_sections": ["Independence", "Conditional Expectation"],
        "keywords": ["ancillary", "sufficient", "independent"],
    },
    {
        "problem_id": "mse_bias_variance",
        "theorem_name": "mse_eq_bias_sq_add_variance",
        "lean_file": "Statlean/Estimator/Basic.lean",
        "difficulty": "easy",
        "categories": ["integral", "algebra"],
        "api_sections": ["Variance", "Integral"],
        "keywords": ["MSE", "bias", "variance", "decomposition"],
    },
    # === MEDIUM (8) ===
    {
        "problem_id": "rao_blackwell_mse",
        "theorem_name": "rb_mse_decomposition",
        "lean_file": "Statlean/Variance/RaoBlackwell.lean",
        "difficulty": "medium",
        "categories": ["condExp", "integral", "algebra"],
        "api_sections": ["Conditional Expectation", "Variance", "Integral"],
        "keywords": ["Rao-Blackwell", "MSE", "condExp"],
    },
    {
        "problem_id": "scheffe",
        "theorem_name": "scheffe",
        "lean_file": "Statlean/LimitTheorems/Scheffe.lean",
        "difficulty": "medium",
        "categories": ["integral", "ae", "convergence"],
        "api_sections": ["Integral", "Convergence", "Norms / Lp"],
        "keywords": ["Scheffé", "L1", "density", "convergence"],
    },
    {
        "problem_id": "delta_method",
        "theorem_name": "delta_method",
        "lean_file": "Statlean/LimitTheorems/DeltaMethod.lean",
        "difficulty": "medium",
        "categories": ["convergence", "chains"],
        "api_sections": ["Convergence", "CharFun", "Topology / Metric"],
        "keywords": ["delta", "differentiable", "CLT"],
    },
    {
        "problem_id": "levy_forward",
        "theorem_name": "levy_forward",
        "lean_file": "Statlean/LimitTheorems/Levy.lean",
        "difficulty": "medium",
        "categories": ["convergence", "integral"],
        "api_sections": ["CharFun", "Convergence", "Integral"],
        "keywords": ["Lévy", "charFun", "weak convergence"],
    },
    {
        "problem_id": "condexp_reduces_mse",
        "theorem_name": "condExp_reduces_mse",
        "lean_file": "Statlean/Sufficiency/LehmannScheffe.lean",
        "difficulty": "medium",
        "categories": ["condExp", "integral", "algebra"],
        "api_sections": ["Conditional Expectation", "Integral", "Norms / Lp"],
        "keywords": ["MSE", "projection", "L2"],
    },
    {
        "problem_id": "factorization_backward",
        "theorem_name": "factorization_backward",
        "lean_file": "Statlean/Sufficiency/Factorization.lean",
        "difficulty": "medium",
        "categories": ["measurability", "integral"],
        "api_sections": ["Integral", "Independence"],
        "keywords": ["factorization", "sufficient", "rnDeriv"],
    },
    {
        "problem_id": "cramer_rao",
        "theorem_name": "cramer_rao",
        "lean_file": "Statlean/Information/CramerRao.lean",
        "difficulty": "medium",
        "categories": ["integral", "algebra", "inequality"],
        "api_sections": ["Integral", "Variance"],
        "keywords": ["Cramér-Rao", "Fisher", "information"],
    },
    {
        "problem_id": "minimal_sufficiency",
        "theorem_name": "minimalSufficient_of_densityRatio",
        "lean_file": "Statlean/Sufficiency/MinimalSufficiency.lean",
        "difficulty": "medium",
        "categories": ["measurability", "integral"],
        "api_sections": ["Integral", "Independence"],
        "keywords": ["minimal", "sufficient", "rnDeriv"],
    },
    # === HARD (4) ===
    {
        "problem_id": "lindeberg_feller",
        "theorem_name": "lindeberg_feller_clt",
        "lean_file": "Statlean/LimitTheorems/LindebergFeller.lean",
        "difficulty": "hard",
        "categories": ["convergence", "integral", "chains", "arithmetic"],
        "api_sections": ["CharFun", "Convergence", "Integral", "Independence"],
        "keywords": ["Lindeberg", "Feller", "CLT", "triangular"],
    },
    {
        "problem_id": "uniform_slln",
        "theorem_name": "uniform_slln",
        "lean_file": "Statlean/LimitTheorems/USLLN.lean",
        "difficulty": "hard",
        "categories": ["convergence", "integral", "chains"],
        "api_sections": ["Convergence", "Integral", "Topology / Metric", "Compactness"],
        "keywords": ["SLLN", "uniform", "strong law"],
    },
    {
        "problem_id": "charfun_taylor",
        "theorem_name": "charfun_normalized_sum_bound",
        "lean_file": "Statlean/CharFun/Taylor.lean",
        "difficulty": "hard",
        "categories": ["integral", "chains", "arithmetic"],
        "api_sections": ["CharFun", "Integral", "Norms / Lp"],
        "keywords": ["Taylor", "characteristic", "bound"],
    },
    {
        "problem_id": "levy_continuity",
        "theorem_name": "levy_continuity",
        "lean_file": "Statlean/LimitTheorems/Levy.lean",
        "difficulty": "hard",
        "categories": ["convergence", "integral", "chains"],
        "api_sections": ["CharFun", "Convergence", "Integral", "Tightness / Prokhorov"],
        "keywords": ["Lévy", "continuity", "tightness", "Prokhorov"],
    },
    # === OPEN (3) — existing sorry gaps ===
    {
        "problem_id": "esseen_concentration",
        "theorem_name": "esseen_concentration_universal",
        "lean_file": "Statlean/LimitTheorems/BerryEsseen.lean",
        "difficulty": "open",
        "categories": ["integral", "chains", "arithmetic"],
        "api_sections": ["CharFun", "Integral"],
        "keywords": ["Berry-Esseen", "Stieltjes", "Esseen", "concentration"],
    },
    {
        "problem_id": "hypercontractivity",
        "theorem_name": "memLp_four_of_W12_gaussian",
        "lean_file": "Statlean/Gaussian/Poincare.lean",
        "difficulty": "open",
        "categories": ["integral", "inequality"],
        "api_sections": ["Norms / Lp", "Integral"],
        "keywords": ["hypercontractivity", "Nelson", "Hermite", "W12"],
    },
    {
        "problem_id": "poincare_condvar",
        "theorem_name": "gaussian_poincare_coord_bound_core",
        "lean_file": "Statlean/Gaussian/Poincare.lean",
        "difficulty": "open",
        "categories": ["condExp", "integral", "inequality"],
        "api_sections": ["Conditional Expectation", "Variance", "Integral"],
        "keywords": ["Poincaré", "condVar", "gradient"],
    },
]


def extract_all_problems(
    definitions: list[dict] | None = None, verify: bool = False
) -> list[dict]:
    """Extract problem definitions and optionally verify ground truth.

    Args:
        definitions: List of problem defs to extract. Defaults to PROBLEM_DEFINITIONS.
        verify: If True, compile ground truth to confirm it passes.
    """
    if definitions is None:
        definitions = PROBLEM_DEFINITIONS
    compiler = LeanCompiler() if verify else None
    results = []

    for defn in definitions:
        print(f"Extracting: {defn['problem_id']}...", end=" ", flush=True)
        try:
            problem = extract_problem(**defn)
            entry = problem_to_yaml(problem)
            # Add extra fields from definition
            entry["categories"] = defn.get("categories", [])
            entry["api_sections"] = defn.get("api_sections", [])
            entry["keywords"] = defn.get("keywords", [])
            results.append(entry)
            print(f"OK ({problem.proof_lines} lines)")

            if verify and compiler:
                print(f"  Verifying ground truth...", end=" ", flush=True)
                cr = compiler.check_proof(
                    defn["lean_file"],
                    defn["theorem_name"],
                    problem.ground_truth,
                )
                if cr.success:
                    print("PASS")
                else:
                    print(f"FAIL: {cr.error_message[:100]}")

        except Exception as e:
            print(f"ERROR: {e}")

    return results


def main():
    parser = argparse.ArgumentParser(description="Extract benchmark problems")
    parser.add_argument("--verify", action="store_true", help="Verify ground truth compiles")
    parser.add_argument("--single", type=str, help="Extract single problem by ID")
    parser.add_argument(
        "--output", "-o", type=str,
        default=str(Path(__file__).resolve().parent.parent / "config" / "problems.yaml"),
        help="Output path"
    )

    args = parser.parse_args()

    if args.single:
        defns = [d for d in PROBLEM_DEFINITIONS if d["problem_id"] == args.single]
        if not defns:
            print(f"Unknown problem: {args.single}")
            print(f"Available: {[d['problem_id'] for d in PROBLEM_DEFINITIONS]}")
            return 1
    else:
        defns = None  # use all

    problems = extract_all_problems(definitions=defns, verify=args.verify)

    if not problems:
        print("No problems extracted!")
        return 1

    output = {"problems": problems}
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        yaml.dump(output, f, default_flow_style=False, allow_unicode=True, sort_keys=False)

    print(f"\nWrote {len(problems)} problems to {output_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
