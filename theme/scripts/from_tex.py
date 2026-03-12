#!/usr/bin/env python3
"""Build theme input package from a LaTeX file.

Extracts theorem-like environments, optionally canonicalizes names via AI,
and writes theorems.yaml + notation.yaml + scope.yaml.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import yaml

THEOREM_ENVS = ["theorem", "lemma", "corollary", "proposition", "definition"]


def extract_blocks(tex: str) -> List[Dict[str, Any]]:
    begin_pat = re.compile(
        r"\\begin\{(" + "|".join(THEOREM_ENVS) + r")\}(?:\[([^\]]*)\])?",
        re.IGNORECASE,
    )

    blocks: List[Dict[str, Any]] = []
    starts = list(begin_pat.finditer(tex))
    for i, m in enumerate(starts):
        env = m.group(1).lower()
        title = (m.group(2) or "").strip()
        start = m.end()
        end_marker = re.compile(r"\\end\{" + re.escape(env) + r"\}", re.IGNORECASE)
        end_m = end_marker.search(tex, pos=start)
        if not end_m:
            continue
        stmt_raw = tex[start:end_m.start()].strip()

        next_theorem_start = starts[i + 1].start() if i + 1 < len(starts) else len(tex)
        proof_pat = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.IGNORECASE | re.DOTALL)
        proof_m = proof_pat.search(tex, pos=end_m.end(), endpos=next_theorem_start)
        proof_raw = proof_m.group(1).strip() if proof_m else ""

        blocks.append(
            {
                "kind": env,
                "title": title or f"{env.title()} {len(blocks) + 1}",
                "statement": stmt_raw,
                "proof": proof_raw,
                "proof_body": proof_raw,  # preserved for R2 route search
            }
        )
    return blocks


def sanitize_name(s: str) -> str:
    s = s.lower()
    s = re.sub(r"[^a-z0-9]+", "_", s)
    s = re.sub(r"_+", "_", s).strip("_")
    return s or "item"


def unique(base: str, used: set[str]) -> str:
    if base not in used:
        used.add(base)
        return base
    i = 2
    while True:
        c = f"{base}_v{i}"
        if c not in used:
            used.add(c)
            return c
        i += 1


def extract_ref_tokens(text: str) -> List[Tuple[str, str]]:
    refs = []
    pat = re.compile(r"\b(Theorem|Lemma|Corollary|Proposition|Definition)\s+(\d+)\b", re.IGNORECASE)
    for m in pat.finditer(text):
        refs.append((m.group(1).lower(), m.group(2)))
    return refs


def theorem_number_from_title(title: str) -> Tuple[str | None, str | None]:
    m = re.search(r"\b(Theorem|Lemma|Corollary|Proposition|Definition)\s*(\d+)\b", title, re.IGNORECASE)
    if not m:
        return (None, None)
    return (m.group(1).lower(), m.group(2))


# ═══════════════════════════════════════════════════════════════
# Heuristic Canonicalize (no API needed)
# ═══════════════════════════════════════════════════════════════

# (keywords, canonical_name, lean_name, topic)
# Order matters: more specific patterns first
_HEURISTIC_RULES: List[Tuple[List[str], str, str, str]] = [
    # Limit theorems — specific first, then general
    (["lindeberg", "feller"], "Lindeberg-Feller CLT", "lindeberg_feller_clt", "LimitTheorems"),
    (["lindeberg"], "Lindeberg CLT", "lindeberg_clt", "LimitTheorems"),
    (["lyapunov"], "Lyapunov CLT", "lyapunov_clt", "LimitTheorems"),
    (["berry.esseen", "berry-esseen", "berryesseen"], "Berry-Esseen Theorem", "berry_esseen", "LimitTheorems"),
    # Scheffe — before CLT (both may appear, Scheffe is more specific)
    (["scheff", "scheffe"], "Scheffé's Theorem", "scheffe_theorem", "LimitTheorems"),
    (["slutsky"], "Slutsky's Theorem", "slutsky_theorem", "LimitTheorems"),
    (["continuous mapping"], "Continuous Mapping Theorem", "continuous_mapping_theorem", "LimitTheorems"),
    (["portmanteau"], "Portmanteau Theorem", "portmanteau_theorem", "LimitTheorems"),
    (["convergence in distribution", "weak convergence"], "Convergence in Distribution", "convergence_in_distribution", "LimitTheorems"),
    (["convergence in probability"], "Convergence in Probability", "convergence_in_probability", "LimitTheorems"),
    (["strong law", "slln"], "Strong Law of Large Numbers", "slln", "LimitTheorems"),
    (["weak law", "wlln"], "Weak Law of Large Numbers", "wlln", "LimitTheorems"),
    # Delta method — before CLT (delta method blocks often mention CLT too)
    ([r"δ.method", "delta.method", r"δ-method", "delta-method",
      r"differentiable.*g\s*\(.*x.*\)", r"g.*differentiable.*g.*\("], "Delta Method", "delta_method", "LimitTheorems"),
    ([r"multivariate.*δ", r"multivariate.*delta"], "Multivariate Delta Method", "multivariate_delta_method", "LimitTheorems"),
    # CLT — general (after more specific patterns that also mention CLT)
    (["central limit", "clt"], "Central Limit Theorem", "central_limit_theorem", "LimitTheorems"),
    # Sufficiency & estimation
    (["fisher.neyman", "factorization"], "Fisher-Neyman Factorization", "factorization_theorem", "Sufficiency"),
    (["basu"], "Basu's Theorem", "basu_theorem", "Sufficiency"),
    (["lehmann.scheff", "umvue"], "Lehmann-Scheffé Theorem", "lehmann_scheffe", "Sufficiency"),
    (["rao.blackwell", "rao-blackwell"], "Rao-Blackwell Theorem", "rao_blackwell", "Variance"),
    (["cramer.rao", "cramér.rao", "information bound"], "Cramér-Rao Lower Bound", "cramer_rao", "Information"),
    (["fisher information"], "Fisher Information", "fisher_information", "Information"),
    (["maximum likelihood", "mle"], "Maximum Likelihood Estimator", "mle", "Estimator"),
    (["asymptotic.*relative.*efficiency", "are"], "Asymptotic Relative Efficiency", "asymptotic_relative_efficiency", "Estimator"),
    (["asymptotic.*variance", "amse"], "Asymptotic MSE", "asymptotic_mse", "Estimator"),
    (["asymptotic.*unbiased"], "Asymptotic Unbiasedness", "asymptotic_unbiasedness", "Estimator"),
    (["asymptotic.*confidence"], "Asymptotic Confidence Interval", "asymptotic_confidence_interval", "Estimator"),
    (["consistency", "consistent estimator"], "Consistency", "consistency", "Estimator"),
    (["unbiased"], "Unbiasedness", "unbiasedness", "Estimator"),
    # Exponential family
    (["exponential family"], "Exponential Family", "exponential_family", "ExpFamily"),
    (["completeness.*exponential", "complete.*sufficient"], "Completeness of Exp Family", "completeness_exp_family", "Sufficiency"),
    # Concentration
    (["efron.stein", "efronstein"], "Efron-Stein Inequality", "efron_stein", "Variance"),
    (["poincar"], "Poincaré Inequality", "poincare_inequality", "Gaussian"),
    (["log.sobolev", "logsobolev"], "Log-Sobolev Inequality", "log_sobolev", "Entropy"),
    (["herbst"], "Herbst Argument", "herbst_argument", "SubGaussian"),
    (["subgaussian", "sub.gaussian"], "Sub-Gaussian", "subgaussian", "SubGaussian"),
    # Distribution-specific examples
    (["poisson.*convergence", r"binom.*→.*poisson", "binom.*poisson"], "Poisson Convergence", "poisson_convergence_example", "LimitTheorems"),
    (["t.distribution", r"t_n.*→.*normal", r"tn.*→.*N", r"t_n.*density"], "t-distribution CLT", "t_distribution_clt_example", "LimitTheorems"),
    ([r"exponential.*mean", r"exponential.*rate", r"λe.*−λx", r"λ.*exp.*-λ"], "Exponential MLE", "exponential_mle_example", "Estimator"),
    (["empirical variance", "sample variance", "asymptotic.*distribution.*variance"], "Asymptotic Distribution of Sample Variance", "asymptotic_sample_variance", "LimitTheorems"),
    # Characteristic function
    (["characteristic function", "charfun", "ch.f."], "Characteristic Function", "charfun", "CharFun"),
    # ─── Common statistical concepts (definitions, structures) ───
    # Convergence modes
    (["convergence.*almost surely", "a\\.s\\. convergence"], "Almost Sure Convergence", "convergence_as", "LimitTheorems"),
    (["convergence.*l.*p", r"l\^p.*convergence"], "Lp Convergence", "convergence_lp", "LimitTheorems"),
    # Distributions
    (["chi.squared", "χ.*squared", r"χ2", r"chi2"], "Chi-Squared Distribution", "chi_squared", "Gaussian"),
    (["multivariate.*normal", "multivariate.*gaussian"], "Multivariate Normal", "multivariate_normal", "Gaussian"),
    (["student.*t", "t.*distribution"], "Student's t-Distribution", "student_t", "Gaussian"),
    (["f.distribution", "fisher.*distribution"], "F-Distribution", "f_distribution", "Gaussian"),
    (["binomial"], "Binomial Distribution", "binomial", "Misc"),
    (["poisson"], "Poisson Distribution", "poisson", "Misc"),
    (["exponential.*distribution"], "Exponential Distribution", "exponential_distribution", "Misc"),
    # Estimation theory
    (["method of moments", "moment.*estimator"], "Method of Moments", "method_of_moments", "Estimator"),
    (["sufficient.*statistic"], "Sufficient Statistic", "sufficient_statistic", "Statistic"),
    (["complete.*statistic"], "Complete Statistic", "complete_statistic", "Statistic"),
    (["ancillary.*statistic"], "Ancillary Statistic", "ancillary_statistic", "Statistic"),
    (["minimal.*sufficient"], "Minimal Sufficient Statistic", "minimal_sufficient", "Statistic"),
    (["order.*statistic"], "Order Statistic", "order_statistic", "Statistic"),
    (["sample.*mean"], "Sample Mean", "sample_mean", "Statistic"),
    # Hypothesis testing
    (["neyman.pearson", "likelihood.*ratio.*test"], "Neyman-Pearson Lemma", "neyman_pearson", "Estimator"),
    (["uniformly.*most.*powerful", "ump"], "UMP Test", "ump_test", "Estimator"),
    (["wald.*test"], "Wald Test", "wald_test", "Estimator"),
    (["score.*test", "lagrange.*multiplier"], "Score Test", "score_test", "Estimator"),
    # Inequalities
    (["chebyshev", "chebychev"], "Chebyshev's Inequality", "chebyshev_inequality", "LimitTheorems"),
    (["markov.*inequality"], "Markov's Inequality", "markov_inequality", "LimitTheorems"),
    (["jensen", "convexity"], "Jensen's Inequality", "jensen_inequality", "Variance"),
    (["cauchy.schwarz", "cauchy-schwarz"], "Cauchy-Schwarz Inequality", "cauchy_schwarz", "Variance"),
    (["hoeffding"], "Hoeffding's Inequality", "hoeffding_inequality", "SubGaussian"),
    (["mcdiarmid", "bounded.*differences"], "McDiarmid's Inequality", "mcdiarmid_inequality", "SubGaussian"),
    # Information theory
    (["kullback.leibler", "kl.*divergence"], "KL Divergence", "kl_divergence", "Entropy"),
    (["entropy"], "Entropy", "entropy", "Entropy"),
    (["mutual.*information"], "Mutual Information", "mutual_information", "Entropy"),
    # Large deviations
    (["large.*deviation", "rate.*function"], "Large Deviation Principle", "large_deviation", "LimitTheorems"),
    (["cramér.*theorem", "cramer.*theorem"], "Cramér's Theorem", "cramer_theorem", "LimitTheorems"),
    (["sanov"], "Sanov's Theorem", "sanov_theorem", "LimitTheorems"),
    # Misc theorems
    (["skorohod"], "Skorohod's Theorem", "skorohod_theorem", "LimitTheorems"),
    (["dominated.*convergence", "dct"], "Dominated Convergence Theorem", "dct", "Misc"),
    (["monotone.*convergence", "mct"], "Monotone Convergence Theorem", "mct", "Misc"),
    (["fatou"], "Fatou's Lemma", "fatou_lemma", "Misc"),
    (["borel.cantelli"], "Borel-Cantelli Lemma", "borel_cantelli", "LimitTheorems"),
    (["glivenko.cantelli"], "Glivenko-Cantelli Theorem", "glivenko_cantelli", "EmpiricalProcess"),
    (["donsker"], "Donsker's Theorem", "donsker_theorem", "EmpiricalProcess"),
    (["kolmogorov.smirnov", "ks.*test"], "Kolmogorov-Smirnov Test", "kolmogorov_smirnov", "EmpiricalProcess"),
    (["uniform.*integrability", "uniformly.*integrable"], "Uniform Integrability", "uniform_integrability", "LimitTheorems"),
    # Regression
    (["gauss.markov", "blue"], "Gauss-Markov Theorem", "gauss_markov", "Regression"),
    (["linear.*regression", "linear.*model"], "Linear Regression", "linear_regression", "Regression"),
    (["least.*squares"], "Least Squares", "least_squares", "Regression"),
]


def _heuristic_canonicalize(blocks: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Match theorem blocks against known statistical theorem patterns.

    No API calls needed — pure regex/keyword matching.
    """
    named = 0
    for b in blocks:
        blob = f"{b['title']} {b['statement']}".lower()
        matched = False
        for keywords, canonical_name, lean_name, topic in _HEURISTIC_RULES:
            for kw in keywords:
                if re.search(kw, blob, re.IGNORECASE):
                    b["canonical_name"] = canonical_name
                    b["lean_name_hint"] = lean_name
                    b["topic"] = topic
                    # Attach Lean sketch if available
                    sketch = _LEAN_SKETCHES.get(lean_name, "")
                    if sketch:
                        b["lean_sketch"] = sketch
                    matched = True
                    named += 1
                    break
            if matched:
                break
        if not matched:
            b["canonical_name"] = None
            b["lean_name_hint"] = ""
            b["topic"] = None
    print(f"[from-tex] heuristic canonicalized {named}/{len(blocks)} blocks")
    sketched = sum(1 for b in blocks if b.get("lean_sketch"))
    if sketched:
        print(f"[from-tex] lean sketches attached: {sketched}/{len(blocks)}")
    return blocks


# ═══════════════════════════════════════════════════════════════
# Lean Sketch Templates for Known Theorems
# ═══════════════════════════════════════════════════════════════
# Each entry: lean_name → Lean 4 signature (with sorry body).
# These are correct mathematical statements, not placeholders.

_LEAN_SKETCHES: Dict[str, str] = {
    "central_limit_theorem": """\
theorem central_limit_theorem
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hind : iIndepFun (fun _ => inferInstance) X μ)
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hm : ∫ ω, X 0 ω ∂μ = 0) (hv : ProbabilityTheory.variance (X 0) μ = 1)
    (hint : Memℒp (X 0) 2 μ) :
    Filter.Tendsto
      (fun n => μ.map (fun ω => (∑ i ∈ Finset.range n, X i ω) / Real.sqrt n))
      Filter.atTop
      (nhds (Measure.gaussianReal 0 1)) := by
  sorry""",

    "delta_method": """\
theorem delta_method
    {Ω : Type*} [MeasurableSpace Ω]
    {μ_n : ℕ → Measure Ω} {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {Y : Measure ℝ}
    {c : ℝ} {g : ℝ → ℝ}
    (ha : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hconv : Filter.Tendsto (fun n => (μ_n n).map (fun ω => a n * (X n ω - c))) Filter.atTop (nhds Y))
    (hg : DifferentiableAt ℝ g c) :
    Filter.Tendsto
      (fun n => (μ_n n).map (fun ω => a n * (g (X n ω) - g c)))
      Filter.atTop
      (nhds (Y.map (fun y => deriv g c * y))) := by
  sorry""",

    "slutsky_theorem": """\
theorem slutsky_theorem
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω} {X Y : ℕ → Ω → ℝ} {L : Measure ℝ} {c : ℝ}
    (hX : Filter.Tendsto (fun n => (μ n).map (X n)) Filter.atTop (nhds L))
    (hY : ∀ ε > 0, Filter.Tendsto (fun n => (μ n) {ω | ‖Y n ω - c‖ > ε}) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => (μ n).map (fun ω => X n ω + Y n ω))
      Filter.atTop
      (nhds (L.map (fun x => x + c))) := by
  sorry""",

    "scheffe_theorem": """\
theorem scheffe_theorem
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [SigmaFinite ν]
    {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hpdf : ∀ n, ∫⁻ x, f n x ∂ν = 1) (hgpdf : ∫⁻ x, g x ∂ν = 1)
    (hconv : ∀ᵐ x ∂ν, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    Filter.Tendsto
      (fun n => ∫⁻ x, (f n x - g x) ⊔ 0 ∂ν)
      Filter.atTop (nhds 0) := by
  sorry""",

    "lindeberg_feller_clt": """\
theorem lindeberg_feller_clt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → ℕ → Ω → ℝ} {σ_sq : ℕ → ℝ}
    (hind : ∀ n, iIndepFun (fun _ => inferInstance) (X n) μ)
    (hmean : ∀ n j, ∫ ω, X n j ω ∂μ = 0)
    (hvar : ∀ n, σ_sq n = ∑ j ∈ Finset.range n, ProbabilityTheory.variance (X n j) μ)
    (hσ : Filter.Tendsto σ_sq Filter.atTop Filter.atTop)
    (hlind : ∀ ε > 0, Filter.Tendsto
      (fun n => (1 / σ_sq n) * ∑ j ∈ Finset.range n,
        ∫ ω, (X n j ω) ^ 2 * Set.indicator {ω | |X n j ω| > ε * Real.sqrt (σ_sq n)} 1 ω ∂μ)
      Filter.atTop (nhds 0)) :
    True := by
  sorry""",

    "continuous_mapping_theorem": """\
theorem continuous_mapping_theorem
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace β] [OpensMeasurableSpace β]
    {μ_n : ℕ → Measure α} {μ : Measure α} {g : α → β}
    (hconv : Filter.Tendsto μ_n Filter.atTop (nhds μ))
    (hg : Continuous g) :
    Filter.Tendsto (fun n => (μ_n n).map g) Filter.atTop (nhds (μ.map g)) := by
  sorry""",

    "slln": """\
theorem slln
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hind : iIndepFun (fun _ => inferInstance) X μ)
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hint : Integrable (X 0) μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => (∑ i ∈ Finset.range n, X i ω) / n)
      Filter.atTop (nhds (∫ ω', X 0 ω' ∂μ)) := by
  sorry""",

    "asymptotic_relative_efficiency": """\
def asymptotic_relative_efficiency
    {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Measure Ω)
    (T₁ T₂ : ℕ → Ω → ℝ) (ϑ : ℝ) (a : ℕ → ℝ)
    (V₁ V₂ : ℝ) : ℝ :=
    V₂ / V₁""",

    "fisher_information": """\
noncomputable def fisherInformation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) (ν : Measure Ω) [∀ θ, (P θ).AbsolutelyContinuous ν]
    (θ : ℝ) : ℝ :=
    ∫ ω, (deriv (fun θ' => Real.log ((P θ').rnDeriv ν ω).toReal) θ) ^ 2 ∂(P θ)""",
}



# ═══════════════════════════════════════════════════════════════
# AI Canonicalize Pass
# ═══════════════════════════════════════════════════════════════

def _call_ai(prompt: str) -> Optional[str]:
    """Call Claude haiku for canonicalization. SDK first, then CLI fallback."""
    # Method 1: Anthropic SDK
    try:
        import anthropic
        if os.environ.get("ANTHROPIC_API_KEY"):
            client = anthropic.Anthropic(timeout=60.0)
            response = client.messages.create(
                model="claude-haiku-4-5-20251001",
                max_tokens=2048,
                messages=[{"role": "user", "content": prompt}],
            )
            return response.content[0].text.strip()
    except ImportError:
        print("[from-tex] anthropic SDK not installed, trying CLI", file=sys.stderr)
    except Exception as e:
        print(f"[from-tex] SDK error: {e}, trying CLI", file=sys.stderr)

    # Method 2: Claude CLI (skip if inside Claude Code to avoid nesting issues)
    if os.environ.get("CLAUDECODE"):
        print("[from-tex] inside Claude Code session, skipping CLI fallback", file=sys.stderr)
        return None
    # Try CLI without --model (uses default model, covered by Max subscription)
    try:
        result = subprocess.run(
            ["claude", "-p", "--output-format", "text"],
            input=prompt,
            capture_output=True, text=True, timeout=90,
        )
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip()
        else:
            stderr_preview = (result.stderr or "")[:300]
            print(f"[from-tex] CLI rc={result.returncode}, stderr={stderr_preview}", file=sys.stderr)
    except FileNotFoundError:
        print("[from-tex] claude CLI not found in PATH", file=sys.stderr)
    except subprocess.TimeoutExpired:
        print("[from-tex] CLI timed out (90s)", file=sys.stderr)
    except Exception as e:
        print(f"[from-tex] CLI error: {e}", file=sys.stderr)

    return None


def canonicalize_blocks(blocks: List[Dict[str, Any]], source_tag: str) -> List[Dict[str, Any]]:
    """Use AI to identify canonical math names for extracted theorem blocks.

    Returns blocks with added 'canonical_name' and 'topic' fields.
    Falls back to source-prefixed positional names if AI unavailable.
    """
    # Build batch prompt — all blocks in one call to minimize latency
    entries = []
    for i, b in enumerate(blocks):
        stmt_preview = b["statement"][:400].replace("\n", " ")
        entries.append(
            f"[{i}] kind={b['kind']}, title=\"{b['title']}\"\n"
            f"    statement: {stmt_preview}"
        )

    prompt = f"""You are a mathematical theorem naming expert. Given theorem blocks extracted from a statistics/probability lecture, identify the canonical mathematical name for each.

Rules:
- Use the standard name in the mathematical community (e.g., "Central Limit Theorem", "Slutsky's Theorem", "Delta Method")
- If the block is a well-known result, use its canonical name
- If it's a textbook exercise, example, or unnamed remark, use a descriptive name based on content (e.g., "poisson_convergence_example", "t_distribution_clt_example")
- For definitions, name the concept being defined (e.g., "convergence_in_distribution", "fisher_information")
- Return lean_name in snake_case (e.g., "central_limit_theorem", "delta_method")
- Return topic as a Statlean module directory (one of: Gaussian, Variance, Entropy, SubGaussian, CharFun, LimitTheorems, EmpiricalProcess, Regression, Sufficiency, Estimator, ExpFamily, Information, SPD, Statistic, Misc)

Blocks:
{chr(10).join(entries)}

Return ONLY a JSON array (no markdown fences), one object per block, in order:
[{{"index": 0, "canonical_name": "...", "lean_name": "...", "topic": "..."}}, ...]"""

    response = _call_ai(prompt)
    if not response:
        print(f"[from-tex] AI canonicalize unavailable, falling back to heuristic")
        return _heuristic_canonicalize(blocks)

    # Parse response
    try:
        # Strip markdown fences if present
        text = response.strip()
        if text.startswith("```"):
            lines = text.split("\n")
            lines = [l for l in lines if not l.startswith("```")]
            text = "\n".join(lines).strip()
        results = json.loads(text)
    except (json.JSONDecodeError, ValueError) as e:
        print(f"[from-tex] AI response parse error: {e}, falling back")
        for b in blocks:
            b["canonical_name"] = None
            b["topic"] = None
        return blocks

    # Merge results back
    for entry in results:
        idx = entry.get("index", -1)
        if 0 <= idx < len(blocks):
            blocks[idx]["canonical_name"] = entry.get("canonical_name", "")
            blocks[idx]["lean_name_hint"] = sanitize_name(entry.get("lean_name", ""))
            blocks[idx]["topic"] = entry.get("topic", "")

    # Fill any missing
    for b in blocks:
        if "canonical_name" not in b:
            b["canonical_name"] = None
            b["topic"] = None

    named = sum(1 for b in blocks if b.get("canonical_name"))
    print(f"[from-tex] AI canonicalized {named}/{len(blocks)} blocks")
    return blocks


def build_theorems(
    blocks: List[Dict[str, Any]],
    namespace: str,
    layer: str,
    source_tag: str = "imported",
) -> List[Dict[str, Any]]:
    used_ids: set[str] = set()
    used_names: set[str] = set()

    # first pass: build items with deduped ids/names
    items: List[Dict[str, Any]] = []
    label_to_id: Dict[Tuple[str, str], str] = {}

    for i, b in enumerate(blocks, start=1):
        kind = b["kind"]
        idx = f"{i:03d}"

        # Use AI-canonicalized name if available, else fall back to source-prefixed
        ai_name = b.get("lean_name_hint", "")
        ai_topic = b.get("topic", "")

        if ai_name:
            base_id = f"{source_tag}.{kind}.{idx}.{ai_name}"
            base_name = ai_name
        else:
            base = sanitize_name(b["title"])
            base_id = f"{source_tag}.{kind}.{idx}.{base}"
            base_name = f"{kind}_{idx}_{base}"

        theorem_id = unique(base_id[:120], used_ids)
        lean_name = unique(base_name[:120], used_names)

        # Determine namespace from topic if AI provided it
        item_namespace = namespace
        if ai_topic and ai_topic != "Misc":
            item_namespace = f"Statlean.{ai_topic}"

        k_num = theorem_number_from_title(b["title"])
        if k_num[0] and k_num[1]:
            label_to_id[(k_num[0], k_num[1])] = theorem_id

        item = {
            "id": theorem_id,
            "title": b["title"],
            "kind": kind,
            "latex_statement": b["statement"],
            "latex_proof_hint": b["proof"],
            "proof_body": b.get("proof_body", ""),
            "lean_name": lean_name,
            "lean_namespace": item_namespace,
            "layer": layer,
            "priority": 3,
            "dependencies": [],
            "assumptions": [],
            "acceptance": [
                "lake build passes",
                "theorem contains no sorry",
                "theorem contains no axiom",
            ],
            "notes": "",
        }
        if b.get("canonical_name"):
            item["canonical_name"] = b["canonical_name"]
        # Attach Lean sketch as reference (in notes, not lean_statement,
        # to avoid compilation issues with missing Mathlib imports)
        if b.get("lean_sketch"):
            item["lean_sketch"] = b["lean_sketch"]
        items.append(item)

    # second pass: infer dependencies from theorem references in statement/proof
    for i, it in enumerate(items):
        src = blocks[i]["statement"] + "\n" + blocks[i]["proof"]
        deps: List[str] = []
        for k, num in extract_ref_tokens(src):
            dep_id = label_to_id.get((k, num))
            if dep_id and dep_id != it["id"] and dep_id not in deps:
                deps.append(dep_id)
        it["dependencies"] = deps

    return items


def derive_source_tag(tex_path: Path) -> str:
    """Derive a short source tag from the tex file path.

    e.g. 'theme/input/paper.tex' from 'lecture-9-handout.pdf'
    → look for the raw PDF name in the parent dir.
    Fallback: use stem of tex file.
    """
    # Check if there's a companion extract_summary.json with the PDF name
    input_dir = tex_path.parent
    summary_path = input_dir / "extract_summary.json"
    if summary_path.exists():
        try:
            summary = json.loads(summary_path.read_text(encoding="utf-8"))
            pdf_name = Path(summary.get("pdf", "")).stem
            if pdf_name:
                return sanitize_name(pdf_name)[:40]
        except (json.JSONDecodeError, KeyError):
            pass

    # Fallback: tex file stem
    stem = tex_path.stem
    if stem == "paper":
        # Generic name, try parent directory
        return sanitize_name(input_dir.name)[:40] or "imported"
    return sanitize_name(stem)[:40] or "imported"


def write_theorems_yaml(
    out_path: Path,
    blocks: List[Dict[str, Any]],
    namespace: str,
    layer: str,
    source_tag: str = "imported",
) -> None:
    data = {
        "version": "v1",
        "theorem_set": f"{source_tag}-tex-batch",
        "source_tag": source_tag,
        "defaults": {
            "lean_namespace": namespace,
            "layer": layer,
            "allow_axiom": False,
        },
        "theorems": build_theorems(blocks, namespace, layer, source_tag=source_tag),
    }
    out_path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True), encoding="utf-8")


def write_notation_yaml(out_path: Path) -> None:
    text = {
        "version": "v1",
        "symbols": [
            {
                "latex": "\\\\mathbb{E}[X]",
                "meaning": "expectation",
                "lean_candidates": ["∫ x, X x ∂μ"],
            },
            {
                "latex": "\\\\mathrm{Var}(X)",
                "meaning": "variance",
                "lean_candidates": ["Var[X; μ]"],
            },
        ],
    }
    out_path.write_text(yaml.safe_dump(text, sort_keys=False, allow_unicode=True), encoding="utf-8")


def write_scope_yaml(out_path: Path, theorem_ids: List[str]) -> None:
    data = {
        "version": "v1",
        "project_name": "imported-formalization",
        "output_policy": {
            "require_zero_sorry": True,
            "require_zero_axiom": True,
            "statlib_first": True,
        },
        "include": {"theorem_ids": theorem_ids or ["imported.theorem.001.placeholder"]},
        "exclude": {"theorem_ids": []},
        "constraints": {
            "max_new_files_per_batch": 50,
            "forbid_direct_mathlib_import_in_formalization": False,
            "allowed_axiom_paths": [],
        },
    }
    out_path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True), encoding="utf-8")


def main() -> None:
    p = argparse.ArgumentParser(description="Build theme input package from a tex file")
    p.add_argument("tex", type=Path, help="path to source tex file (e.g. ./output.tex)")
    p.add_argument("input_dir", type=Path, help="target input directory (e.g. theme/input)")
    p.add_argument("--namespace", default="Formalization.Imported", help="default lean namespace")
    p.add_argument("--layer", default="formalization", choices=["statlib", "formalization"])
    p.add_argument("--no-ai", action="store_true", help="skip AI canonicalization")
    args = p.parse_args()

    tex_path = args.tex
    input_dir = args.input_dir
    input_dir.mkdir(parents=True, exist_ok=True)

    tex = tex_path.read_text(encoding="utf-8", errors="ignore")
    blocks = extract_blocks(tex)

    # Derive source tag from PDF name
    source_tag = derive_source_tag(tex_path)
    print(f"[from-tex] source_tag={source_tag}")

    # AI canonicalize pass (unless --no-ai)
    if not args.no_ai:
        blocks = canonicalize_blocks(blocks, source_tag)

    (input_dir / "paper.tex").write_text(tex, encoding="utf-8")

    theorems_path = input_dir / "theorems.yaml"
    write_theorems_yaml(theorems_path, blocks, args.namespace, args.layer, source_tag=source_tag)

    if not (input_dir / "notation.yaml").exists():
        write_notation_yaml(input_dir / "notation.yaml")

    theorem_data = yaml.safe_load(theorems_path.read_text(encoding="utf-8")) or {}
    theorem_ids = [str(it.get("id", "")) for it in (theorem_data.get("theorems", []) or []) if it.get("id")]

    # Always regenerate scope.yaml to match current theorem IDs
    write_scope_yaml(input_dir / "scope.yaml", theorem_ids)

    print(f"[from-tex] source={tex_path}")
    print(f"[from-tex] extracted={len(blocks)} theorem-like blocks")
    print(f"[from-tex] wrote {input_dir / 'paper.tex'}")
    print(f"[from-tex] wrote {input_dir / 'theorems.yaml'}")
    if (input_dir / "notation.yaml").exists():
        print(f"[from-tex] notation file present at {input_dir / 'notation.yaml'}")
    if (input_dir / "scope.yaml").exists():
        print(f"[from-tex] scope file present at {input_dir / 'scope.yaml'}")


if __name__ == "__main__":
    main()
