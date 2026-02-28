#!/usr/bin/env python3
"""Classify theorems into Statlean/ subdirectory and submodule.

Two-stage classification:
  1. If kind is definition/structure/class/abbrev → infra rules (routes to Basic.lean)
  2. Otherwise → theorem rules (routes to specific file)

Used by generate_project.py and sync_sorry_backlog.py to consistently map
theorem metadata to the Statlean/ file hierarchy.
"""
from __future__ import annotations

import re
from typing import Tuple

_INFRA_KINDS = {"definition", "structure", "class", "abbrev", "def"}

# Infrastructure rules: definitions route to <Topic>/Basic.lean
# (keywords, topic)
_INFRA_RULES: list[Tuple[list[str], str]] = [
    # Statistics foundations (completeness, sufficiency, ancillary are peer concepts)
    (["completeness", "complete statistic", "boundedly complete",
      "ancillary", "ancillarity",
      "sufficiency", "sufficient statistic", "minimal sufficient"], "Statistic"),
    # Exponential family
    (["exponential family", "natural parameter", "natural exponential"], "ExpFamily"),
    # Gaussian family
    (["gaussian", "stdgaussian", "normal distribution"], "Gaussian"),
    # Variance / moments
    (["variance", "condvar", "covariance", "moment"], "Variance"),
    # Entropy / information
    (["entropy", "kl divergence", "mutual information"], "Entropy"),
    # Sub-Gaussian
    (["subgaussian", "sub.gaussian"], "SubGaussian"),
    # Characteristic functions
    (["charfun", "characteristic function"], "CharFun"),
]

# Theorem rules: theorems/lemmas route to <Topic>/<Specific>.lean
# (keywords, subdir, submodule) — order matters, first match wins
_THEOREM_RULES: list[Tuple[list[str], str, str]] = [
    # Gaussian family
    (["poincar", "spectral gap", "coord_bound"], "Gaussian", "Poincare"),
    (["hermite", "hermitebasis"], "Gaussian", "Hermite"),
    (["stein identity", "stein_identity"], "Gaussian", "Stein"),
    (["gaussian", "stdgaussian", "normal distribution"], "Gaussian", "Basic"),
    # Variance
    (["rao.blackwell", "raoblackwell", "rao-blackwell", "mse"], "Variance", "RaoBlackwell"),
    (["efron.stein", "efronstein", "efron-stein", "jackknife"], "Variance", "EfronStein"),
    (["anova", "variance decomposition", "marginal_l2"], "Variance", "ANOVA"),
    # Entropy / Log-Sobolev
    (["log.sobolev", "logsobolev", "log-sobolev", "lsi", "gross", "hypercontract"], "Entropy", "LogSobolev"),
    (["entropy", "kl divergence", "condentropy"], "Entropy", "Basic"),
    # Sub-Gaussian / Concentration
    (["herbst", "subgaussian.*mgf", "subgaussian.*lipschitz"], "SubGaussian", "Herbst"),
    (["lipschitz.*concentration", "concentration.*inequality"], "SubGaussian", "Lipschitz"),
    (["subgaussian"], "SubGaussian", "Herbst"),
    # Characteristic functions
    (["charfun", "characteristic function", "fourier.*transform"], "CharFun", "Taylor"),
    # Limit theorems
    (["berry.esseen", "berryesseen", "berry-esseen", "normal approximation"], "LimitTheorems", "BerryEsseen"),
    (["slln", "strong law", "uniform.*law.*large"], "LimitTheorems", "USLLN"),
    (["clt", "central limit"], "LimitTheorems", "CLT"),
    # Empirical process
    (["covering number", "bracketing", "metric entropy"], "EmpiricalProcess", "CoveringNumber"),
    (["dudley", "chaining"], "EmpiricalProcess", "Dudley"),
    # Regression
    (["least.squares", "regression", "oracle inequality"], "Regression", "Basic"),
    (["master bound"], "Regression", "MasterBound"),
    (["linear regression", "linear model"], "Regression", "Linear"),
    # Sufficiency theorems (distinct from the definitions in Statistic/Basic)
    (["factorization", "fisher.neyman"], "Sufficiency", "Factorization"),
    (["basu"], "Sufficiency", "Basu"),
    (["lehmann.scheff", "umvue"], "Sufficiency", "LehmannScheffe"),
    (["completeness.*exponential", "complete.*sufficient"], "Sufficiency", "Completeness"),
    # SPD matrices
    (["frechet mean", "fr.chet mean", "log.cholesky"], "SPD", "FrechetMean"),
    (["determinant.*spd", "spd.*determinant"], "SPD", "Determinant"),
    (["geodesic.*spd", "spd.*geodesic"], "SPD", "Geodesic"),
]


def classify_theorem(
    title: str = "",
    namespace: str = "",
    statement: str = "",
    kind: str = "theorem",
) -> Tuple[str, str]:
    """Return (subdir, submodule) for a theorem or definition.

    >>> classify_theorem(title="Completeness of a Statistic", kind="definition")
    ('Statistic', 'Basic')
    >>> classify_theorem(title="Poincaré inequality for Gaussian measure")
    ('Gaussian', 'Poincare')
    >>> classify_theorem(namespace="ProbabilityTheory.Variance.EfronStein")
    ('Variance', 'EfronStein')
    >>> classify_theorem(title="Basu's Theorem", kind="theorem")
    ('Sufficiency', 'Basu')
    >>> classify_theorem(title="Some unknown thing")
    ('Misc', 'Pipeline')
    """
    blob = f"{title} {namespace} {statement}".lower()
    is_infra = kind.lower().strip() in _INFRA_KINDS

    # Try namespace-based shortcut: "Statlean.Gaussian.Poincare" → ("Gaussian", "Poincare")
    ns_match = re.search(r"statlean\.(\w+)\.(\w+)", namespace, re.IGNORECASE)
    if ns_match:
        subdir, submodule = ns_match.group(1), ns_match.group(2)
        # For infra, override submodule to Basic
        if is_infra:
            return subdir, "Basic"
        return subdir, submodule

    # Stage 1: if infra kind, try infra rules first
    if is_infra:
        for keywords, topic in _INFRA_RULES:
            for kw in keywords:
                if re.search(kw, blob, re.IGNORECASE):
                    return topic, "Basic"

    # Stage 2: theorem rules
    for keywords, subdir, submodule in _THEOREM_RULES:
        for kw in keywords:
            if re.search(kw, blob, re.IGNORECASE):
                # If infra kind matched a theorem rule, redirect to Basic
                if is_infra:
                    return subdir, "Basic"
                return subdir, submodule

    # Fallback: infra → Misc/Basic, theorem → Misc/Pipeline
    if is_infra:
        return "Misc", "Basic"
    return "Misc", "Pipeline"


def lean_module_path(subdir: str, submodule: str) -> str:
    """Return the dotted Lean module path.

    >>> lean_module_path("Gaussian", "Poincare")
    'Statlean.Gaussian.Poincare'
    """
    return f"Statlean.{subdir}.{submodule}"


def file_path(subdir: str, submodule: str) -> str:
    """Return the filesystem path relative to repo root.

    >>> file_path("Gaussian", "Poincare")
    'Statlean/Gaussian/Poincare.lean'
    """
    return f"Statlean/{subdir}/{submodule}.lean"


if __name__ == "__main__":
    import doctest
    doctest.testmod(verbose=True)
