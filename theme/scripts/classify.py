#!/usr/bin/env python3
"""Classify theorems into Statlean/ subdirectory and submodule.

Used by generate_project.py and sync_sorry_backlog.py to consistently map
theorem metadata (title, namespace, statement keywords) to the Statlean/
file hierarchy.
"""
from __future__ import annotations

import re
from typing import Tuple

# (subdir, submodule) pairs that mirror Statlean/ layout.
# Order matters: first match wins.
_RULES: list[Tuple[list[str], str, str]] = [
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
    # SPD matrices
    (["frechet mean", "fr.chet mean", "log.cholesky"], "SPD", "FrechetMean"),
    (["determinant.*spd", "spd.*determinant"], "SPD", "Determinant"),
    (["geodesic.*spd", "spd.*geodesic"], "SPD", "Geodesic"),
]


def classify_theorem(
    title: str = "",
    namespace: str = "",
    statement: str = "",
) -> Tuple[str, str]:
    """Return (subdir, submodule) for a theorem.

    >>> classify_theorem(title="Poincaré inequality for Gaussian measure")
    ('Gaussian', 'Poincare')
    >>> classify_theorem(namespace="ProbabilityTheory.Variance.EfronStein")
    ('Variance', 'EfronStein')
    >>> classify_theorem(title="Some unknown thing")
    ('Misc', 'Pipeline')
    """
    blob = f"{title} {namespace} {statement}".lower()

    # Try namespace-based shortcut first: "Statlean.Gaussian.Poincare" → ("Gaussian", "Poincare")
    ns_match = re.search(r"statlean\.(\w+)\.(\w+)", namespace, re.IGNORECASE)
    if ns_match:
        return ns_match.group(1), ns_match.group(2)

    for keywords, subdir, submodule in _RULES:
        for kw in keywords:
            if re.search(kw, blob, re.IGNORECASE):
                return subdir, submodule

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
