#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Set

import yaml

# Statistics-related keywords for auto-promotion filtering.
STATS_KEYWORDS = [
    "probability", "expectation", "variance", "covariance", "moment",
    "distribution", "gaussian", "normal", "poisson", "bernoulli", "binomial",
    "cdf", "pdf", "density", "measure", "random", "sample", "iid",
    "estimator", "estimate", "bias", "mse", "risk", "loss",
    "regression", "least-squares", "least squares",
    "concentration", "bound", "inequality", "tail",
    "berry", "esseen", "clt", "central limit",
    "poincare", "log-sobolev", "efron-stein", "stein",
    "entropy", "mutual information", "kl divergence",
    "empirical", "covering number", "dudley",
    "frechet", "fréchet", "mean", "average",
    "convergence", "rate", "consistency",
    "hypothesis", "test", "confidence",
    "bayes", "posterior", "prior", "likelihood",
    "markov", "martingale", "ergodic",
    "hermite", "orthogonal", "fourier",
    "integrable", "integrability", "lp", "l2", "l1",
    "conditional", "condexp", "independence",
]


def _text_blob(it: Dict[str, Any]) -> str:
    """Collect all textual fields from a theorem entry for keyword matching."""
    parts = []
    for key in ("id", "title", "kind", "latex_statement", "notes", "lean_statement"):
        v = it.get(key)
        if v:
            parts.append(str(v))
    return " ".join(parts).lower()


def _is_stats_related(it: Dict[str, Any]) -> bool:
    """Check if a theorem entry is statistics-related by keyword matching."""
    blob = _text_blob(it)
    return any(kw in blob for kw in STATS_KEYWORDS)


def _existing_theorem_names(repo_root: str) -> Set[str]:
    """Collect theorem/def names already in Statlean/ to avoid duplicates."""
    names: Set[str] = set()
    statlean_dir = Path(repo_root) / "Statlean"
    if not statlean_dir.is_dir():
        return names
    pat = re.compile(r"^\s*(?:theorem|def|lemma|noncomputable\s+def)\s+([A-Za-z0-9_']+)")
    for f in statlean_dir.rglob("*.lean"):
        for line in f.read_text(encoding="utf-8", errors="replace").splitlines():
            m = pat.match(line)
            if m:
                names.add(m.group(1))
    return names


def _mathlib_has_name(name: str, repo_root: str) -> bool:
    """Quick check if a name exists in local Mathlib source."""
    mathlib_dir = Path(repo_root) / ".lake" / "packages" / "mathlib" / "Mathlib"
    if not mathlib_dir.is_dir():
        return False
    try:
        result = subprocess.run(
            ["rg", "-l", f"\\b{re.escape(name)}\\b", str(mathlib_dir)],
            capture_output=True, text=True, timeout=10,
        )
        return result.returncode == 0 and bool(result.stdout.strip())
    except Exception:
        return False


def main() -> None:
    ap = argparse.ArgumentParser(description="Promote formalization theorems to statlib")
    ap.add_argument("--in-yaml", required=True)
    ap.add_argument("--out-yaml", required=True)
    ap.add_argument("--report-json", required=True)
    ap.add_argument("--min-fanin", type=int, default=2)
    ap.add_argument("--promote-all-novel", action="store_true",
                    help="Promote any novel stats-related theorem regardless of fanin")
    ap.add_argument("--repo-root", default=".")
    args = ap.parse_args()

    in_path = Path(args.in_yaml)
    out_path = Path(args.out_yaml)
    report_path = Path(args.report_json)

    data = yaml.safe_load(in_path.read_text(encoding="utf-8")) or {}
    items: List[Dict[str, Any]] = list(data.get("theorems", []) or [])

    id_to_item = {str(it.get("id", "")): it for it in items}
    fanin: Dict[str, int] = {k: 0 for k in id_to_item.keys()}
    for it in items:
      deps = it.get("dependencies", []) or []
      for d in deps:
        ds = str(d)
        if ds in fanin:
          fanin[ds] += 1

    # Pre-compute deduplication sets when promote-all-novel is active.
    existing_names: Set[str] = set()
    if args.promote_all_novel:
        existing_names = _existing_theorem_names(args.repo_root)

    promoted: List[Dict[str, Any]] = []
    for it in items:
      tid = str(it.get("id", ""))
      layer = str(it.get("layer", "formalization")).strip().lower()
      if layer != "formalization":
        continue

      # --- Promotion decision ---
      reason = ""
      if fanin.get(tid, 0) >= args.min_fanin:
          reason = f"fanin={fanin.get(tid, 0)}"
      elif args.promote_all_novel:
          # New path: promote if (a) stats-related, (b) not in Statlib, (c) not in Mathlib
          if not _is_stats_related(it):
              continue
          # Extract a likely theorem name from the ID
          name_parts = tid.rsplit(".", 1)
          likely_name = name_parts[-1] if name_parts else tid
          if likely_name in existing_names:
              continue
          if _mathlib_has_name(likely_name, args.repo_root):
              continue
          reason = "novel-stats"
      else:
          continue

      old = layer
      it["layer"] = "statlib"
      notes = str(it.get("notes", "")).strip()
      extra = f"auto-promoted by {reason}"
      it["notes"] = (notes + " | " + extra).strip(" |")
      promoted.append({
        "id": tid,
        "old_layer": old,
        "new_layer": "statlib",
        "fanin": fanin.get(tid, 0),
        "reason": reason,
      })

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True), encoding="utf-8")

    report = {
      "input": str(in_path),
      "output": str(out_path),
      "min_fanin": args.min_fanin,
      "total_theorems": len(items),
      "promoted_count": len(promoted),
      "promoted": promoted,
      "fanin": fanin,
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    print(json.dumps({"promoted_count": len(promoted), "report": str(report_path)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
