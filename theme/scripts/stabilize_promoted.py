#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Tuple


def module_name_from_path(module_path: Path, repo_root: Path) -> str:
    rel = module_path.resolve().relative_to(repo_root.resolve())
    if rel.suffix != ".lean":
        raise ValueError(f"not a lean file: {module_path}")
    return ".".join(rel.with_suffix("").parts)


def extract_entries(source_text: str) -> List[Dict[str, str]]:
    lines = source_text.splitlines(keepends=True)
    n = len(lines)
    i = 0
    out: List[Dict[str, str]] = []
    current_section = ""

    def starts_id_block(idx: int) -> bool:
        return idx + 1 < n and lines[idx].strip() == "/-" and lines[idx + 1].startswith("ID: ")

    def boundary(idx: int) -> bool:
        if idx >= n:
            return True
        s = lines[idx].strip()
        if starts_id_block(idx):
            return True
        if s.startswith("section "):
            return True
        if s in {"end AutoPromoted", "end Statlean"}:
            return True
        if current_section and s == f"end {current_section}":
            return True
        return False

    while i < n:
        s = lines[i].strip()
        if s.startswith("section "):
            current_section = s[len("section ") :].strip()
            i += 1
            continue
        if current_section and s == f"end {current_section}":
            current_section = ""
            i += 1
            continue
        if not starts_id_block(i):
            i += 1
            continue

        start = i
        theorem_id = lines[i + 1][len("ID: ") :].strip()

        j = i + 2
        while j < n and lines[j].strip() != "-/":
            j += 1
        if j >= n:
            break

        k = j + 1
        while k < n and lines[k].strip() == "":
            k += 1
        if k >= n or not lines[k].lstrip().startswith("theorem "):
            i = k
            continue

        theorem_line = lines[k].strip()
        theorem_name = theorem_line[len("theorem ") :].split(" ", 1)[0]
        theorem_name = theorem_name.split(":", 1)[0].strip()
        if theorem_name.endswith(":"):
            theorem_name = theorem_name[:-1]

        l = k + 1
        while l < n and not boundary(l):
            l += 1
        chunk = "".join(lines[start:l]).rstrip() + "\n\n"
        chunk_hash = hashlib.sha256(chunk.encode("utf-8")).hexdigest()
        out.append(
            {
                "id": theorem_id,
                "name": theorem_name,
                "section": current_section,
                "chunk": chunk,
                "hash": chunk_hash,
            }
        )
        i = l
    return out


def contains_any(text: str, keywords: List[str]) -> bool:
    return any(k in text for k in keywords)


def classify_target_module(entry: Dict[str, str], stats_only: bool) -> Tuple[str, str, bool]:
    text = f"{entry['section']}\n{entry['id']}\n{entry['chunk']}".lower()
    # ── Route by mathematical object (v10 architecture) ──
    reg_kw = ["regression", "risk", "estimator", "least-squares", "least squares"]
    emp_kw = ["empirical process", "covering number", "dudley", "entropy"]
    gauss_kw = ["gaussian", "poincare", "poincaré", "stein identity", "hermite", "sobolev"]
    var_kw = ["variance", "efron-stein", "efron stein", "rao-blackwell", "rao blackwell"]
    ent_kw = ["entropy", "log-sobolev", "log sobolev", "lsi"]
    subg_kw = ["sub-gaussian", "subgaussian", "herbst", "lipschitz concentration"]
    charfun_kw = ["characteristic function", "charfun", "fourier", "berry", "esseen", "clt", "central limit"]
    spd_kw = ["fréchet", "frechet", "spd", "log-cholesky", "determinant", "logdet", "geodesic"]

    if contains_any(text, reg_kw):
        return "Statlean/Regression/AutoStable.lean", "Regression", True
    if contains_any(text, emp_kw):
        return "Statlean/EmpiricalProcess/AutoStable.lean", "EmpiricalProcess", True
    if contains_any(text, var_kw):
        return "Statlean/Variance/AutoStable.lean", "Variance", True
    if contains_any(text, ent_kw):
        return "Statlean/Entropy/AutoStable.lean", "Entropy", True
    if contains_any(text, subg_kw):
        return "Statlean/SubGaussian/AutoStable.lean", "SubGaussian", True
    if contains_any(text, charfun_kw):
        return "Statlean/CharFun/AutoStable.lean", "CharFun", True
    if contains_any(text, gauss_kw):
        return "Statlean/Gaussian/AutoStable.lean", "Gaussian", True
    if contains_any(text, spd_kw):
        return "Statlean/SPD/AutoStable.lean", "SPD", True
    if stats_only:
        return "", "skip_non_statistical_general", False
    return "Statlean/Support/AutoStable.lean", "SupportGeneral", False


def theorem_names_in_file(path: Path) -> set[str]:
    if not path.exists():
        return set()
    text = path.read_text(encoding="utf-8")
    return set(re.findall(r"(?m)^\s*theorem\s+([A-Za-z0-9_']+)\b", text))


def theorem_names_in_repo_statlean(repo_root: Path, exclude_files: List[Path]) -> set[str]:
    out: set[str] = set()
    statlean_dir = repo_root / "Statlean"
    if not statlean_dir.exists():
        return out
    excludes = {p.resolve() for p in exclude_files if p}
    for fp in statlean_dir.rglob("*.lean"):
        if fp.resolve() in excludes:
            continue
        out |= theorem_names_in_file(fp)
    return out


def exists_name_in_mathlib(mathlib_root: Path, name: str, use_mathlib_check: bool) -> bool:
    if not use_mathlib_check or not mathlib_root.exists():
        return False
    if not re.fullmatch(r"[A-Za-z0-9_']+", name):
        return False

    pattern = rf"^\s*(theorem|lemma|def|abbrev|instance)\s+{re.escape(name)}\b"
    try:
        rg = subprocess.run(
            ["rg", "-n", "-m", "1", "-g", "*.lean", pattern, str(mathlib_root)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        return rg.returncode == 0
    except FileNotFoundError:
        gp = subprocess.run(
            ["grep", "-RInm1", "-E", pattern, str(mathlib_root)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        return gp.returncode == 0


def parse_existing_auto_module_entries(path: Path) -> Dict[str, str]:
    if not path.exists():
        return {}
    entries = extract_entries(path.read_text(encoding="utf-8"))
    return {e["name"]: e["chunk"] for e in entries if e.get("name")}


def render_auto_module(module_name: str, chunks: List[str]) -> str:
    header = (
        "import Mathlib\n\n"
        "/-! Auto-generated by theme/scripts/stabilize_promoted.py.\n"
        "This file stores stabilized statistical declarations.\n"
        "Do not edit manually; rerun the stabilization pipeline.\n"
        "-/\n\n"
        f"namespace {module_name}\n\n"
    )
    if chunks:
        body = "".join(chunks)
    else:
        body = "-- no stabilized declarations\n\n"
    footer = f"end {module_name}\n"
    return header + body + footer


def ensure_root_import(statlean_root: Path, import_line: str) -> bool:
    lines = statlean_root.read_text(encoding="utf-8").splitlines()
    if import_line in lines:
        return False
    insert_at = -1
    for i, ln in enumerate(lines):
        if ln.startswith("import "):
            insert_at = i
    if insert_at >= 0:
        lines.insert(insert_at + 1, import_line)
    else:
        lines.insert(0, import_line)
    statlean_root.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return True


def main() -> None:
    ap = argparse.ArgumentParser(description="Stabilize auto-promoted declarations into formal Statlean modules")
    ap.add_argument("--repo-root", required=True)
    ap.add_argument("--autopromoted", required=True)
    ap.add_argument("--state-json", required=True)
    ap.add_argument("--summary-json", required=True)
    ap.add_argument("--min-stable-runs", type=int, default=2)
    ap.add_argument("--stats-only", type=int, default=1)
    ap.add_argument("--mathlib-check", type=int, default=1)
    args = ap.parse_args()

    repo_root = Path(args.repo_root).resolve()
    autopromoted = Path(args.autopromoted).resolve()
    state_json = Path(args.state_json).resolve()
    summary_json = Path(args.summary_json).resolve()
    statlean_root = (repo_root / "Statlean.lean").resolve()
    mathlib_root = (repo_root / ".lake" / "packages" / "mathlib" / "Mathlib").resolve()
    stats_only = args.stats_only == 1
    use_mathlib_check = args.mathlib_check == 1
    min_stable_runs = max(1, int(args.min_stable_runs))

    entries = extract_entries(autopromoted.read_text(encoding="utf-8")) if autopromoted.exists() else []

    state = {"theorems": {}}
    if state_json.exists():
        state = json.loads(state_json.read_text(encoding="utf-8"))
        if "theorems" not in state or not isinstance(state["theorems"], dict):
            state = {"theorems": {}}

    theorem_state: Dict[str, Dict[str, object]] = state["theorems"]
    for e in entries:
        name = e["name"]
        prev = theorem_state.get(name, {})
        if prev.get("hash") == e["hash"]:
            stable_runs = int(prev.get("stable_runs", 0)) + 1
        else:
            stable_runs = 1
        theorem_state[name] = {
            "hash": e["hash"],
            "stable_runs": stable_runs,
            "id": e["id"],
            "section": e["section"],
        }

    candidates = [e for e in entries if int(theorem_state.get(e["name"], {}).get("stable_runs", 0)) >= min_stable_runs]

    existing_repo_names = theorem_names_in_repo_statlean(repo_root, exclude_files=[autopromoted])
    mathlib_cache: Dict[str, bool] = {}

    migrated: List[Dict[str, str]] = []
    skipped: List[Dict[str, str]] = []
    by_module_new_chunks: Dict[Path, Dict[str, str]] = defaultdict(dict)

    for e in candidates:
        module_rel, group_label, is_stat = classify_target_module(e, stats_only=stats_only)
        if not module_rel:
            skipped.append({"name": e["name"], "id": e["id"], "reason": group_label})
            continue

        if e["name"] in existing_repo_names:
            skipped.append({"name": e["name"], "id": e["id"], "reason": "already_in_statlean"})
            continue

        if e["name"] not in mathlib_cache:
            mathlib_cache[e["name"]] = exists_name_in_mathlib(mathlib_root, e["name"], use_mathlib_check)
        if mathlib_cache[e["name"]]:
            skipped.append({"name": e["name"], "id": e["id"], "reason": "name_exists_in_mathlib"})
            continue

        target_path = (repo_root / module_rel).resolve()
        by_module_new_chunks[target_path][e["name"]] = e["chunk"]
        migrated.append(
            {
                "name": e["name"],
                "id": e["id"],
                "module": str(target_path),
                "group": group_label,
                "is_statistical": str(is_stat),
            }
        )

    written_modules: List[str] = []
    root_imports_added: List[str] = []
    for module_path, additions in by_module_new_chunks.items():
        module_path.parent.mkdir(parents=True, exist_ok=True)
        existing_chunks = parse_existing_auto_module_entries(module_path)
        existing_chunks.update(additions)
        sorted_chunks = [existing_chunks[k] for k in sorted(existing_chunks.keys())]
        module_name = module_name_from_path(module_path, repo_root)
        module_text = render_auto_module(module_name, sorted_chunks)
        module_path.write_text(module_text, encoding="utf-8")
        written_modules.append(str(module_path))

        import_line = f"import {module_name}"
        if ensure_root_import(statlean_root, import_line):
            root_imports_added.append(import_line)

    state_json.parent.mkdir(parents=True, exist_ok=True)
    state_json.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    summary = {
        "repo_root": str(repo_root),
        "autopromoted": str(autopromoted),
        "min_stable_runs": min_stable_runs,
        "stats_only": stats_only,
        "mathlib_check": use_mathlib_check,
        "entries_seen": len(entries),
        "candidates_after_stability": len(candidates),
        "migrated_count": len(migrated),
        "migrated": migrated,
        "skipped": skipped,
        "written_modules": written_modules,
        "root_imports_added": root_imports_added,
        "state_json": str(state_json),
    }
    summary_json.parent.mkdir(parents=True, exist_ok=True)
    summary_json.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, ensure_ascii=False))


if __name__ == "__main__":
    main()
