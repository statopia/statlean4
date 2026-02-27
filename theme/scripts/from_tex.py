#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
from pathlib import Path
from typing import Any, Dict, List, Tuple

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


def build_theorems(blocks: List[Dict[str, Any]], namespace: str, layer: str) -> List[Dict[str, Any]]:
    used_ids: set[str] = set()
    used_names: set[str] = set()

    # first pass: build items with deduped ids/names
    items: List[Dict[str, Any]] = []
    label_to_id: Dict[Tuple[str, str], str] = {}

    for i, b in enumerate(blocks, start=1):
        kind = b["kind"]
        idx = f"{i:03d}"
        base = sanitize_name(b["title"])

        theorem_id = unique(f"imported.{kind}.{idx}.{base}"[:120], used_ids)
        lean_name = unique(f"{kind}_{idx}_{base}"[:120], used_names)

        k_num = theorem_number_from_title(b["title"])
        if k_num[0] and k_num[1]:
            label_to_id[(k_num[0], k_num[1])] = theorem_id

        item = {
            "id": theorem_id,
            "title": b["title"],
            "kind": kind,
            "latex_statement": b["statement"],
            "latex_proof_hint": b["proof"],
            "lean_name": lean_name,
            "lean_namespace": namespace,
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
        items.append(item)

    # second pass: infer dependencies from theorem references in statement/proof
    id_by_index = {i: it["id"] for i, it in enumerate(items)}
    for i, it in enumerate(items):
        src = blocks[i]["statement"] + "\n" + blocks[i]["proof"]
        deps: List[str] = []
        for k, num in extract_ref_tokens(src):
            dep_id = label_to_id.get((k, num))
            if dep_id and dep_id != it["id"] and dep_id not in deps:
                deps.append(dep_id)
        it["dependencies"] = deps

    return items


def write_theorems_yaml(out_path: Path, blocks: List[Dict[str, Any]], namespace: str, layer: str) -> None:
    data = {
        "version": "v1",
        "theorem_set": "imported-tex-batch",
        "defaults": {
            "lean_namespace": namespace,
            "layer": layer,
            "allow_axiom": False,
        },
        "theorems": build_theorems(blocks, namespace, layer),
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
    args = p.parse_args()

    tex_path = args.tex
    input_dir = args.input_dir
    input_dir.mkdir(parents=True, exist_ok=True)

    tex = tex_path.read_text(encoding="utf-8", errors="ignore")
    blocks = extract_blocks(tex)

    (input_dir / "paper.tex").write_text(tex, encoding="utf-8")

    theorems_path = input_dir / "theorems.yaml"
    write_theorems_yaml(theorems_path, blocks, args.namespace, args.layer)

    if not (input_dir / "notation.yaml").exists():
        write_notation_yaml(input_dir / "notation.yaml")

    theorem_data = yaml.safe_load(theorems_path.read_text(encoding="utf-8")) or {}
    theorem_ids = [str(it.get("id", "")) for it in (theorem_data.get("theorems", []) or []) if it.get("id")]

    if not (input_dir / "scope.yaml").exists():
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
