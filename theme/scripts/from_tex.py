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
        print(f"[from-tex] AI canonicalize unavailable, using source-prefixed names")
        for i, b in enumerate(blocks):
            b["canonical_name"] = None
            b["topic"] = None
        return blocks

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
