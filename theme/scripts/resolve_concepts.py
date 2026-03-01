#!/usr/bin/env python3
"""Resolve user-supplied concept names to ontology entries, expand dependencies,
and generate theorems.yaml for the formalization pipeline.

Usage:
    python3 resolve_concepts.py \\
        --concepts "cramer_rao, Fisher Information" \\
        --output theme/input/theorems.yaml \\
        [--pdf lecture.pdf] \\
        [--no-deps]

Concept matching priority:
  1. Exact id match (e.g. "cramer_rao")
  2. Fuzzy name/keyword match (longest keyword overlap wins)
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional

import yaml

# ---------------------------------------------------------------------------
# Import shared helpers from sibling scripts
# ---------------------------------------------------------------------------
_SCRIPT_DIR = Path(__file__).resolve().parent

sys.path.insert(0, str(_SCRIPT_DIR))
from classify import load_ontology  # noqa: E402


# ---------------------------------------------------------------------------
# Concept resolution
# ---------------------------------------------------------------------------

def _normalize(s: str) -> str:
    """Lowercase, collapse whitespace, strip accents for matching."""
    s = s.strip().lower()
    # Basic accent normalization (Cramér → cramer, Poincaré → poincare)
    s = s.replace("\u00e9", "e").replace("\u00e8", "e")
    s = s.replace("\u00f6", "o").replace("\u00fc", "u")
    s = re.sub(r"[''`]", "", s)
    s = re.sub(r"[-–—]", "_", s)
    s = re.sub(r"\s+", " ", s)
    return s


def _keyword_score(query: str, concept: dict) -> float:
    """Score a concept against a query string using keyword overlap.

    Reuses the same length-weighted dedup logic as classify.py.
    """
    q = _normalize(query)
    all_kws: list[str] = [_normalize(k) for k in concept.get("keywords", [])]
    all_kws.append(_normalize(concept.get("name", "")))
    all_kws.append(_normalize(concept.get("id", "")))

    matched: list[str] = []
    for kw in all_kws:
        if not kw:
            continue
        if kw in q:
            if any(kw in m for m in matched):
                continue
            matched = [m for m in matched if m not in kw]
            matched.append(kw)

    return sum(len(m) for m in matched)


def resolve_concept(name_or_id: str, concepts: list[dict]) -> Optional[dict]:
    """Resolve a user string to an ontology concept.

    Priority: exact id match > fuzzy name/keyword match.

    >>> cs = load_ontology()
    >>> c = resolve_concept("cramer_rao", cs)
    >>> c is not None and "cramer" in c["id"]
    True
    >>> resolve_concept("nonexistent_xyz_123", cs) is None
    True
    """
    norm = _normalize(name_or_id)

    # 1. Exact id match
    for c in concepts:
        if _normalize(c["id"]) == norm:
            return c

    # 2. Exact id match after stripping _theorem/_def suffix
    for suffix in ("_theorem", "_def", "_definition", "_lemma"):
        for c in concepts:
            if _normalize(c["id"]) == norm + suffix:
                return c
            if _normalize(c["id"]).rstrip(suffix) == norm:
                return c

    # 3. Fuzzy match by name/keywords (require minimum score)
    best: Optional[dict] = None
    best_score = 0.0
    for c in concepts:
        score = _keyword_score(name_or_id, c)
        if score > best_score:
            best_score = score
            best = c

    # Require at least 4 chars matched to avoid false positives
    if best and best_score >= 4:
        return best

    return None


# ---------------------------------------------------------------------------
# Dependency expansion
# ---------------------------------------------------------------------------

def expand_deps(root_ids: list[str], concepts: list[dict], no_deps: bool = False) -> list[str]:
    """Recursively expand `requires` deps. Filter out lean_topic=null (Mathlib).

    Returns list of concept IDs that need Statlean entries.

    >>> cs = load_ontology()
    >>> ids = expand_deps(["basu_theorem"], cs)
    >>> "basu_theorem" in ids
    True
    """
    if no_deps:
        return [cid for cid in root_ids]

    id_map = {c["id"]: c for c in concepts}
    result_set: set[str] = set()
    stack = list(root_ids)

    while stack:
        cid = stack.pop()
        if cid in result_set:
            continue
        result_set.add(cid)
        concept = id_map.get(cid)
        if not concept:
            continue
        for dep in concept.get("requires", []):
            if dep not in result_set:
                stack.append(dep)

    # Filter: only keep concepts that have lean_topic (need Statlean entry)
    filtered = []
    for cid in result_set:
        c = id_map.get(cid)
        if c and c.get("lean_topic"):
            filtered.append(cid)

    return filtered


# ---------------------------------------------------------------------------
# Topological sort
# ---------------------------------------------------------------------------

def topo_sort(ids: list[str], concepts: list[dict]) -> list[str]:
    """Topological sort: dependencies before dependents.

    >>> cs = load_ontology()
    >>> sorted_ids = topo_sort(["basu_theorem", "sufficient"], cs)
    >>> sorted_ids.index("sufficient") < sorted_ids.index("basu_theorem") or "sufficient" not in sorted_ids
    True
    """
    id_map = {c["id"]: c for c in concepts}
    id_set = set(ids)

    # Build adjacency: concept -> [deps that are in id_set]
    graph: dict[str, list[str]] = {cid: [] for cid in ids}
    for cid in ids:
        c = id_map.get(cid)
        if not c:
            continue
        for dep in c.get("requires", []):
            if dep in id_set:
                graph[cid].append(dep)

    # Kahn's algorithm
    in_degree: dict[str, int] = {cid: 0 for cid in ids}
    for cid, deps in graph.items():
        for dep in deps:
            in_degree[dep] = in_degree.get(dep, 0)
            in_degree[cid] = in_degree.get(cid, 0)

    # Count incoming edges
    in_deg: dict[str, int] = defaultdict(int)
    reverse: dict[str, list[str]] = defaultdict(list)
    for cid, deps in graph.items():
        for dep in deps:
            reverse[dep].append(cid)
            in_deg[cid] += 1
        if cid not in in_deg:
            in_deg[cid] = 0

    queue = sorted([cid for cid in ids if in_deg[cid] == 0])
    result: list[str] = []
    while queue:
        node = queue.pop(0)
        result.append(node)
        for dependent in sorted(reverse.get(node, [])):
            in_deg[dependent] -= 1
            if in_deg[dependent] == 0:
                queue.append(dependent)

    # Append any remaining (cycles) at the end
    for cid in ids:
        if cid not in result:
            result.append(cid)

    return result


# ---------------------------------------------------------------------------
# PDF matching (optional)
# ---------------------------------------------------------------------------

def match_pdf_blocks(
    resolved: list[dict], pdf_path: Path
) -> dict[str, dict]:
    """Extract LaTeX blocks from PDF and match them to ontology concepts.

    Returns {concept_id: {"latex_statement": ..., "latex_proof_hint": ...}}.
    """
    if not pdf_path or not pdf_path.is_file():
        return {}

    try:
        # Step 1: Extract PDF to markdown via pdf_extract.py
        with tempfile.TemporaryDirectory(prefix="resolve_") as tmpdir:
            tmp = Path(tmpdir)
            result = subprocess.run(
                [
                    sys.executable,
                    str(_SCRIPT_DIR / "pdf_extract.py"),
                    "--pdf", str(pdf_path),
                    "--output-dir", str(tmp),
                ],
                capture_output=True,
                text=True,
                timeout=300,
            )

            # Find the output tex file
            tex_files = list(tmp.glob("*.tex"))
            if not tex_files:
                # Try markdown files and convert
                md_files = list(tmp.glob("*.md"))
                if not md_files:
                    print(f"[resolve] warning: no output from pdf_extract for {pdf_path}")
                    return {}

                # Use extract_theorem_blocks from pdf_extract
                md_text = md_files[0].read_text(encoding="utf-8", errors="ignore")
                from pdf_extract import extract_theorem_blocks, blocks_to_latex
                blocks = extract_theorem_blocks(md_text)
                if not blocks:
                    return {}
                tex_content = blocks_to_latex(blocks, pdf_path.name, "pymupdf")
            else:
                tex_content = tex_files[0].read_text(encoding="utf-8", errors="ignore")

            # Step 2: Parse LaTeX blocks via from_tex.py
            from from_tex import extract_blocks
            tex_blocks = extract_blocks(tex_content)

            if not tex_blocks:
                # If LaTeX parsing fails, try theorem blocks directly
                if not tex_files and md_files:
                    return _match_md_blocks(resolved, blocks)
                return {}

            # Step 3: Match each block to the best concept by keyword scoring
            return _match_tex_blocks(resolved, tex_blocks)

    except Exception as e:
        print(f"[resolve] warning: PDF processing failed: {e}")
        return {}


def _match_tex_blocks(
    resolved: list[dict],
    tex_blocks: list[dict],
) -> dict[str, dict]:
    """Match parsed LaTeX blocks to resolved concepts by keyword scoring."""
    matches: dict[str, dict] = {}
    used_blocks: set[int] = set()

    for concept in resolved:
        best_idx = -1
        best_score = 0.0
        for i, block in enumerate(tex_blocks):
            if i in used_blocks:
                continue
            blob = f"{block.get('title', '')} {block.get('statement', '')}".lower()
            score = _keyword_score(blob, concept)
            if score > best_score:
                best_score = score
                best_idx = i

        if best_idx >= 0 and best_score >= 4:
            block = tex_blocks[best_idx]
            used_blocks.add(best_idx)
            matches[concept["id"]] = {
                "latex_statement": block.get("statement", ""),
                "latex_proof_hint": block.get("proof", ""),
            }

    return matches


def _match_md_blocks(
    resolved: list[dict],
    md_blocks: list[dict],
) -> dict[str, dict]:
    """Match PDF-extracted markdown blocks to concepts."""
    matches: dict[str, dict] = {}
    used_blocks: set[int] = set()

    for concept in resolved:
        best_idx = -1
        best_score = 0.0
        for i, block in enumerate(md_blocks):
            if i in used_blocks:
                continue
            blob = f"{block.get('name', '')} {block.get('statement', '')}".lower()
            score = _keyword_score(blob, concept)
            if score > best_score:
                best_score = score
                best_idx = i

        if best_idx >= 0 and best_score >= 4:
            block = md_blocks[best_idx]
            used_blocks.add(best_idx)
            matches[concept["id"]] = {
                "latex_statement": block.get("statement", ""),
                "latex_proof_hint": block.get("proof_hint", ""),
            }

    return matches


# ---------------------------------------------------------------------------
# Claude sketch generation (fallback when ontology has no lean_sketch)
# ---------------------------------------------------------------------------

def call_claude_sketch(concept: dict) -> str:
    """Generate a Lean 4 skeleton for a concept using Claude API.

    Tries Anthropic SDK first, falls back to Claude CLI.
    Returns Lean 4 code string, or "" on failure.
    """
    cid = concept.get("id", "unknown")
    name = concept.get("name", cid)
    kind = concept.get("kind", "definition")
    keywords = concept.get("keywords", [])
    mathlib = concept.get("mathlib", "")
    requires = concept.get("requires", [])

    prompt = (
        f"Generate a Lean 4 {kind} skeleton for \"{name}\".\n"
        f"Context: {', '.join(keywords)}. "
        f"Mathlib: {mathlib or 'not in Mathlib'}.\n"
        f"Dependencies: {', '.join(requires) if requires else 'none'}.\n"
        f"Output ONLY the Lean 4 code (def/structure/theorem + sorry), no explanation.\n"
        f"Use Mathlib conventions (MeasureTheory, ProbabilityTheory namespaces). Keep it minimal.\n"
        f"For theorems, use `theorem name : <type> := sorry`.\n"
        f"For definitions, use `def name ... := ...` or `structure name ... where`."
    )

    # Method 1: Anthropic Python SDK
    try:
        import anthropic
        if os.environ.get("ANTHROPIC_API_KEY"):
            client = anthropic.Anthropic()
            response = client.messages.create(
                model="claude-haiku-4-5-20251001",
                max_tokens=1024,
                messages=[{"role": "user", "content": prompt}],
            )
            text = response.content[0].text.strip()
            # Strip markdown fences if present
            if text.startswith("```"):
                lines = text.split("\n")
                lines = [l for l in lines if not l.startswith("```")]
                text = "\n".join(lines).strip()
            print(f"[resolve]   Claude SDK generated sketch for {cid}")
            return text
    except ImportError:
        pass
    except Exception as e:
        print(f"[resolve]   Claude SDK error for {cid}: {e}", file=sys.stderr)

    # Method 2: Claude CLI (unset CLAUDECODE to allow nesting)
    try:
        env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
        result = subprocess.run(
            ["claude", "-p", "--output-format", "text", "--model", "claude-haiku-4-5-20251001"],
            input=prompt,
            capture_output=True, text=True, timeout=60,
            env=env,
        )
        if result.returncode == 0 and result.stdout.strip():
            text = result.stdout.strip()
            if text.startswith("```"):
                lines = text.split("\n")
                lines = [l for l in lines if not l.startswith("```")]
                text = "\n".join(lines).strip()
            print(f"[resolve]   Claude CLI generated sketch for {cid}")
            return text
    except FileNotFoundError:
        pass
    except Exception as e:
        print(f"[resolve]   Claude CLI error for {cid}: {e}", file=sys.stderr)

    print(f"[resolve]   no Claude available for {cid}, using placeholder")
    return ""


# ---------------------------------------------------------------------------
# YAML generation
# ---------------------------------------------------------------------------

def _lean_name_from_id(concept_id: str) -> str:
    """Generate lean_name from ontology id.

    Strips _theorem/_def suffixes and returns snake_case.

    >>> _lean_name_from_id("cramer_rao")
    'cramer_rao'
    >>> _lean_name_from_id("basu_theorem")
    'basu'
    >>> _lean_name_from_id("fisher_information_def")
    'fisher_information'
    """
    name = concept_id
    for suffix in ("_theorem", "_def", "_definition", "_lemma"):
        if name.endswith(suffix):
            name = name[: -len(suffix)]
            break
    return name


def generate_theorems_yaml(
    resolved: list[dict],
    pdf_matches: dict[str, dict],
    output: Path,
    *,
    no_claude: bool = False,
) -> None:
    """Generate theorems.yaml from resolved ontology concepts + optional PDF LaTeX.

    Each concept becomes a theorem entry. Fields from ontology:
      - id, title (name), kind, lean routing (topic/module)
      - lean_sketch (if present) → lean_statement
    Fields from PDF (if matched):
      - latex_statement, latex_proof_hint
    If no lean_sketch and not no_claude, calls Claude to generate a sketch.
    """
    id_map = {c["id"]: c for c in resolved}

    theorems: list[dict] = []
    for i, concept in enumerate(resolved, start=1):
        cid = concept["id"]
        pdf = pdf_matches.get(cid, {})

        lean_name = _lean_name_from_id(cid)
        topic = concept.get("lean_topic", "Misc")
        module = concept.get("lean_module", "Basic")
        namespace = f"Statlean.{topic}.{module}" if topic else "Statlean.Misc.Pipeline"

        # --- lean_statement: ontology lean_sketch → Claude fallback → empty ---
        lean_stmt = concept.get("lean_sketch", "")
        if isinstance(lean_stmt, str):
            lean_stmt = lean_stmt.strip()
        else:
            lean_stmt = ""

        if not lean_stmt and not no_claude:
            # NOTE: Claude API is reserved for PDF extraction only.
            # Skeleton generation is done by Claude Code in the generate step.
            # call_claude_sketch() is disabled by default; use --force-claude to enable.
            print(f"[resolve]   no lean_sketch for {cid}, leaving empty (use --force-claude to generate)")
            lean_stmt = ""

        # Compute dependencies (only those in the resolved set)
        deps = []
        for dep_id in concept.get("requires", []):
            if dep_id in id_map:
                deps.append(f"concept.{dep_id}")

        entry: Dict[str, Any] = {
            "id": f"concept.{cid}",
            "title": concept.get("name", cid),
            "kind": concept.get("kind", "theorem"),
            "latex_statement": pdf.get("latex_statement", ""),
            "latex_proof_hint": pdf.get("latex_proof_hint", ""),
            "lean_name": lean_name,
            "lean_statement": lean_stmt,
            "lean_namespace": namespace,
            "layer": "formalization",
            "priority": 3,
            "dependencies": deps,
            "assumptions": [],
            "acceptance": [
                "lake build passes",
                "theorem contains no sorry",
                "theorem contains no axiom",
            ],
            "notes": f"From ontology: {cid} (level {concept.get('level', '?')})",
        }

        # Skip if statlean file already exists
        statlean_path = concept.get("statlean", "")
        if statlean_path:
            repo_root = _SCRIPT_DIR.parent.parent
            if (repo_root / statlean_path).is_file():
                entry["notes"] += " [EXISTING — review only]"

        theorems.append(entry)

    data = {
        "version": "v1",
        "theorem_set": "concept-resolved",
        "defaults": {
            "lean_namespace": "Statlean",
            "layer": "formalization",
            "allow_axiom": False,
        },
        "theorems": theorems,
    }

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        yaml.safe_dump(data, sort_keys=False, allow_unicode=True),
        encoding="utf-8",
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_concepts_arg(arg: str) -> list[str]:
    """Split comma/space separated concept list.

    >>> parse_concepts_arg("cramer_rao, Fisher Information, basu")
    ['cramer_rao', 'Fisher Information', 'basu']
    >>> parse_concepts_arg("cramer_rao")
    ['cramer_rao']
    """
    # Split on commas first
    parts = [p.strip() for p in arg.split(",")]
    # Filter empty
    return [p for p in parts if p]


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Resolve concept names to ontology, expand deps, generate theorems.yaml"
    )
    parser.add_argument(
        "--concepts",
        required=True,
        help="Comma-separated concept names or IDs (e.g. 'cramer_rao, Fisher Information')",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("theme/input/theorems.yaml"),
        help="Output path for theorems.yaml",
    )
    parser.add_argument(
        "--pdf",
        type=Path,
        default=None,
        help="Optional PDF file to extract LaTeX from",
    )
    parser.add_argument(
        "--no-deps",
        action="store_true",
        help="Do not expand dependency tree, only include listed concepts",
    )
    parser.add_argument(
        "--no-claude",
        action="store_true",
        help="(deprecated, now default) Do not call Claude API for missing lean_sketch",
    )
    parser.add_argument(
        "--force-claude",
        action="store_true",
        help="Force Claude API for missing lean_sketch (API credits required)",
    )
    args = parser.parse_args()

    concepts = load_ontology()
    if not concepts:
        print("[resolve] ERROR: failed to load stat_ontology.yaml", file=sys.stderr)
        sys.exit(1)

    # Parse user input
    names = parse_concepts_arg(args.concepts)
    print(f"[resolve] input concepts: {names}")

    # Resolve each name
    resolved_roots: list[dict] = []
    unresolved: list[str] = []
    for name in names:
        c = resolve_concept(name, concepts)
        if c:
            resolved_roots.append(c)
            print(f"[resolve]   '{name}' -> {c['id']} ({c['name']})")
        else:
            unresolved.append(name)
            print(f"[resolve]   '{name}' -> NOT FOUND", file=sys.stderr)

    if unresolved:
        print(
            f"[resolve] WARNING: {len(unresolved)} concept(s) not found: {unresolved}",
            file=sys.stderr,
        )

    if not resolved_roots:
        print("[resolve] ERROR: no concepts resolved", file=sys.stderr)
        sys.exit(1)

    # Expand dependencies
    root_ids = [c["id"] for c in resolved_roots]
    expanded_ids = expand_deps(root_ids, concepts, no_deps=args.no_deps)
    sorted_ids = topo_sort(expanded_ids, concepts)

    id_map = {c["id"]: c for c in concepts}
    resolved_concepts = [id_map[cid] for cid in sorted_ids if cid in id_map]

    print(f"[resolve] expanded: {len(root_ids)} roots -> {len(resolved_concepts)} concepts")
    for c in resolved_concepts:
        marker = " *" if c["id"] in root_ids else ""
        print(f"[resolve]   {c['id']} ({c['name']}){marker}")

    # Match PDF blocks (optional)
    pdf_matches: dict[str, dict] = {}
    if args.pdf:
        print(f"[resolve] extracting from PDF: {args.pdf}")
        pdf_matches = match_pdf_blocks(resolved_concepts, args.pdf)
        print(f"[resolve] matched {len(pdf_matches)} concepts to PDF blocks")

    # Generate output
    # API is reserved for PDF extraction only; sketch generation is off by default
    no_claude = not args.force_claude
    generate_theorems_yaml(resolved_concepts, pdf_matches, args.output,
                           no_claude=no_claude)
    print(f"[resolve] wrote {args.output} ({len(resolved_concepts)} entries)")


if __name__ == "__main__":
    main()
