#!/usr/bin/env python3
"""Generate Lean 4 skeletons from theorems.yaml directly into Statlean/.

Each theorem is classified by classify.py into a (subdir, submodule) pair
and appended to the corresponding file inside `section PipelineGenerated`.
New files are created with module docstring + imports as needed.
The manifest is per-theorem: {id → {file, line, status}}.
"""
from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Tuple

import yaml

# Import sibling module
import sys
sys.path.insert(0, str(Path(__file__).parent))
from classify import classify_theorem, file_path as classify_file_path, lean_module_path


def sanitize_lean_ident(s: str) -> str:
    s = s.strip()
    s = re.sub(r"[^A-Za-z0-9_']+", "_", s)
    s = re.sub(r"_+", "_", s).strip("_")
    if not s:
        s = "item"
    if s[0].isdigit():
        s = f"t_{s}"
    return s


def unique_name(base: str, used: set[str]) -> str:
    if base not in used:
        used.add(base)
        return base
    i = 2
    while True:
        c = f"{base}_{i}"
        if c not in used:
            used.add(c)
            return c
        i += 1


def safe_comment(s: str, max_chars: int = 1200) -> str:
    t = (s or "").replace("/-", "/ -").replace("-/", "- /")
    t = t.strip()
    if len(t) > max_chars:
        t = t[:max_chars] + "\n..."
    return t


def _is_full_lean_file(stmt: str) -> bool:
    """Detect if lean_statement is a full Lean file (Claude SDK sketch) rather than a
    single declaration body.  Heuristics: contains `import` or `namespace` lines."""
    for line in stmt.splitlines():
        stripped = line.strip()
        if stripped.startswith("import ") or stripped.startswith("namespace "):
            return True
    return False


_DECL_KW_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance)\s",
    re.MULTILINE,
)


def _strip_lean_file_wrapper(stmt: str) -> str:
    """Strip import/open/namespace/end/variable lines from a Claude SDK sketch,
    keeping only declaration bodies (def/theorem/structure/etc.)."""
    keep: List[str] = []
    skip_prefixes = ("import ", "open ", "namespace ", "end ", "variable ", "section ",
                     "noncomputable section", "set_option ")
    for line in stmt.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("--"):
            continue
        if any(stripped.startswith(p) for p in skip_prefixes):
            continue
        keep.append(line)
    return "\n".join(keep).strip()


def _stmt_has_decl_keyword(stmt: str) -> bool:
    """Check if stmt already starts with a declaration keyword (def/theorem/structure/etc.)."""
    return bool(_DECL_KW_RE.match(stmt))


def theorem_block(item: Dict[str, Any], used_names: set[str]) -> Tuple[str, str, bool]:
    """Generate a Lean 4 theorem or definition block.

    Returns (block_text, lean_name, has_pipeline_id).
    """
    tid = str(item.get("id", "unknown.id"))
    title = str(item.get("title", tid))
    kind = str(item.get("kind", "theorem"))
    is_def = kind.lower().strip() in {"definition", "structure", "class", "abbrev", "def"}

    lean_name = sanitize_lean_ident(str(item.get("lean_name", tid.split(".")[-1])))
    lean_name = unique_name(lean_name, used_names)

    stmt = item.get("lean_statement")
    proof = item.get("lean_proof")

    # Sanitize Claude SDK sketches: if lean_statement is a full Lean file
    # (contains import/namespace lines), strip the wrapper and keep only
    # the declaration bodies.  Mark as pipeline_id since the sketch is
    # likely low-quality.
    sdk_sketch = False
    if stmt and _is_full_lean_file(str(stmt)):
        stmt = _strip_lean_file_wrapper(str(stmt))
        sdk_sketch = True
        if not stmt:
            stmt = None  # fully stripped → treat as empty

    has_pipeline_id = False
    if not stmt or not str(stmt).strip():
        has_pipeline_id = True
    if not is_def and (not proof or not str(proof).strip()):
        has_pipeline_id = True
    if sdk_sketch:
        has_pipeline_id = True

    latex_stmt = safe_comment(str(item.get("latex_statement", "")))
    latex_hint = safe_comment(str(item.get("latex_proof_hint", "")))

    lines: List[str] = []
    lines.append("/-")
    lines.append(f"ID: {tid}")
    lines.append(f"Title: {title}")
    lines.append(f"Kind: {kind}")
    if has_pipeline_id:
        lines.append(f"PIPELINE_ID: {tid}")
    lines.append("")
    lines.append("LaTeX statement:")
    lines.append(latex_stmt or "(empty)")
    lines.append("")
    lines.append("LaTeX proof hint:")
    lines.append(latex_hint or "(empty)")

    # Include Lean sketch as reference if available
    lean_sketch = safe_comment(str(item.get("lean_sketch", "")))
    if lean_sketch:
        lines.append("")
        lines.append("Lean sketch (reference, not compiled):")
        lines.append(lean_sketch)

    lines.append("-/")

    if stmt and str(stmt).strip() and _stmt_has_decl_keyword(str(stmt).strip()):
        # lean_statement already contains the full declaration (def/theorem/structure)
        # — emit as-is, but rename the declared identifier to lean_name (for dedup)
        stmt_text = str(stmt).strip()
        decl_m = _DECL_KW_RE.match(stmt_text)
        if decl_m:
            # Extract the original declared name and replace with lean_name
            after_kw = stmt_text[decl_m.end():]
            orig_name_m = re.match(r'(\S+)', after_kw)
            if orig_name_m:
                orig_name = orig_name_m.group(1)
                # Replace first occurrence of original name after keyword
                stmt_text = stmt_text[:decl_m.end()] + lean_name + after_kw[len(orig_name):]
        for ln in stmt_text.splitlines():
            lines.append(ln)
    elif is_def:
        if stmt and str(stmt).strip():
            # User provided full Lean definition — emit as-is
            for ln in str(stmt).splitlines():
                lines.append(ln)
        else:
            # Placeholder definition — use Prop := sorry so it compiles
            lines.append(f"def {lean_name} : Prop := sorry  -- TODO: fill Lean definition")
    else:
        if not stmt or not str(stmt).strip():
            stmt = "True"
        if not proof or not str(proof).strip():
            proof = "sorry"
        lines.append(f"theorem {lean_name} : {stmt} := by")
        for ln in str(proof).splitlines() or ["sorry"]:
            lines.append(f"  {ln}" if ln.strip() else "")
    lines.append("")

    return "\n".join(lines), lean_name, has_pipeline_id


def ensure_target_file(repo_root: Path, subdir: str, submodule: str) -> Path:
    """Ensure the target .lean file exists with proper header."""
    target = repo_root / "Statlean" / subdir / f"{submodule}.lean"

    if target.exists():
        return target

    # Create directory
    target.parent.mkdir(parents=True, exist_ok=True)

    # Create file with module docstring + imports
    # Include standard Mathlib imports for probability/measure theory sketches
    module_path = lean_module_path(subdir, submodule)
    header = (
        f"import Mathlib.MeasureTheory.Measure.MeasureSpace\n"
        f"import Mathlib.MeasureTheory.Integral.Bochner.Basic\n"
        f"import Mathlib.MeasureTheory.Integral.Lebesgue.Basic\n"
        f"import Mathlib.MeasureTheory.Function.LpSpace.Basic\n"
        f"import Mathlib.Probability.IdentDistrib\n"
        f"import Mathlib.Probability.Independence.Basic\n"
        f"\n"
        f"open MeasureTheory ProbabilityTheory Filter\n"
        f"\n"
        f"/-! # {subdir}/{submodule}\n"
        f"\n"
        f"Pipeline-generated declarations for {subdir}.{submodule}.\n"
        f"-/\n"
        f"\n"
        f"namespace Statlean.{subdir}.{submodule}\n"
        f"\n"
        f"end Statlean.{subdir}.{submodule}\n"
    )
    target.write_text(header, encoding="utf-8")

    # Update Statlean.lean imports
    statlean_lean = repo_root / "Statlean.lean"
    if statlean_lean.exists():
        content = statlean_lean.read_text(encoding="utf-8")
        import_line = f"import {module_path}"
        if import_line not in content:
            content = content.rstrip() + f"\n{import_line}\n"
            statlean_lean.write_text(content, encoding="utf-8")

    return target


def append_to_section(target: Path, blocks: List[str]) -> int:
    """Append theorem blocks to `section PipelineGenerated` in the target file.

    Creates the section if it doesn't exist. Returns the line number of the
    first appended block.
    """
    content = target.read_text(encoding="utf-8")
    section_marker = "section PipelineGenerated"
    end_marker = "end PipelineGenerated"

    if section_marker not in content:
        # Append section before final `end namespace` or at EOF
        block_text = "\n".join(blocks)
        appendix = (
            f"\n{section_marker}\n"
            f"/-! Declarations generated by the pipeline. -/\n\n"
            f"{block_text}\n"
            f"{end_marker}\n"
        )
        first_line = content.count("\n") + 2  # +2 for section marker + docstring
        content = content.rstrip() + "\n" + appendix
        target.write_text(content, encoding="utf-8")
        return first_line
    else:
        # Insert before `end PipelineGenerated`
        idx = content.rfind(end_marker)
        if idx == -1:
            # Malformed — append at end
            block_text = "\n".join(blocks)
            first_line = content.count("\n") + 1
            content = content.rstrip() + "\n" + block_text + "\n"
            target.write_text(content, encoding="utf-8")
            return first_line
        else:
            block_text = "\n".join(blocks)
            first_line = content[:idx].count("\n") + 1
            content = content[:idx] + block_text + "\n" + content[idx:]
            target.write_text(content, encoding="utf-8")
            return first_line


def build_project(
    repo_root: Path,
    theorems_file: Path,
    out_dir: Path,
) -> Dict[str, Any]:
    """Main entry: read theorems.yaml, classify, write to Statlean/, produce manifest."""
    data = yaml.safe_load(theorems_file.read_text(encoding="utf-8")) or {}
    items: List[Dict[str, Any]] = list(data.get("theorems", []) or [])
    source_tag = str(data.get("source_tag", ""))

    used_names: set[str] = set()
    # Per-theorem manifest
    manifest_entries: Dict[str, Dict[str, Any]] = {}
    pipeline_ids: List[str] = []

    # Group theorems by target file
    file_groups: Dict[str, List[Tuple[Dict[str, Any], str, str, bool]]] = {}

    for item in items:
        title = str(item.get("title", ""))
        # Include canonical_name in classification blob for better routing
        canonical = str(item.get("canonical_name", ""))
        classify_title = f"{title} {canonical}".strip() if canonical else title
        namespace = str(item.get("lean_namespace", ""))
        # Use latex_statement for classification (not lean_statement which has Lean variable names)
        latex_stmt = str(item.get("latex_statement", ""))
        kind = str(item.get("kind", "theorem"))

        subdir, submodule = classify_theorem(classify_title, namespace, latex_stmt, kind=kind, source_tag=source_tag)
        block, lean_name, has_pipeline_id = theorem_block(item, used_names)

        rel_path = classify_file_path(subdir, submodule)
        if rel_path not in file_groups:
            file_groups[rel_path] = []
        file_groups[rel_path].append((item, block, lean_name, has_pipeline_id))

    # Write to files (with deduplication)
    for rel_path, group in file_groups.items():
        parts = rel_path.replace("Statlean/", "").replace(".lean", "").split("/")
        subdir, submodule = parts[0], parts[1]

        target = ensure_target_file(repo_root, subdir, submodule)
        existing_content = target.read_text(encoding="utf-8")

        # Filter out blocks whose concept ID already has a comment block in the file,
        # OR whose lean_name (in any case variant) is already declared.
        new_group = []
        for item, block, lean_name, has_pipeline_id in group:
            tid = str(item.get("id", "unknown.id"))

            # Check 1: Is this concept ID already present as a comment?
            id_already_present = f"ID: {tid}" in existing_content

            # Check 2: Is the lean_name already declared (any case variant)?
            # Generate both snake_case and PascalCase variants
            name_variants = {lean_name}
            # snake_case → PascalCase
            pascal = "".join(w.capitalize() for w in lean_name.split("_"))
            name_variants.add(pascal)
            # PascalCase → snake_case (basic)
            snake = re.sub(r'(?<!^)(?=[A-Z])', '_', lean_name).lower()
            name_variants.add(snake)

            name_declared = False
            for variant in name_variants:
                decl_pattern = re.compile(
                    rf'(?:^|\n)\s*(?:noncomputable\s+)?(?:def|theorem|lemma|structure|class|abbrev)\s+{re.escape(variant)}\b'
                )
                if decl_pattern.search(existing_content):
                    name_declared = True
                    break

            if id_already_present or name_declared:
                # Find existing line number for manifest
                line_num = 1
                for i, line in enumerate(existing_content.splitlines(), 1):
                    for variant in name_variants:
                        if re.search(rf'\b(?:def|theorem|lemma|structure|class|abbrev)\s+{re.escape(variant)}\b', line):
                            line_num = i
                            break
                    if line_num > 1:
                        break
                manifest_entries[tid] = {
                    "file": rel_path,
                    "line": line_num,
                    "lean_name": lean_name,
                    "status": "existing",
                }
                if has_pipeline_id:
                    pipeline_ids.append(tid)
                continue
            new_group.append((item, block, lean_name, has_pipeline_id))

        if new_group:
            blocks = [g[1] for g in new_group]
            first_line = append_to_section(target, blocks)

            # Record manifest entries
            offset = 0
            for item, block, lean_name, has_pipeline_id in new_group:
                tid = str(item.get("id", "unknown.id"))
                line_num = first_line + offset
                manifest_entries[tid] = {
                    "file": rel_path,
                    "line": line_num,
                    "lean_name": lean_name,
                    "status": "pipeline_id" if has_pipeline_id else "skeleton",
                }
                if has_pipeline_id:
                    pipeline_ids.append(tid)
                offset += block.count("\n") + 1

    # Write manifest
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "repo_root": str(repo_root.resolve()),
        "theorems_file": str(theorems_file.resolve()),
        "theorem_count": len(items),
        "pipeline_id_count": len(pipeline_ids),
        "pipeline_ids": pipeline_ids,
        "entries": manifest_entries,
    }

    manifest_path = out_dir / "manifest.json"
    manifest_path.write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    return manifest


def main() -> None:
    ap = argparse.ArgumentParser(description="Generate Lean skeletons into Statlean/")
    ap.add_argument("--input-dir", required=True, help="Directory containing theorems.yaml")
    ap.add_argument("--out-dir", required=True, help="Output directory for manifest")
    ap.add_argument("--repo-root", required=True, help="Repository root")
    ap.add_argument("--theorems-file", default="", help="Path to theorems.yaml (default: input-dir/theorems.yaml)")
    args = ap.parse_args()

    input_dir = Path(args.input_dir).resolve()
    out_dir = Path(args.out_dir).resolve()
    repo_root = Path(args.repo_root).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    theorems_file = Path(args.theorems_file).resolve() if args.theorems_file else (input_dir / "theorems.yaml")
    manifest = build_project(repo_root, theorems_file, out_dir)

    print(f"[generate] theorem_count={manifest['theorem_count']}")
    print(f"[generate] pipeline_id_count={manifest['pipeline_id_count']}")
    for tid, entry in manifest.get("entries", {}).items():
        print(f"  {tid} → {entry['file']}:{entry['line']} ({entry['status']})")


if __name__ == "__main__":
    main()
