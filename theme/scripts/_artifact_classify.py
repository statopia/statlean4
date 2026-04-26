"""_artifact_classify — single source of truth for path → artifact kind.

Mirror of `website/server/services/artifactClassifier.ts::classifyArtifactPath`.
The two implementations MUST stay byte-identical in semantics — both are
keyed off the same UI artifact taxonomy in
`statlean/theme/conventions/ui-signals.md`.

Used by:
  - `emit_event.py artifact`  (defaults `kind_tag` from `--path` when the
    caller omits `--kind-tag`)
  - any future script that needs to default-classify a path

Classification rules (priority order — first match wins):

  1. `sorry_list.json`                         → "sorry-list"
  2. `theorems.yaml`                           → "yaml"
  3. `*.lean`                                  → "lean-live"
  4. `raw/<file>.{md,markdown,tex}`            → "pdf-extract"
  5. `extracted/<file>.{md,markdown,tex}`      → "pdf-extract"
  6. `paper.tex`                               → "pdf-extract"
  7. `raw_content.md`                          → "pdf-extract"
  8. top-level `*.{md,markdown,tex}`           → "pdf-extract"
  9. top-level `*.yaml`                        → "yaml"
 else                                          → None

Pure / structural — only looks at path components. Does NOT hit disk.
Strict on case: lowercase extensions only (PDF toolchains all emit
lowercase). Keeps the test surface small.
"""
from __future__ import annotations

import re
from typing import Optional

# Public taxonomy — keep in sync with ArtifactKind in src/lib/types.ts.
ARTIFACT_KIND_VALUES = frozenset(
    [
        "sorry-list",
        "yaml",
        "lean-skeleton",
        "lean-live",
        "pdf-extract",
        "sub-agent-result",
    ]
)

_RAW_EXT_RE = re.compile(r"^(?:.*/)?raw/[^/]+\.(md|markdown|tex)$")
_EXTRACTED_EXT_RE = re.compile(r"^(?:.*/)?extracted/[^/]+\.(md|markdown|tex)$")
_TOPLEVEL_DOC_RE = re.compile(r"^[^/]+\.(tex|md|markdown)$")
_TOPLEVEL_YAML_RE = re.compile(r"^[^/]+\.yaml$")
_LEAN_RE = re.compile(r"\.lean$")
_THEOREMS_YAML_RE = re.compile(r"(?:^|/)theorems\.yaml$")
_SORRY_LIST_RE = re.compile(r"(?:^|/)sorry_list\.json$")
_PAPER_TEX_RE = re.compile(r"(?:^|/)paper\.tex$")
_RAW_CONTENT_RE = re.compile(r"(?:^|/)raw_content\.md$")


def classify_artifact_path(rel_path: str) -> Optional[str]:
    """Classify a path that's already relative to a known root.

    Returns one of the `ARTIFACT_KIND_VALUES` strings, or `None` if the
    path doesn't match any rule. Tolerates Windows backslashes, leading
    `./`, trailing `/`.
    """
    if not rel_path:
        return None

    p = rel_path.replace("\\", "/")
    while p.startswith("./"):
        p = p[2:]
    while p.endswith("/"):
        p = p[:-1]
    if not p:
        return None

    # 1. sorry-list
    if p == "sorry_list.json" or _SORRY_LIST_RE.search(p):
        return "sorry-list"

    # 2. theorems.yaml (primary)
    if _THEOREMS_YAML_RE.search(p):
        return "yaml"

    # 3. .lean (caller resolves skeleton ↔ live)
    if _LEAN_RE.search(p):
        return "lean-live"

    # 4. raw/<f>.{md,markdown,tex}
    if _RAW_EXT_RE.match(p):
        return "pdf-extract"

    # 5. extracted/<f>.{md,markdown,tex}
    if _EXTRACTED_EXT_RE.match(p):
        return "pdf-extract"

    # 6. paper.tex (well-known)
    if p == "paper.tex" or _PAPER_TEX_RE.search(p):
        return "pdf-extract"

    # 7. raw_content.md (well-known)
    if p == "raw_content.md" or _RAW_CONTENT_RE.search(p):
        return "pdf-extract"

    # 8. top-level *.{tex,md,markdown}
    if _TOPLEVEL_DOC_RE.match(p):
        return "pdf-extract"

    # 9. top-level *.yaml (notation/scope/etc — not theorems.yaml)
    if _TOPLEVEL_YAML_RE.match(p):
        return "yaml"

    return None
