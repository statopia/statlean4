#!/usr/bin/env python3
"""Extract theorems from PDF → structured LaTeX.

Backends:
    pymupdf    — fast, local, no API cost (default for all modes)
    claude-api — most accurate, uses Claude API (requires ANTHROPIC_API_KEY, costs credits)
    openai-api — uses OpenAI API (requires OPENAI_API_KEY, costs credits)
    mineru     — MinerU OCR + VLM (requires local GPU or heavy CPU)

pymupdf extracts raw text; Claude Code can post-process in-session to restore LaTeX.

Usage:
    # Full PDF extraction (pymupdf, fast, zero cost)
    python3 pdf_extract.py --pdf <file.pdf> --output-dir <dir>

    # Extract only specific pages
    python3 pdf_extract.py --pdf <file.pdf> --output-dir <dir> --pages 5-8

    # Extract a specific theorem (auto-finds the page)
    python3 pdf_extract.py --pdf <file.pdf> --output-dir <dir> --theorem "4.1"

    # Search by keyword (finds pages containing the keyword, sends only those)
    python3 pdf_extract.py --pdf <file.pdf> --output-dir <dir> --query "consistency of MLE"
"""
from __future__ import annotations

import argparse
import base64
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import List, Dict, Optional, Tuple


# ── Common statistics notation defaults ──
DEFAULT_NOTATION = {
    "symbols": {
        r"\mathbb{E}": "expectation",
        r"\operatorname{E}": "expectation",
        r"\operatorname{Var}": "variance",
        r"\mathbb{V}": "variance",
        r"\operatorname{Cov}": "covariance",
        r"\mathbb{P}": "probability",
        r"\operatorname{P}": "probability",
        r"\mathcal{N}": "normal distribution",
        r"\sim": "distributed as",
        r"\perp": "independent",
        r"\mid": "conditional",
        r"\mathbb{R}": "real numbers",
        r"\mathbb{Z}": "integers",
        r"\mathbb{N}": "natural numbers",
        r"\nabla": "gradient",
        r"\partial": "partial derivative",
        r"\int": "integral",
        r"\sum": "summation",
        r"\prod": "product",
        r"\sup": "supremum",
        r"\inf": "infimum",
        r"\lim": "limit",
        r"\log": "logarithm",
        r"\exp": "exponential",
        r"\|": "norm delimiter",
        r"\lfloor": "floor",
        r"\lceil": "ceiling",
    }
}


# ── Theorem-like block detection ──
THEOREM_KEYWORDS = [
    "theorem", "lemma", "corollary", "proposition",
    "definition", "remark", "example", "conjecture",
]
PROOF_KEYWORDS = ["proof", "proof sketch", "proof outline"]

THEOREM_HEADING_RE = re.compile(
    r"(?:^|\n)\s*(?:\*\*|#{1,4}\s*)"
    r"(" + "|".join(THEOREM_KEYWORDS) + r")"
    r"\s*(\d+(?:\.\d+)*)?\s*"
    r"(?:\(([^)]*)\))?\s*\.?\s*\*?\*?",
    re.IGNORECASE,
)

PROOF_HEADING_RE = re.compile(
    r"(?:^|\n)\s*(?:\*\*|#{1,4}\s*)"
    r"(" + "|".join(PROOF_KEYWORDS) + r")"
    r"\s*(?:of\s+(?:theorem|lemma|corollary|proposition)\s*(\d+(?:\.\d+)*))?\s*\.?\s*\*?\*?",
    re.IGNORECASE,
)


# ═══════════════════════════════════════════════════════════
# Page scanning: find relevant pages (fast, local)
# ═══════════════════════════════════════════════════════════

def scan_pages_for_keyword(pdf_path: Path, keyword: str) -> List[int]:
    """Scan PDF text to find pages containing the keyword. Returns 0-indexed page numbers."""
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    matching_pages = []
    keyword_lower = keyword.lower()
    for i in range(len(doc)):
        text = doc[i].get_text().lower()
        if keyword_lower in text:
            matching_pages.append(i)
    doc.close()
    return matching_pages


def scan_pages_for_theorem(pdf_path: Path, theorem_id: str) -> List[int]:
    """Find pages containing a specific theorem (e.g., "4.1", "Theorem 4.1").
    Returns the theorem page + next page (for proofs that span pages)."""
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    matching = []
    all_keywords = THEOREM_KEYWORDS + ["example", "remark", "conjecture"]
    keyword_alt = "|".join(all_keywords + ["thm", "lem", "cor", "prop", "def", "ex", "rem"])
    patterns = [
        re.compile(rf"(?:{keyword_alt})\.?\s*{re.escape(theorem_id)}", re.IGNORECASE),
        # Also match just the bare identifier in case of different formatting.
        # Case-insensitive: user may type "lemma s3" while the PDF prints
        # "Lemma S3" or vice-versa — old case-sensitive regex missed both.
        re.compile(rf"\b{re.escape(theorem_id)}\b", re.IGNORECASE),
    ]
    for i in range(len(doc)):
        text = doc[i].get_text()
        if any(p.search(text) for p in patterns):
            matching.append(i)
            # Also include next page (proof might continue)
            if i + 1 < len(doc):
                matching.append(i + 1)
    doc.close()
    return sorted(set(matching))


def parse_page_range(page_spec: str, total_pages: int) -> List[int]:
    """Parse page range like '1-5,8,10-12' into 0-indexed page list."""
    pages = set()
    for part in page_spec.split(","):
        part = part.strip()
        if "-" in part:
            start, end = part.split("-", 1)
            start = max(1, int(start))
            end = min(total_pages, int(end))
            pages.update(range(start - 1, end))  # convert to 0-indexed
        else:
            p = int(part)
            if 1 <= p <= total_pages:
                pages.add(p - 1)
    return sorted(pages)


# ═══════════════════════════════════════════════════════════
# Backend: pymupdf (fast, local, no model)
# ═══════════════════════════════════════════════════════════

def run_pymupdf(pdf_path: Path, raw_output_dir: Path, pages: Optional[List[int]] = None) -> Path:
    """Extract PDF to markdown using pymupdf4llm."""
    try:
        import pymupdf4llm
    except ImportError:
        raise SystemExit("[pdf-extract] pymupdf4llm not found. Install: pip install pymupdf4llm")

    raw_output_dir.mkdir(parents=True, exist_ok=True)
    print(f"[pdf-extract] Running pymupdf4llm on {pdf_path.name}")

    if pages is not None:
        md_text = pymupdf4llm.to_markdown(str(pdf_path), pages=pages)
        print(f"[pdf-extract] Extracted pages {[p+1 for p in pages]}")
    else:
        md_text = pymupdf4llm.to_markdown(str(pdf_path))

    md_file = raw_output_dir / f"{pdf_path.stem}.md"
    md_file.write_text(md_text, encoding="utf-8")
    print(f"[pdf-extract] pymupdf4llm output: {md_file} ({len(md_text)} chars)")
    return md_file


# ═══════════════════════════════════════════════════════════
# Backend: claude (most accurate, uses Claude API)
# ═══════════════════════════════════════════════════════════

def pdf_to_page_images(pdf_path: Path, pages: Optional[List[int]] = None) -> List[Tuple[int, bytes]]:
    """Convert PDF pages to PNG images. Returns list of (page_num, png_bytes)."""
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    images = []
    page_indices = pages if pages is not None else range(len(doc))
    for page_num in page_indices:
        page = doc[page_num]
        mat = pymupdf.Matrix(2, 2)  # 2x resolution for better quality
        pix = page.get_pixmap(matrix=mat)
        images.append((page_num, pix.tobytes("png")))
    doc.close()
    return images


def _extract_page_text(pdf_path: Path, pages: Optional[List[int]] = None) -> Dict[int, str]:
    """Extract raw text per page using pymupdf."""
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    result = {}
    indices = pages if pages is not None else range(len(doc))
    for i in indices:
        result[i] = doc[i].get_text()
    doc.close()
    return result


def run_claude_extract(pdf_path: Path, raw_output_dir: Path,
                       pages: Optional[List[int]] = None,
                       theorem_id: Optional[str] = None,
                       query: Optional[str] = None) -> Path:
    """Use Claude to extract theorems from PDF.

    Strategy:
    - If ANTHROPIC_API_KEY is set: send page images via SDK (most accurate)
    - Otherwise: extract text via pymupdf, send to Claude CLI for LaTeX restoration
    """
    raw_output_dir.mkdir(parents=True, exist_ok=True)
    use_images = bool(os.environ.get("ANTHROPIC_API_KEY"))

    if use_images:
        print(f"[pdf-extract] Using Anthropic SDK with page images (most accurate)")
    else:
        print(f"[pdf-extract] Using Claude CLI with extracted text (no API key for images)")
        print(f"[pdf-extract] Tip: set ANTHROPIC_API_KEY for image-based extraction")

    # Build focus instruction
    if theorem_id:
        focus = f"Focus on Theorem/Lemma/Definition {theorem_id}. Extract its FULL statement and proof."
    elif query:
        focus = f"Focus on content related to: {query}. Extract all relevant theorems, definitions, and proofs."
    else:
        focus = "Extract ALL theorems, lemmas, definitions, propositions, corollaries, and their proofs."

    instructions = f"""{focus}

For each theorem-like block found, output in this EXACT format:

## [Type] [Number] [Optional Name]
[Full statement with LaTeX: $...$ for inline, $$...$$ for display math]

### Proof
[Proof content if present]

Rules:
- Use standard LaTeX: \\mathbb{{E}}, \\operatorname{{Var}}, \\mathcal{{N}}, etc.
- Preserve ALL mathematical details — every subscript, superscript, condition
- Skip headers/footers, page numbers, author info
- If a formula is unclear, add: %% OCR_UNCERTAIN: [what's unclear]"""

    all_md_parts: List[str] = []

    if use_images:
        # Image-based extraction via SDK
        page_images = pdf_to_page_images(pdf_path, pages)
        print(f"[pdf-extract] {len(page_images)} pages to process as images")

        batch_size = 10
        for batch_start in range(0, len(page_images), batch_size):
            batch = page_images[batch_start:batch_start + batch_size]
            page_nums = [p + 1 for p, _ in batch]
            page_range_str = f"{page_nums[0]}-{page_nums[-1]}" if len(page_nums) > 1 else str(page_nums[0])
            print(f"[pdf-extract] Sending pages {page_range_str} to Claude...")

            content_parts = []
            for _, img_bytes in batch:
                b64 = base64.b64encode(img_bytes).decode("ascii")
                content_parts.append({
                    "type": "image",
                    "source": {"type": "base64", "media_type": "image/png", "data": b64}
                })
            content_parts.append({"type": "text", "text": instructions + f"\n\nPages shown: {page_range_str}"})

            md_part = _call_claude_api(content_parts)
            all_md_parts.append(md_part)
    else:
        # Text-based extraction via CLI
        page_texts = _extract_page_text(pdf_path, pages)
        print(f"[pdf-extract] {len(page_texts)} pages extracted as text")

        # Process in batches of 10 pages
        page_items = sorted(page_texts.items())
        batch_size = 10
        for batch_start in range(0, len(page_items), batch_size):
            batch = page_items[batch_start:batch_start + batch_size]
            page_nums = [p + 1 for p, _ in batch]
            page_range_str = f"{page_nums[0]}-{page_nums[-1]}" if len(page_nums) > 1 else str(page_nums[0])
            print(f"[pdf-extract] Sending pages {page_range_str} to Claude CLI...")

            # Build text content with page markers
            text_content = ""
            for page_num, text in batch:
                text_content += f"\n===== PAGE {page_num + 1} =====\n{text}\n"

            prompt = f"""Below is text extracted from a mathematics/statistics PDF (pages {page_range_str}).
The math formulas have been converted to Unicode and lost their LaTeX formatting.

YOUR TASK: Restore the mathematical content to proper LaTeX and identify theorem-like blocks.

{instructions}

--- PDF TEXT (pages {page_range_str}) ---
{text_content}
--- END PDF TEXT ---"""

            content_parts = [{"type": "text", "text": prompt}]
            md_part = _call_claude_api(content_parts)
            all_md_parts.append(md_part)

    full_md = "\n\n".join(all_md_parts)
    suffix = f"_thm{theorem_id}" if theorem_id else ("_query" if query else "")
    md_file = raw_output_dir / f"{pdf_path.stem}{suffix}_claude.md"
    md_file.write_text(full_md, encoding="utf-8")
    print(f"[pdf-extract] Claude extraction: {md_file} ({len(full_md)} chars)")
    return md_file


def _call_claude_api(content_parts: list) -> str:
    """Call Claude API with image+text content. Tries SDK first, then CLI."""
    # Method 1: Anthropic Python SDK (needs ANTHROPIC_API_KEY)
    try:
        import anthropic
        if os.environ.get("ANTHROPIC_API_KEY"):
            client = anthropic.Anthropic()
            response = client.messages.create(
                model="claude-sonnet-4-20250514",
                max_tokens=8192,
                messages=[{"role": "user", "content": content_parts}],
            )
            return response.content[0].text
    except ImportError:
        pass
    except Exception as e:
        print(f"[pdf-extract] SDK error: {e}", file=sys.stderr)

    # Method 2: Claude CLI (unset CLAUDECODE to allow nesting)
    # Extract text prompt from content_parts
    text_prompt = ""
    for part in content_parts:
        if isinstance(part, dict) and part.get("type") == "text":
            text_prompt = part["text"]
            break

    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    result = subprocess.run(
        ["claude", "-p", "--output-format", "text"],
        input=text_prompt,
        capture_output=True, text=True, timeout=300,
        env=env,
    )
    if result.returncode != 0:
        print(f"[pdf-extract] Claude CLI error: {result.stderr[:500]}", file=sys.stderr)
        return f"% Claude extraction failed\n% Error: {result.stderr[:200]}"
    return result.stdout


# ═══════════════════════════════════════════════════════════
# Backend: openai-api (uses OpenAI API for extraction)
# ═══════════════════════════════════════════════════════════

def _call_openai_api(content_parts: list) -> str:
    """Call OpenAI API with text content. Tries SDK first, then Codex CLI."""
    # Extract text prompt from content_parts
    text_prompt = ""
    for part in content_parts:
        if isinstance(part, dict) and part.get("type") == "text":
            text_prompt = part["text"]
            break

    # Method 1: OpenAI Python SDK (needs OPENAI_API_KEY)
    try:
        import openai
        if os.environ.get("OPENAI_API_KEY"):
            client = openai.OpenAI()
            response = client.chat.completions.create(
                model="gpt-4o",
                max_tokens=8192,
                messages=[{"role": "user", "content": text_prompt}],
            )
            return response.choices[0].message.content
    except ImportError:
        pass
    except Exception as e:
        print(f"[pdf-extract] OpenAI SDK error: {e}", file=sys.stderr)

    # Method 2: Codex CLI
    try:
        result = subprocess.run(
            ["codex", "exec", "--full-auto", text_prompt],
            capture_output=True, text=True, timeout=300,
        )
        if result.returncode != 0:
            print(f"[pdf-extract] Codex CLI error: {result.stderr[:500]}", file=sys.stderr)
            return f"% OpenAI extraction failed\n% Error: {result.stderr[:200]}"
        return result.stdout
    except FileNotFoundError:
        print("[pdf-extract] ERROR: neither openai SDK nor codex CLI available", file=sys.stderr)
        return "% OpenAI extraction failed — no SDK or CLI available"
    except Exception as e:
        print(f"[pdf-extract] Codex CLI error: {e}", file=sys.stderr)
        return f"% OpenAI extraction failed\n% Error: {e}"


def run_openai_extract(pdf_path: Path, raw_output_dir: Path,
                       pages: Optional[List[int]] = None,
                       theorem_id: Optional[str] = None,
                       query: Optional[str] = None) -> Path:
    """Use OpenAI to extract theorems from PDF (text-based only)."""
    raw_output_dir.mkdir(parents=True, exist_ok=True)
    print(f"[pdf-extract] Using OpenAI backend for extraction")

    # Build focus instruction
    if theorem_id:
        focus = f"Focus on Theorem/Lemma/Definition {theorem_id}. Extract its FULL statement and proof."
    elif query:
        focus = f"Focus on content related to: {query}. Extract all relevant theorems, definitions, and proofs."
    else:
        focus = "Extract ALL theorems, lemmas, definitions, propositions, corollaries, and their proofs."

    instructions = f"""{focus}

For each theorem-like block found, output in this EXACT format:

## [Type] [Number] [Optional Name]
[Full statement with LaTeX: $...$ for inline, $$...$$ for display math]

### Proof
[Proof content if present]

Rules:
- Use standard LaTeX: \\mathbb{{E}}, \\operatorname{{Var}}, \\mathcal{{N}}, etc.
- Preserve ALL mathematical details — every subscript, superscript, condition
- Skip headers/footers, page numbers, author info
- If a formula is unclear, add: %% OCR_UNCERTAIN: [what's unclear]"""

    # Text-based extraction via pymupdf + OpenAI
    page_texts = _extract_page_text(pdf_path, pages)
    print(f"[pdf-extract] {len(page_texts)} pages extracted as text")

    all_md_parts: List[str] = []
    page_items = sorted(page_texts.items())
    batch_size = 10
    for batch_start in range(0, len(page_items), batch_size):
        batch = page_items[batch_start:batch_start + batch_size]
        page_nums = [p + 1 for p, _ in batch]
        page_range_str = f"{page_nums[0]}-{page_nums[-1]}" if len(page_nums) > 1 else str(page_nums[0])
        print(f"[pdf-extract] Sending pages {page_range_str} to OpenAI...")

        text_content = ""
        for page_num, text in batch:
            text_content += f"\n===== PAGE {page_num + 1} =====\n{text}\n"

        prompt = f"""Below is text extracted from a mathematics/statistics PDF (pages {page_range_str}).
The math formulas have been converted to Unicode and lost their LaTeX formatting.

YOUR TASK: Restore the mathematical content to proper LaTeX and identify theorem-like blocks.

{instructions}

--- PDF TEXT (pages {page_range_str}) ---
{text_content}
--- END PDF TEXT ---"""

        content_parts = [{"type": "text", "text": prompt}]
        md_part = _call_openai_api(content_parts)
        all_md_parts.append(md_part)

    full_md = "\n\n".join(all_md_parts)
    suffix = f"_thm{theorem_id}" if theorem_id else ("_query" if query else "")
    md_file = raw_output_dir / f"{pdf_path.stem}{suffix}_openai.md"
    md_file.write_text(full_md, encoding="utf-8")
    print(f"[pdf-extract] OpenAI extraction: {md_file} ({len(full_md)} chars)")
    return md_file


# ═══════════════════════════════════════════════════════════
# Backend: mineru (heavy, needs GPU or lots of CPU/RAM)
# ═══════════════════════════════════════════════════════════

def check_mineru() -> bool:
    return shutil.which("mineru") is not None


def _has_gpu() -> bool:
    """Detect whether a real NVIDIA GPU is available.

    torch.cuda.is_available() is NOT reliable here — on CPU-only boxes
    where torch was installed as the CUDA build (e.g. via `pip install
    torch==X.Y.Z+cu124`), it returns True even with no actual device,
    then `torchvision::nms` dispatches to a CUDA backend that has no
    kernel and raises NotImplementedError inside MinerU hybrid, which
    silently swallows it → exit 0 with empty output. See
    docs/CLI_WEB_CONFORMANCE.md §12 (CPU-only VPS silent-fail case).

    Two cheap, authoritative probes:
      1. /dev/nvidia0 exists (kernel driver loaded)
      2. nvidia-smi on PATH (userspace tooling installed)
    Both true → real GPU. Either false → treat as CPU-only.
    """
    return Path("/dev/nvidia0").exists() and shutil.which("nvidia-smi") is not None


def _mineru_attempt(
    cmd: List[str],
    raw_output_dir: Path,
    label: str,
    env: Optional[Dict[str, str]] = None,
    timeout: Optional[float] = None,
) -> Optional[Path]:
    """Run one MinerU invocation and return the path to its main `.md`
    output, or None if MinerU exited 0 but produced no usable markdown
    (silent failure — empirically observed on long docs, e.g. 83-page PDFs
    with -b hybrid-auto-engine; see docs/CLI_WEB_CONFORMANCE.md §12).

    `env` lets the caller override subprocess env (used to set
    `CUDA_VISIBLE_DEVICES=""` when hybrid runs on a CPU-only host with a
    CUDA-build torch so torchvision's nms stays on the CPU backend).

    `timeout` caps wall time for the attempt. Exceeded → log + return
    None so the caller can fall back to the next backend instead of
    hanging forever on a VLM inference that will never complete in a
    user-acceptable window.
    """
    print(f"[pdf-extract] Running ({label}): {' '.join(cmd)}")
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, env=env, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        print(
            f"[pdf-extract] MinerU ({label}) timed out after {timeout}s — "
            f"treating as attempt failure (caller will fall back).",
            file=sys.stderr,
        )
        return None
    if result.returncode != 0:
        print(f"[pdf-extract] MinerU ({label}) stderr:\n{result.stderr[-2000:]}", file=sys.stderr)
        return None
    md_files = [p for p in raw_output_dir.rglob("*.md") if p.stat().st_size >= 100]
    if not md_files:
        print(
            f"[pdf-extract] MinerU ({label}) exit 0 but produced no non-empty "
            f"markdown under {raw_output_dir} — silent failure, treating as "
            f"attempt failure.",
            file=sys.stderr,
        )
        return None
    md_file = max(md_files, key=lambda p: p.stat().st_size)
    print(f"[pdf-extract] MinerU ({label}) output: {md_file} ({md_file.stat().st_size} bytes)")
    return md_file


def _page_range_flags(target_pages: Optional[List[int]]) -> List[str]:
    """Convert an (optionally non-contiguous) list of 0-indexed page
    numbers into MinerU `-s <start> -e <end>` flags.

    MinerU CLI only supports a single contiguous range. For
    non-contiguous requests like `[32, 40, 50]` we pass the superset
    `-s 32 -e 50` — still a massive speedup vs processing the whole
    PDF, and the downstream structure extractor filters blocks by
    heading match anyway.
    """
    if not target_pages:
        return []
    lo = min(target_pages)
    hi = max(target_pages)
    flags = ["-s", str(lo), "-e", str(hi)]
    if set(target_pages) != set(range(lo, hi + 1)):
        print(
            f"[pdf-extract] target_pages {sorted(target_pages)} is non-contiguous; "
            f"passing MinerU the superset [{lo},{hi}] ({hi - lo + 1} pages).",
            file=sys.stderr,
        )
    return flags


# CPU-hybrid budget. Empirically hybrid-auto-engine VLM inference on a
# 10-core CPU-only WSL box took ~74 s/page (MinerU 2.7 / 1.2B VLM model).
# We'll try hybrid when pages <= HYBRID_MAX_PAGES_CPU and cap wall time at
# HYBRID_TIMEOUT_CPU — if exceeded, fall back to pipeline which is ~3× faster
# on CPU at the cost of noisier LaTeX (`V a r`, `\operatorname*{s u p}`).
# On GPU hosts we skip both caps: hybrid is fast enough to run on the whole PDF.
HYBRID_MAX_PAGES_CPU = 3
HYBRID_TIMEOUT_CPU = 360  # seconds


def run_mineru(
    pdf_path: Path,
    raw_output_dir: Path,
    target_pages: Optional[List[int]] = None,
) -> Path:
    """Extract markdown from a PDF via MinerU with a retry cascade.

    Attempt order:
      1. `-b hybrid-auto-engine` — MinerU's VLM-based backend. Cleanest
         LaTeX output per docs/CLI_WEB_CONFORMANCE.md §12. On GPU hosts:
         always tried. On CPU hosts: tried only when target_pages is set
         and small (≤ HYBRID_MAX_PAGES_CPU), with CUDA_VISIBLE_DEVICES=""
         so torchvision::nms stays on the CPU backend (else
         NotImplementedError → silent fail), and a hard wall-clock
         timeout so the agent isn't blocked for 40+ min on 46 pages.
      2. `-b pipeline -d cpu` fallback — slower per-page but reliably
         completes on CPU at any page count. Takes over when attempt 1
         was skipped, silent-failed, timed out, or errored.

    When `target_pages` is supplied the same range is passed via MinerU's
    `-s`/`-e` flags to both attempts — prevents the 83-pages-when-user-
    asked-for-3 silent slowdown that made `jobmobv6mso5nfl` take minutes.

    Raises SystemExit if both attempts fail (or pipeline fails when
    hybrid was skipped) so the caller (agent) sees the failure and can
    surface it via `request_user_decision` rather than proceeding with
    empty input and hallucinating (Rule 3).
    """
    raw_output_dir.mkdir(parents=True, exist_ok=True)
    page_flags = _page_range_flags(target_pages)

    gpu = _has_gpu()
    page_count = len(target_pages) if target_pages else None

    # Decide whether to attempt hybrid. On CPU-only hosts a 46-page VLM
    # inference is ≈ 57 minutes — not user-acceptable, so we only try
    # hybrid for small page ranges where the quality gain is worth the
    # few minutes of wall time.
    if gpu:
        attempt_hybrid = True
        hybrid_env: Optional[Dict[str, str]] = None
        hybrid_timeout: Optional[float] = None
        reason = "GPU detected"
    elif page_count is not None and page_count <= HYBRID_MAX_PAGES_CPU:
        attempt_hybrid = True
        hybrid_env = os.environ.copy()
        # setdefault so a user who already set CUDA_VISIBLE_DEVICES keeps control.
        hybrid_env.setdefault("CUDA_VISIBLE_DEVICES", "")
        hybrid_timeout = HYBRID_TIMEOUT_CPU
        reason = f"CPU-only, pages={page_count} ≤ {HYBRID_MAX_PAGES_CPU}"
    else:
        attempt_hybrid = False
        hybrid_env = None
        hybrid_timeout = None
        reason = (
            f"CPU-only, pages={page_count or 'all'} > {HYBRID_MAX_PAGES_CPU} "
            f"(VLM on CPU is ~74s/page; skipping to avoid long wall time)"
        )

    if attempt_hybrid:
        print(f"[pdf-extract] hybrid gate: attempting ({reason})")
        hybrid_cmd = [
            "mineru", "-p", str(pdf_path), "-o", str(raw_output_dir),
            "-m", "auto", "-b", "hybrid-auto-engine",
            *page_flags,
        ]
        md_file = _mineru_attempt(
            hybrid_cmd, raw_output_dir, "hybrid-auto-engine",
            env=hybrid_env, timeout=hybrid_timeout,
        )
        if md_file is not None:
            return md_file
        print(
            "[pdf-extract] Attempt 1 (hybrid-auto-engine) failed; "
            "retrying with `-b pipeline -d cpu`.",
            file=sys.stderr,
        )
    else:
        print(f"[pdf-extract] hybrid gate: skipped ({reason})")

    # Pipeline backend — runs on CPU, ~25 s/page, noisier LaTeX but reliable.
    pipeline_cmd = [
        "mineru", "-p", str(pdf_path), "-o", str(raw_output_dir),
        "-m", "auto", "-b", "pipeline", "-d", "cpu",
        *page_flags,
    ]
    md_file = _mineru_attempt(pipeline_cmd, raw_output_dir, "pipeline -d cpu")
    if md_file is not None:
        return md_file

    raise SystemExit(
        "[pdf-extract] MinerU failed on "
        + ("BOTH hybrid-auto-engine and pipeline backends" if attempt_hybrid else "pipeline backend (hybrid skipped)")
        + " (exit 0 with empty output, non-zero exit, or timeout). "
        "Do NOT hallucinate content — ask the user to paste the relevant "
        "theorem text (via request_user_decision in pipeline.md Step 1) "
        "or to provide a smaller page range."
    )


# ═══════════════════════════════════════════════════════════
# Common: theorem extraction and LaTeX generation
# ═══════════════════════════════════════════════════════════

def extract_theorem_blocks(md_text: str) -> List[Dict[str, str]]:
    """Parse markdown to extract theorem-like blocks with their proofs."""
    blocks: List[Dict[str, str]] = []
    lines = md_text.split("\n")
    current_block: Optional[Dict[str, str]] = None
    current_proof_for: Optional[str] = None
    buffer: List[str] = []

    def flush():
        nonlocal current_block, buffer, current_proof_for
        if current_block is not None:
            content = "\n".join(buffer).strip()
            if current_proof_for is not None:
                for b in reversed(blocks):
                    if b.get("number") == current_proof_for or current_proof_for is None:
                        b["proof_hint"] = content
                        break
                else:
                    if blocks:
                        blocks[-1]["proof_hint"] = content
            else:
                current_block["statement"] = content
                blocks.append(current_block)
            current_block = None
            current_proof_for = None
            buffer = []

    for line in lines:
        thm_match = THEOREM_HEADING_RE.search(line)
        if thm_match:
            flush()
            kind = thm_match.group(1).lower()
            number = thm_match.group(2) or ""
            name = thm_match.group(3) or ""
            current_block = {
                "kind": kind, "number": number, "name": name,
                "statement": "", "proof_hint": "",
            }
            rest = line[thm_match.end():].strip()
            if rest:
                buffer.append(rest)
            continue

        proof_match = PROOF_HEADING_RE.search(line)
        if proof_match:
            flush()
            current_block = {"kind": "proof", "number": "", "name": "", "statement": "", "proof_hint": ""}
            current_proof_for = proof_match.group(2) or None
            rest = line[proof_match.end():].strip()
            if rest:
                buffer.append(rest)
            continue

        if current_block is not None:
            buffer.append(line)

    flush()
    return blocks


def blocks_to_latex(blocks: List[Dict[str, str]], pdf_name: str, backend: str) -> str:
    parts: List[str] = []
    parts.append(f"% Auto-extracted from: {pdf_name}")
    parts.append(f"% Backend: {backend}")
    parts.append(r"% Review formulas marked with % OCR_UNCERTAIN before proceeding.")
    parts.append("")
    parts.append(r"\documentclass{article}")
    parts.append(r"\usepackage{amsmath,amssymb,amsthm}")
    parts.append(r"\newtheorem{theorem}{Theorem}")
    parts.append(r"\newtheorem{lemma}[theorem]{Lemma}")
    parts.append(r"\newtheorem{corollary}[theorem]{Corollary}")
    parts.append(r"\newtheorem{proposition}[theorem]{Proposition}")
    parts.append(r"\newtheorem{definition}[theorem]{Definition}")
    parts.append(r"\begin{document}")
    parts.append("")

    for block in blocks:
        kind = block["kind"]
        if kind == "proof":
            continue
        env = kind if kind in ("theorem", "lemma", "corollary", "proposition", "definition") else "theorem"
        number_comment = f"  % Original number: {block['number']}" if block["number"] else ""
        name_opt = f"[{block['name']}]" if block["name"] else ""
        parts.append(f"\\begin{{{env}}}{name_opt}{number_comment}")
        statement = block["statement"]
        statement = re.sub(r"\$\$(.+?)\$\$", r"\\[\1\\]", statement, flags=re.DOTALL)
        parts.append(statement)
        parts.append(f"\\end{{{env}}}")
        parts.append("")
        if block.get("proof_hint"):
            parts.append(r"\begin{proof}")
            proof = block["proof_hint"]
            proof = re.sub(r"\$\$(.+?)\$\$", r"\\[\1\\]", proof, flags=re.DOTALL)
            parts.append(proof)
            parts.append(r"\end{proof}")
            parts.append("")

    parts.append(r"\end{document}")
    return "\n".join(parts)


def check_latex_balance(tex: str) -> List[str]:
    warnings: List[str] = []
    depth = 0
    for i, c in enumerate(tex):
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        if depth < 0:
            line_num = tex[:i].count("\n") + 1
            warnings.append(f"Line {line_num}: extra closing brace")
            depth = 0
    if depth > 0:
        warnings.append(f"Unbalanced: {depth} unclosed braces at end of file")
    ocr_artifacts = [
        (r"\\mathbb\{[A-Z]\}[A-Z]", "possible merged mathbb"),
        (r"[^\\]_\{[^}]{20,}", "very long subscript (possible OCR merge)"),
        (r"\\[a-z]+\{$", "backslash command at end of line"),
    ]
    for pattern, msg in ocr_artifacts:
        for m in re.finditer(pattern, tex):
            line_num = tex[:m.start()].count("\n") + 1
            warnings.append(f"Line {line_num}: {msg}")
    return warnings


def generate_notation_yaml(tex: str) -> str:
    detected: Dict[str, str] = {}
    for sym, desc in DEFAULT_NOTATION["symbols"].items():
        pattern = re.escape(sym)
        if re.search(pattern, tex):
            detected[sym] = desc
    lines = ["# Auto-generated notation mapping", "# Review and edit as needed", "", "symbols:"]
    for sym, desc in sorted(detected.items()):
        lines.append(f'  "{sym}": "{desc}"')
    if not detected:
        lines.append("  # No standard symbols detected — add mappings manually")
    return "\n".join(lines) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Extract theorems from PDF → structured LaTeX",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""Examples:
  # Full PDF (fast local, zero API cost)
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/

  # Only Theorem 4.1 (auto-finds page)
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/ --theorem 4.1

  # Pages 5-8 only
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/ --pages 5-8

  # Search by keyword
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/ --query "Poincaré inequality"

  # Use Claude API for highest accuracy (costs API credits)
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/ --backend claude-api
""")
    ap.add_argument("--pdf", required=True, help="Path to input PDF")
    ap.add_argument("--output-dir", required=True, help="Output directory")
    ap.add_argument("--backend", choices=["pymupdf", "claude-api", "openai-api", "mineru"], default=None,
                    help="Extraction backend (default: pymupdf, zero API cost). claude-api requires ANTHROPIC_API_KEY. openai-api requires OPENAI_API_KEY.")
    ap.add_argument("--pages", type=str, default=None,
                    help="Page range to extract, e.g. '1-5,8,10-12' (1-indexed)")
    ap.add_argument("--theorem", type=str, default=None,
                    help="Extract a specific theorem by ID, e.g. '4.1'. Auto-finds the page.")
    ap.add_argument("--query", type=str, default=None,
                    help="Extract theorems matching a keyword/phrase. Auto-finds relevant pages.")
    ap.add_argument("--skip-ocr", action="store_true",
                    help="Skip extraction, use existing markdown in output-dir/raw/")
    args = ap.parse_args()

    pdf_path = Path(args.pdf).resolve()
    output_dir = Path(args.output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    raw_dir = output_dir / "raw"

    # Determine which pages to process
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    total_pages = len(doc)
    doc.close()
    print(f"[pdf-extract] PDF: {pdf_path.name} ({total_pages} pages)")

    target_pages: Optional[List[int]] = None

    if args.theorem:
        target_pages = scan_pages_for_theorem(pdf_path, args.theorem)
        if target_pages:
            print(f"[pdf-extract] Theorem {args.theorem} found on pages: {[p+1 for p in target_pages]}")

    elif args.query:
        target_pages = scan_pages_for_keyword(pdf_path, args.query)
        if target_pages:
            print(f"[pdf-extract] Query matches pages: {[p+1 for p in target_pages]}")

    elif args.pages:
        target_pages = parse_page_range(args.pages, total_pages)
        print(f"[pdf-extract] Using specified pages: {[p+1 for p in target_pages]}")

    # If a targeted search returned 0 hits on a large PDF, DO NOT silently
    # fall back to full-PDF OCR — that's a multi-minute footgun. Instead
    # fail closed so the agent either (a) retries with an explicit
    # --pages range, or (b) surfaces to the user via request_user_decision
    # (see pipeline.md Step 1). Empirical threshold: 15 pages — below
    # that, full-PDF OCR is still ~3 min and acceptable.
    LARGE_PDF_THRESHOLD = 15
    if target_pages is not None and len(target_pages) == 0:
        if total_pages > LARGE_PDF_THRESHOLD:
            raise SystemExit(
                f"[pdf-extract] --{'theorem' if args.theorem else 'query'} "
                f"{args.theorem or args.query!r} found no matching pages in "
                f"this {total_pages}-page PDF. Full-PDF OCR would take "
                f"~{total_pages * 15}s (= {total_pages * 15 // 60} min) of "
                f"CPU — refusing to run it silently. Either supply "
                f"--pages <range> explicitly, or ask the user to paste "
                f"the target statement (via request_user_decision). "
                f"Note: the fuzzy scan tries case-insensitive matching "
                f"for bare identifiers AND keyword+identifier pairs; if "
                f"it still missed, the PDF is likely OCR-scanned with "
                f"broken text extraction."
            )
        # Small PDFs: fall back to all pages (the old behavior — cheap).
        print("[pdf-extract] No matching pages found and PDF is short; falling back to all pages.")
        target_pages = None

    # Determine backend.
    #
    # Default policy:
    #   - mineru if installed (local VLM OCR — preserves LaTeX formulas,
    #     handles dense math), because math-heavy papers produce broken
    #     tokens under pymupdf's raw-character-stream extraction.
    #   - else pymupdf (zero-dep text extraction for clean, text-only PDFs).
    #
    # Override with --backend {pymupdf,mineru,claude-api,openai-api}. The
    # claude-api / openai-api paths are only picked when the user explicitly
    # asks, since they spend real tokens.
    is_targeted = target_pages is not None and len(target_pages) < total_pages
    if args.backend:
        backend = args.backend
    else:
        backend = "mineru" if check_mineru() else "pymupdf"
    print(f"[pdf-extract] Using backend: {backend}"
          f"{' (auto: mineru detected)' if not args.backend and backend == 'mineru' else ''}"
          f"{' (auto: mineru not installed, falling back)' if not args.backend and backend == 'pymupdf' else ''}")

    if is_targeted:
        est_tokens = len(target_pages or []) * 1500  # ~1.5K tokens per page image
        print(f"[pdf-extract] Targeted extraction: {len(target_pages or [])} pages, ~{est_tokens} input tokens")
    else:
        print(f"[pdf-extract] Full extraction: {total_pages} pages")

    # Step 1: Extract markdown from PDF
    if args.skip_ocr:
        md_files = list(raw_dir.rglob("*.md"))
        if not md_files:
            raise SystemExit(f"[pdf-extract] --skip-ocr but no .md files in {raw_dir}")
        md_file = max(md_files, key=lambda p: p.stat().st_size)
        print(f"[pdf-extract] Using existing output: {md_file}")
    elif backend == "pymupdf":
        md_file = run_pymupdf(pdf_path, raw_dir, pages=target_pages)
    elif backend == "claude-api":
        md_file = run_claude_extract(
            pdf_path, raw_dir,
            pages=target_pages,
            theorem_id=args.theorem,
            query=args.query,
        )
    elif backend == "openai-api":
        md_file = run_openai_extract(
            pdf_path, raw_dir,
            pages=target_pages,
            theorem_id=args.theorem,
            query=args.query,
        )
    elif backend == "mineru":
        if not check_mineru():
            print("[pdf-extract] ERROR: mineru not found. Install:", file=sys.stderr)
            print("  pip install 'mineru[full]' torch torchvision", file=sys.stderr)
            raise SystemExit(1)
        md_file = run_mineru(pdf_path, raw_dir, target_pages=target_pages)
    else:
        raise SystemExit(f"[pdf-extract] Unknown backend: {backend}")

    md_text = md_file.read_text(encoding="utf-8")

    # Step 2: Extract theorem blocks
    blocks = extract_theorem_blocks(md_text)
    print(f"[pdf-extract] Extracted {len(blocks)} theorem-like blocks")

    if not blocks:
        print("[pdf-extract] WARNING: no structured theorem blocks found.")
        print(f"[pdf-extract] Raw content saved at: {md_file}")
        (output_dir / "paper.tex").write_text(
            f"% No structured theorems extracted from {pdf_path.name}\n"
            f"% Backend: {backend}\n"
            f"% Raw content: {md_file}\n"
            r"\documentclass{article}" + "\n"
            r"\begin{document}" + "\n"
            "% See raw content file for extracted text\n"
            r"\end{document}" + "\n",
            encoding="utf-8",
        )
        (output_dir / "raw_content.md").write_text(md_text, encoding="utf-8")
        _write_summary(output_dir, pdf_path, [], [], md_file, backend)
        return

    # Step 3: Convert to structured LaTeX
    tex = blocks_to_latex(blocks, pdf_path.name, backend)

    # Step 4: Quality checks
    warnings = check_latex_balance(tex)
    if warnings:
        print(f"[pdf-extract] {len(warnings)} LaTeX warnings:")
        for w in warnings[:10]:
            print(f"  - {w}")
        warning_lines = "\n".join(f"% WARNING: {w}" for w in warnings)
        tex = tex.replace(r"\begin{document}",
                          f"% === Quality Warnings ===\n{warning_lines}\n\n\\begin{{document}}")

    # Step 5: Write outputs
    tex_path = output_dir / "paper.tex"
    tex_path.write_text(tex, encoding="utf-8")
    print(f"[pdf-extract] Wrote: {tex_path}")

    notation_yaml = generate_notation_yaml(tex)
    notation_path = output_dir / "notation.yaml"
    notation_path.write_text(notation_yaml, encoding="utf-8")
    print(f"[pdf-extract] Wrote: {notation_path}")

    _write_summary(output_dir, pdf_path, blocks, warnings, md_file, backend)


def _write_summary(output_dir: Path, pdf_path: Path, blocks: list, warnings: list,
                   md_file: Path, backend: str) -> None:
    summary = {
        "pdf": str(pdf_path),
        "backend": backend,
        "blocks_extracted": len(blocks),
        "block_kinds": {k: sum(1 for b in blocks if b["kind"] == k)
                        for k in set(b["kind"] for b in blocks)} if blocks else {},
        "latex_warnings": len(warnings),
        "output_tex": str(output_dir / "paper.tex"),
        "notation_yaml": str(output_dir / "notation.yaml"),
        "raw_output": str(md_file),
    }
    summary_path = output_dir / "extract_summary.json"
    summary_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"[pdf-extract] Summary: {json.dumps(summary, ensure_ascii=False)}")


if __name__ == "__main__":
    main()
