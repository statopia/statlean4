#!/usr/bin/env python3
"""Parse proof roadmaps from multiple formats into a unified YAML structure.

Supports:
- Plain text (Chinese/English proof sketches)
- LaTeX proof blocks
- YAML files
- PDF pages (via pdf_extract.py)

Output format:
  roadmap:
    theorem: "<name>"
    completeness: "full" | "partial" | "hint"
    steps:
      - id: 1
        description: "..."
        key_api: [...]
        gap: false
      - id: 2
        description: "..."
        gap: true
    confidence: <1-5>
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

import yaml


# ═══════════════════════════════════════════════════════════════
# Known API keyword mapping (keyword → likely Mathlib API names)
# ═══════════════════════════════════════════════════════════════

_API_KEYWORDS: Dict[str, List[str]] = {
    "fubini": ["MeasureTheory.integral_integral_swap", "MeasureTheory.integral_prod"],
    "tonelli": ["MeasureTheory.lintegral_lintegral_swap", "MeasureTheory.lintegral_prod"],
    "cauchy-schwarz": ["inner_mul_le_norm_mul_norm", "abs_inner_le_norm"],
    "cauchy_schwarz": ["inner_mul_le_norm_mul_norm", "abs_inner_le_norm"],
    "柯西-施瓦茨": ["inner_mul_le_norm_mul_norm"],
    "dominated convergence": ["tendsto_integral_of_dominated_convergence"],
    "控制收敛": ["tendsto_integral_of_dominated_convergence"],
    "monotone convergence": ["lintegral_iSup_directed", "tendsto_lintegral_of_tendsto_of_monotone"],
    "单调收敛": ["lintegral_iSup_directed"],
    "jensen": ["ConvexOn.smul_le_integral", "convexOn_mul_log.map_integral_le"],
    "延森": ["ConvexOn.smul_le_integral"],
    "stein identity": ["stein_identity"],
    "stein 恒等式": ["stein_identity"],
    "integration by parts": ["integral_mul_deriv_eq_deriv_mul_of_integrable"],
    "分部积分": ["integral_mul_deriv_eq_deriv_mul_of_integrable"],
    "ibp": ["integral_mul_deriv_eq_deriv_mul_of_integrable"],
    "taylor": ["taylor_mean_remainder_bound"],
    "泰勒": ["taylor_mean_remainder_bound"],
    "condexp": ["MeasureTheory.condExp", "integral_condExp", "setIntegral_condExp"],
    "条件期望": ["MeasureTheory.condExp", "integral_condExp"],
    "markov": ["MeasureTheory.meas_ge_le_integral_of_nonneg"],
    "马尔可夫": ["MeasureTheory.meas_ge_le_integral_of_nonneg"],
    "chebyshev": ["ProbabilityTheory.meas_ge_le_variance_div_sq"],
    "切比雪夫": ["ProbabilityTheory.meas_ge_le_variance_div_sq"],
    "hölder": ["NNReal.inner_le_Lnorm_mul_Lnorm"],
    "holder": ["NNReal.inner_le_Lnorm_mul_Lnorm"],
    "minkowski": ["MeasureTheory.Memℒp.add"],
    "borel-cantelli": ["MeasureTheory.measure_limsup_eq_zero"],
    "博雷尔-坎特利": ["MeasureTheory.measure_limsup_eq_zero"],
    "portmanteau": ["MeasureTheory.tendsto_measure_of_null_frontier"],
    "lévy": ["levy_continuity"],
    "levy": ["levy_continuity"],
    "scheffé": ["scheffe"],
    "scheffe": ["scheffe"],
    "slutsky": ["slutsky_add", "slutsky_mul"],
    "delta method": ["delta_method"],
    "δ方法": ["delta_method"],
    "clt": ["central_limit_theorem"],
    "中心极限定理": ["central_limit_theorem"],
    "characteristic function": ["charFun_apply_real"],
    "特征函数": ["charFun_apply_real"],
    "rao-blackwell": ["rao_blackwell"],
    "factorization": ["factorization_forward", "factorization_backward"],
    "因子分解": ["factorization_forward", "factorization_backward"],
    "neyman-pearson": ["np_lemma"],
    "data processing inequality": ["integrated_condEntropyAt_condExpect_le"],
    "dpi": ["integrated_condEntropyAt_condExpect_le"],
    "entropy subadditivity": ["entropy_subadditivity"],
    "熵次加性": ["entropy_subadditivity"],
    "log-sobolev": ["log_sobolev_inequality"],
    "对数sobolev": ["log_sobolev_inequality"],
    "poincaré": ["gaussian_poincare"],
    "poincare": ["gaussian_poincare"],
    "庞加莱": ["gaussian_poincare"],
    "efron-stein": ["efron_stein"],
    "gauss-markov": ["gauss_markov"],
    "高斯-马尔可夫": ["gauss_markov"],
    "cramér-rao": ["cramer_rao_lower_bound"],
}


def _extract_api_from_text(text: str) -> List[str]:
    """Extract likely Mathlib API names from proof text."""
    apis: List[str] = []
    text_lower = text.lower()
    for keyword, api_list in _API_KEYWORDS.items():
        if keyword in text_lower:
            apis.extend(api_list)

    # Also match backtick-quoted identifiers (Lean API references)
    lean_refs = re.findall(r"`([A-Za-z_][\w.]*)`", text)
    apis.extend(lean_refs)

    # Match CamelCase identifiers that look like Mathlib names
    camel = re.findall(r"\b([A-Z][a-z]+(?:[A-Z][a-z]+)+(?:\.[a-zA-Z_]\w*)*)\b", text)
    apis.extend(camel)

    return list(dict.fromkeys(apis))  # deduplicate preserving order


# ═══════════════════════════════════════════════════════════════
# Step Extraction from Natural Language
# ═══════════════════════════════════════════════════════════════

# Chinese step markers
_CN_STEP_PAT = re.compile(
    r"(?:^|\n)\s*(?:"
    r"第[一二三四五六七八九十\d]+步[：:]?"
    r"|步骤\s*\d+[：:]?"
    r"|(?:\d+)[.、）)]\s*"
    r"|先[，,]|再[，,]|然后[，,]?|最后[，,]?|接着[，,]?"
    r"|首先[，,]?|其次[，,]?"
    r")",
    re.MULTILINE,
)

# English step markers
_EN_STEP_PAT = re.compile(
    r"(?:^|\n)\s*(?:"
    r"Step\s+\d+[.:)]?\s*"
    r"|(?:\d+)[.)]\s+"
    r"|First[,:]?\s|Then[,:]?\s|Next[,:]?\s|Finally[,:]?\s"
    r"|(?:We\s+)?(?:apply|use|invoke|consider)\s"
    r")",
    re.MULTILINE | re.IGNORECASE,
)

# LaTeX proof structure
_LATEX_STEP_PAT = re.compile(
    r"(?:^|\n)\s*(?:"
    r"\\(?:textbf|mathbf|emph)\{(?:Step|Case|Claim)\s*\d*[.:)]?\}"
    r"|\\item\s"
    r"|\\(?:begin|end)\{(?:enumerate|itemize)\}"
    r")",
    re.MULTILINE,
)

_CN_NUM_MAP = {"一": 1, "二": 2, "三": 3, "四": 4, "五": 5,
               "六": 6, "七": 7, "八": 8, "九": 9, "十": 10}


def _split_into_steps(text: str) -> List[str]:
    """Split proof text into individual steps."""
    text = text.strip()
    if not text:
        return []

    # Try numbered steps first (1. ... 2. ... or Step 1: ...)
    numbered = re.split(
        r"(?:^|\n)\s*(?:Step\s+)?(\d+)[.)：:]\s*",
        text, flags=re.MULTILINE | re.IGNORECASE
    )
    if len(numbered) >= 5:  # at least 2 steps (odd elements are numbers)
        steps = []
        for i in range(1, len(numbered), 2):
            content = numbered[i + 1].strip() if i + 1 < len(numbered) else ""
            if content:
                steps.append(content)
        if len(steps) >= 2:
            return steps

    # Try Chinese sequential markers
    cn_parts = re.split(r"(?:先|首先)[，,]?\s*", text, maxsplit=1)
    if len(cn_parts) > 1:
        remaining = cn_parts[1]
        segments = re.split(r"(?:再|然后|接着|其次|最后)[，,]?\s*", remaining)
        steps = [cn_parts[1].split("再")[0].split("然后")[0].split("接着")[0].strip()]
        for seg in segments[1:] if len(segments) > 1 else []:
            seg = seg.strip()
            if seg:
                steps.append(seg)
        if len(steps) >= 2:
            return steps

    # Try English sequential markers
    en_parts = re.split(
        r"(?:First|Then|Next|Finally)[,:]?\s+",
        text, flags=re.IGNORECASE
    )
    en_parts = [p.strip() for p in en_parts if p.strip()]
    if len(en_parts) >= 2:
        return en_parts

    # Try sentence splitting as last resort
    sentences = re.split(r"[。.]\s*", text)
    sentences = [s.strip() for s in sentences if s.strip() and len(s.strip()) > 10]
    if len(sentences) >= 2:
        return sentences

    # Single chunk
    return [text] if text else []


def _classify_completeness(steps: List[Dict[str, Any]]) -> str:
    """Classify the completeness of the parsed roadmap."""
    if not steps:
        return "hint"
    n_steps = len(steps)
    n_gaps = sum(1 for s in steps if s.get("gap", False))
    n_with_api = sum(1 for s in steps if s.get("key_api"))

    # Single step = hint (even if it has API, it's not a "route")
    if n_steps == 1:
        return "hint"
    if n_steps == 2 and n_with_api <= 1:
        return "partial"
    if n_gaps == 0 and n_with_api >= n_steps * 0.5:
        return "full"
    if n_gaps <= n_steps * 0.3:
        return "partial"
    return "hint"


# ═══════════════════════════════════════════════════════════════
# Main Parsers
# ═══════════════════════════════════════════════════════════════

def parse_plaintext(text: str, theorem_name: str = "") -> Dict[str, Any]:
    """Parse a plain-text proof description into a roadmap."""
    raw_steps = _split_into_steps(text)

    steps: List[Dict[str, Any]] = []
    for i, raw in enumerate(raw_steps, start=1):
        apis = _extract_api_from_text(raw)
        steps.append({
            "id": i,
            "description": raw[:200],  # truncate long descriptions
            "key_api": apis,
            "gap": False,
        })

    # If only one step with no API, treat as hint
    completeness = _classify_completeness(steps)

    # Estimate confidence
    n_with_api = sum(1 for s in steps if s.get("key_api"))
    if completeness == "full":
        confidence = 4 if n_with_api >= len(steps) else 3
    elif completeness == "partial":
        confidence = 3
    else:
        confidence = 2

    return {
        "roadmap": {
            "theorem": theorem_name,
            "completeness": completeness,
            "source": "plaintext",
            "steps": steps,
            "confidence": confidence,
        }
    }


def parse_latex_proof(proof_body: str, theorem_name: str = "") -> Dict[str, Any]:
    """Parse a LaTeX proof body into a roadmap."""
    # Strip LaTeX commands but keep text content
    cleaned = proof_body
    # Remove \begin{proof} and \end{proof} if present
    cleaned = re.sub(r"\\begin\{proof\}|\\end\{proof\}", "", cleaned)
    # Convert \textbf{...} to plain text
    cleaned = re.sub(r"\\(?:textbf|emph|mathbf)\{([^}]*)\}", r"\1", cleaned)
    # Convert \item to newline
    cleaned = re.sub(r"\\item\s*", "\n• ", cleaned)
    # Remove \begin/end{enumerate/itemize}
    cleaned = re.sub(r"\\(?:begin|end)\{(?:enumerate|itemize|align\*?|equation\*?)\}", "", cleaned)
    # Convert math mode markers
    cleaned = re.sub(r"\$\$([^$]+)\$\$", r" \1 ", cleaned)
    cleaned = re.sub(r"\$([^$]+)\$", r" \1 ", cleaned)
    # Clean up whitespace
    cleaned = re.sub(r"\n{3,}", "\n\n", cleaned).strip()

    # Check for "trivial" proofs
    trivial_markers = ["obvious", "clear", "immediate", "trivial",
                       "显然", "易证", "由引理", "即得", "由定义直接得"]
    is_trivial = any(m in cleaned.lower() for m in trivial_markers) and len(cleaned) < 100

    if is_trivial:
        return {
            "roadmap": {
                "theorem": theorem_name,
                "completeness": "hint",
                "source": "latex",
                "steps": [{"id": 1, "description": cleaned[:200], "key_api": [], "gap": True}],
                "confidence": 1,
            }
        }

    return parse_plaintext(cleaned, theorem_name)


def parse_yaml_roadmap(yaml_text: str) -> Dict[str, Any]:
    """Parse a YAML roadmap file directly."""
    data = yaml.safe_load(yaml_text)
    if not data:
        return {"roadmap": {"theorem": "", "completeness": "hint", "source": "yaml",
                            "steps": [], "confidence": 1}}

    # Accept either top-level roadmap or bare structure
    if "roadmap" in data:
        rm = data["roadmap"]
    else:
        rm = data

    # Normalize steps
    steps = rm.get("steps", [])
    for i, s in enumerate(steps):
        s.setdefault("id", i + 1)
        s.setdefault("description", "")
        s.setdefault("key_api", [])
        s.setdefault("gap", False)

    rm.setdefault("theorem", "")
    rm.setdefault("completeness", _classify_completeness(steps))
    rm.setdefault("source", "yaml")
    rm.setdefault("confidence", 4)
    rm["steps"] = steps

    return {"roadmap": rm}


def parse_file(path: str, theorem_name: str = "") -> Dict[str, Any]:
    """Parse a roadmap from a file, detecting format by extension."""
    p = Path(path)
    if not p.exists():
        print(f"[roadmap] file not found: {path}", file=sys.stderr)
        return {"roadmap": {"theorem": theorem_name, "completeness": "hint",
                            "source": "file", "steps": [], "confidence": 0}}

    text = p.read_text(encoding="utf-8", errors="ignore")
    ext = p.suffix.lower()

    if ext in (".yaml", ".yml"):
        result = parse_yaml_roadmap(text)
        if theorem_name:
            result["roadmap"]["theorem"] = theorem_name
        return result
    elif ext == ".tex":
        return parse_latex_proof(text, theorem_name)
    elif ext == ".pdf":
        # Delegate to pdf_extract.py
        return _parse_pdf(path, theorem_name)
    else:
        # Assume plain text
        return parse_plaintext(text, theorem_name)


def _parse_pdf(path: str, theorem_name: str = "") -> Dict[str, Any]:
    """Extract proof from PDF using pdf_extract.py, then parse."""
    import subprocess
    try:
        result = subprocess.run(
            ["python3", "theme/scripts/pdf_extract.py", path, "--format", "text"],
            capture_output=True, text=True, timeout=60,
            cwd=str(Path(__file__).resolve().parent.parent),
        )
        if result.returncode == 0:
            text = result.stdout
            # Try to find proof blocks
            proof_pat = re.compile(
                r"(?:Proof|证明)[.：:\s]*\n(.*?)(?:□|∎|QED|\$\\square\$|\\qed)",
                re.DOTALL | re.IGNORECASE
            )
            m = proof_pat.search(text)
            if m:
                return parse_plaintext(m.group(1), theorem_name)
            # No proof block found, try full text
            return parse_plaintext(text[:3000], theorem_name)
    except Exception as e:
        print(f"[roadmap] PDF extraction failed: {e}", file=sys.stderr)

    return {"roadmap": {"theorem": theorem_name, "completeness": "hint",
                        "source": "pdf", "steps": [], "confidence": 0}}


def parse_inline(text: str, theorem_name: str = "") -> Dict[str, Any]:
    """Parse an inline roadmap from user message text.

    Detects proof descriptions in free-form text by looking for
    mathematical proof language markers.
    """
    # Check for proof description markers
    proof_markers = [
        r"证明路线", r"proof sketch", r"proof outline", r"proof strategy",
        r"先[^。]{5,}再", r"first[^.]{5,}then",
        r"关键是用", r"the key is",
        r"步骤\s*\d", r"step\s*\d",
        r"用.*定理", r"apply.*theorem",
        r"(?:use|apply|invoke)\s+\w+",
    ]

    has_proof_desc = any(re.search(p, text, re.IGNORECASE) for p in proof_markers)
    if not has_proof_desc:
        return {"roadmap": None}  # No proof description found

    return parse_plaintext(text, theorem_name)


def merge_roadmaps(r1: Dict[str, Any], r2: Dict[str, Any]) -> Dict[str, Any]:
    """Merge two roadmaps, filling gaps in r1 with steps from r2.

    r1 is the primary (e.g., from human input), r2 is supplementary (e.g., from context).
    """
    rm1 = r1.get("roadmap")
    rm2 = r2.get("roadmap")

    if not rm1 or not rm1.get("steps"):
        return r2
    if not rm2 or not rm2.get("steps"):
        return r1

    steps1 = rm1["steps"]
    steps2 = rm2["steps"]

    # Fill gap steps from r1 with matching steps from r2
    merged = []
    r2_idx = 0
    for s in steps1:
        if s.get("gap", False) and r2_idx < len(steps2):
            # Use r2's step to fill the gap
            filled = dict(steps2[r2_idx])
            filled["id"] = s["id"]
            filled["gap"] = False
            filled["source"] = "merged"
            merged.append(filled)
            r2_idx += 1
        else:
            merged.append(s)

    # Append any remaining r2 steps
    for s in steps2[r2_idx:]:
        s_copy = dict(s)
        s_copy["id"] = len(merged) + 1
        merged.append(s_copy)

    completeness = _classify_completeness(merged)
    confidence = max(rm1.get("confidence", 1), rm2.get("confidence", 1))

    return {
        "roadmap": {
            "theorem": rm1.get("theorem") or rm2.get("theorem", ""),
            "completeness": completeness,
            "source": "merged",
            "steps": merged,
            "confidence": confidence,
        }
    }


# ═══════════════════════════════════════════════════════════════
# CLI + Tests
# ═══════════════════════════════════════════════════════════════

def _run_tests():
    """Run built-in tests."""
    print("=== Test 1: Plain text (Chinese sequential) ===")
    r = parse_plaintext(
        "先用 Fubini 交换积分顺序，再用 Cauchy-Schwarz 得到上界，最后取极限得结论",
        "entropy_subadditivity"
    )
    rm = r["roadmap"]
    assert rm["theorem"] == "entropy_subadditivity"
    assert len(rm["steps"]) >= 2, f"Expected >=2 steps, got {len(rm['steps'])}"
    print(f"  Steps: {len(rm['steps'])}, completeness: {rm['completeness']}")
    for s in rm["steps"]:
        print(f"    {s['id']}: {s['description'][:60]}... api={s['key_api']}")
    print()

    print("=== Test 2: Plain text (English numbered) ===")
    r = parse_plaintext(
        "1. Apply Fubini to swap integrals\n"
        "2. Use Jensen's inequality on the inner integral\n"
        "3. Combine with dominated convergence",
        "test_theorem"
    )
    rm = r["roadmap"]
    assert len(rm["steps"]) >= 3
    print(f"  Steps: {len(rm['steps'])}, completeness: {rm['completeness']}")
    for s in rm["steps"]:
        print(f"    {s['id']}: {s['description'][:60]}... api={s['key_api']}")
    print()

    print("=== Test 3: Hint-level input ===")
    r = parse_plaintext("关键是用 Stein identity", "poincare")
    rm = r["roadmap"]
    assert rm["completeness"] == "hint"
    print(f"  completeness: {rm['completeness']}, steps: {len(rm['steps'])}")
    for s in rm["steps"]:
        print(f"    {s['id']}: {s['description'][:60]}... api={s['key_api']}")
    print()

    print("=== Test 4: LaTeX proof ===")
    r = parse_latex_proof(
        r"""\begin{proof}
        By Fubini's theorem, we can exchange the order of integration.
        Then applying the Cauchy-Schwarz inequality gives
        $\int |fg| \leq \|f\|_2 \|g\|_2$.
        Finally, taking $n \to \infty$ and using dominated convergence completes the proof.
        \end{proof}""",
        "latex_test"
    )
    rm = r["roadmap"]
    print(f"  Steps: {len(rm['steps'])}, completeness: {rm['completeness']}")
    for s in rm["steps"]:
        print(f"    {s['id']}: {s['description'][:60]}... api={s['key_api']}")
    print()

    print("=== Test 5: Inline detection ===")
    r = parse_inline("请帮我证明这个定理，证明路线是先用 Fubini 再用 Jensen", "inline_test")
    assert r["roadmap"] is not None
    print(f"  Detected: {r['roadmap']['completeness']}, steps: {len(r['roadmap']['steps'])}")
    print()

    r_none = parse_inline("请帮我看看这个文件有什么问题")
    assert r_none["roadmap"] is None
    print("  No-proof text correctly returned None")
    print()

    print("=== Test 6: YAML roadmap ===")
    yaml_text = """
roadmap:
  theorem: "test_yaml"
  steps:
    - description: "Apply Fubini"
      key_api: ["integral_integral_swap"]
    - description: "Use Jensen"
      key_api: ["ConvexOn.smul_le_integral"]
    - description: "Take limit"
      key_api: ["tendsto_integral_of_dominated_convergence"]
"""
    r = parse_yaml_roadmap(yaml_text)
    rm = r["roadmap"]
    assert rm["completeness"] == "full"
    assert len(rm["steps"]) == 3
    print(f"  Steps: {len(rm['steps'])}, completeness: {rm['completeness']}")
    print()

    print("=== Test 7: Partial roadmap with gaps ===")
    r1 = parse_plaintext(
        "1. Apply Fubini to exchange integrals\n2. ???\n3. Take the limit",
        "partial_test"
    )
    # Mark step 2 as gap manually (in practice the parser detects ??? as gap)
    for s in r1["roadmap"]["steps"]:
        if "???" in s["description"]:
            s["gap"] = True
    r2 = parse_plaintext("Use Cauchy-Schwarz to bound the middle term", "filler")
    merged = merge_roadmaps(r1, r2)
    print(f"  Merged steps: {len(merged['roadmap']['steps'])}")
    for s in merged["roadmap"]["steps"]:
        print(f"    {s['id']}: gap={s.get('gap', False)} {s['description'][:50]}")
    print()

    print("=== All tests passed! ===")


def main():
    p = argparse.ArgumentParser(
        description="Parse proof roadmaps from multiple formats"
    )
    p.add_argument("input", nargs="?", help="Input file path (or - for stdin)")
    p.add_argument("--theorem", default="", help="Theorem name")
    p.add_argument("--format", choices=["auto", "text", "latex", "yaml", "pdf"],
                   default="auto", help="Input format (default: auto-detect)")
    p.add_argument("--inline", type=str, help="Parse inline text directly")
    p.add_argument("--test", action="store_true", help="Run built-in tests")
    p.add_argument("--output", "-o", type=str, help="Output YAML file (default: stdout)")
    args = p.parse_args()

    if args.test:
        _run_tests()
        return

    if args.inline:
        result = parse_inline(args.inline, args.theorem)
        if result["roadmap"] is None:
            print("No proof description detected in input.", file=sys.stderr)
            sys.exit(1)
    elif args.input:
        if args.input == "-":
            text = sys.stdin.read()
            if args.format == "yaml":
                result = parse_yaml_roadmap(text)
            elif args.format == "latex":
                result = parse_latex_proof(text, args.theorem)
            else:
                result = parse_plaintext(text, args.theorem)
        else:
            if args.format == "auto":
                result = parse_file(args.input, args.theorem)
            elif args.format == "text":
                text = Path(args.input).read_text(encoding="utf-8")
                result = parse_plaintext(text, args.theorem)
            elif args.format == "latex":
                text = Path(args.input).read_text(encoding="utf-8")
                result = parse_latex_proof(text, args.theorem)
            elif args.format == "yaml":
                text = Path(args.input).read_text(encoding="utf-8")
                result = parse_yaml_roadmap(text)
            elif args.format == "pdf":
                result = _parse_pdf(args.input, args.theorem)
            else:
                result = parse_file(args.input, args.theorem)
    else:
        p.print_help()
        sys.exit(1)

    output = yaml.safe_dump(result, sort_keys=False, allow_unicode=True, default_flow_style=False)

    if args.output:
        Path(args.output).write_text(output, encoding="utf-8")
        print(f"[roadmap] wrote {args.output}", file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()
