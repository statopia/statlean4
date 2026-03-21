#!/usr/bin/env python3
"""Generate subagent prompt from CLAUDE.md template + sorry context.

Usage:
  python3 scripts/gen_agent_prompt.py <file> <sorry_line> [--route "proof route text"]

Output: Complete agent prompt to stdout (pipe to clipboard or use in code).
"""
import sys
import subprocess
import re

def extract_signatures(filepath):
    """Run extract_signatures.py and return output."""
    try:
        r = subprocess.run(
            ["python3", "scripts/extract_signatures.py", filepath],
            capture_output=True, text=True, timeout=10
        )
        return r.stdout[:2000]  # truncate
    except Exception:
        return ""

def read_lines(filepath, start, count):
    """Read specific lines from file."""
    lines = []
    with open(filepath) as f:
        for i, line in enumerate(f, 1):
            if i >= start and i < start + count:
                lines.append(f"{i:>5}→{line.rstrip()}")
            if i >= start + count:
                break
    return "\n".join(lines)

def get_agent_rules():
    """Hardcoded operational rules. Not extracted from CLAUDE.md because
    extraction is fragile and the rules rarely change."""
    return """=== 强制操作规则 ===
约束: 只修改目标文件。直接写 Lean 代码。不做理论分析。
build: ≤ 5 次 lake build。每次 build 前先做 Level 0 或 Level 1。
Level 0: echo '#check @API_Name' | lake env lean --stdin（写 API 前必做）
Level 1: cat > /tmp/test.lean << 'TESTEOF'\\nimport Mathlib\\n...\\nTESTEOF && lake env lean /tmp/test.lean
文件读取: 禁止 Read >50 行。用 grep -n 定位行号后 Read ±15 行。
API 名错误: grep -i '<name>' theme/api_gotchas.tsv → theme/mathlib_full_type_index.tsv
每证完一个子引理立即写入文件。stuck → sorry 暂留 + 继续。"""

def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <file> <sorry_line> [--route 'text']", file=sys.stderr)
        sys.exit(1)

    filepath = sys.argv[1]
    sorry_line = int(sys.argv[2])
    route = ""
    if "--route" in sys.argv:
        idx = sys.argv.index("--route")
        if idx + 1 < len(sys.argv):
            route = sys.argv[idx + 1]

    # Read sorry context (±15 lines)
    context = read_lines(filepath, max(1, sorry_line - 15), 30)

    # Get agent rules from CLAUDE.md
    rules = get_agent_rules()

    # Count current sorry
    try:
        with open(filepath) as f:
            sorry_count = sum(1 for line in f if re.search(r'\bsorry\s*$', line))
    except Exception:
        sorry_count = "?"

    # Build prompt
    target_sorry = sorry_count - 1 if isinstance(sorry_count, int) else '?'
    prompt = f"""目标: 关闭 {filepath}:{sorry_line} 的 sorry
验收标准: sorry 数从 {sorry_count} 降到 {target_sorry}
约束: 只修改 {filepath}。直接写 Lean 代码。
已有 API: [由主会话在此补充]

{rules}

**sorry 上下文** (L{max(1,sorry_line-15)}-L{sorry_line+15}):
{context}

**证明路线**: {route if route else '[由主会话在此补充]'}"""

    print(prompt)

if __name__ == "__main__":
    main()
