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
    """Extract the agent rules block from CLAUDE.md."""
    try:
        with open("CLAUDE.md") as f:
            content = f.read()
        # Find the template block between ``` markers after "段 1:"
        match = re.search(
            r'段 1: 指令头.*?```\n(.*?)```',
            content, re.DOTALL
        )
        if match:
            return match.group(1).strip()
    except Exception:
        pass
    # Fallback: hardcoded minimal rules
    return """约束: 直接写 Lean 代码。不做理论分析。
预验证: echo '#check @API' | lake env lean --stdin
build 上限: ≤ 5 次 lake build
文件读取: 禁止 Read >50 行。用 grep 定位行号后 Read ±15 行。"""

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

    # Clean rules: replace template placeholders with actual values
    rules_filled = rules.replace("<file>", filepath)
    rules_filled = rules_filled.replace("<lemma_name>", f"sorry at L{sorry_line}")
    rules_filled = rules_filled.replace(
        "sorry 数从 N 降到 M（或 \"sorry 关闭\"）",
        f"sorry 数从 {sorry_count} 降到 {sorry_count - 1 if isinstance(sorry_count, int) else '?'}"
    )
    # Remove the generic "目标:" and "验收标准:" lines (we provide our own)
    lines = rules_filled.split('\n')
    lines = [l for l in lines if not l.startswith('目标:') and not l.startswith('验收标准:')
             and not l.startswith('已有 API:')]

    # Build prompt
    prompt = f"""目标: 关闭 {filepath}:{sorry_line} 的 sorry
验收标准: sorry 数从 {sorry_count} 降到 {sorry_count - 1 if isinstance(sorry_count, int) else '?'}
约束: 只修改 {filepath}。直接写 Lean 代码。
已有 API: [由主会话在此补充]

{"chr(10)".join(lines)}

**sorry 上下文** (L{max(1,sorry_line-15)}-L{sorry_line+15}):
{context}

**证明路线**: {route if route else '[由主会话在此补充]'}"""

    print(prompt)

if __name__ == "__main__":
    main()
