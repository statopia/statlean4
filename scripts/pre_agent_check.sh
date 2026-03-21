#!/bin/bash
# Pre-agent launch checklist. Run before every Agent() call.
# Usage: bash scripts/pre_agent_check.sh <file> <sorry_line>
#
# Outputs: context block ready to paste into agent prompt.
# Also checks: did you search proof_knowledge? did you grep indexes?

FILE="$1"
LINE="$2"

if [ -z "$FILE" ] || [ -z "$LINE" ]; then
    echo "Usage: $0 <file> <sorry_line>"
    exit 1
fi

echo "=== PRE-AGENT CHECKLIST ==="

# 1. Sorry count
SORRY_COUNT=$(grep -c ' sorry$' "$FILE" 2>/dev/null || echo "?")
echo "Current sorry count in $FILE: $SORRY_COUNT"

# 2. Extract sorry context (±15 lines)
echo ""
echo "=== SORRY CONTEXT (L$((LINE-15))-L$((LINE+15))) ==="
sed -n "$((LINE-15)),$((LINE+15))p" "$FILE" 2>/dev/null | cat -n

# 3. Check proof_knowledge for matching patterns
echo ""
echo "=== PROOF_KNOWLEDGE MATCHES ==="
# Extract keywords from the sorry context
CONTEXT=$(sed -n "$((LINE-5)),$((LINE+5))p" "$FILE" 2>/dev/null)
for kw in integral cdf charFun Fourier bracket kernel smoothing sSup iSup; do
    if echo "$CONTEXT" | grep -qi "$kw"; then
        MATCHES=$(grep -i "$kw" theme/proof_knowledge.yaml 2>/dev/null | head -3)
        if [ -n "$MATCHES" ]; then
            echo "  [$kw]: $MATCHES"
        fi
    fi
done

# 4. Stuck count from backlog
echo ""
echo "=== STUCK ROUNDS ==="
grep -A2 "$(basename $FILE .lean)" theme/input/sorry_backlog.yaml 2>/dev/null | grep -i "stuck\|round" | head -3
echo "(If stuck ≥ 3: R6 required. If stuck ≥ 5: counterexample search required.)"

# 5. Reminder
echo ""
echo "=== REMINDERS ==="
echo "- Agent prompt must start with operational rules (段 1)"
echo "- Include this context block as 段 2"
echo "- Proof route ≤ 200 words as 段 3"
echo "- After agent returns: grep -c ' sorry$' $FILE"
