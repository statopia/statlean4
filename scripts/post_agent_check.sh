#!/bin/bash
# Post-agent return checklist. Run after every agent completes.
# Usage: bash scripts/post_agent_check.sh <file> <expected_sorry_before> <agent_duration_s> <agent_tokens> <agent_builds>
#
# Checks sorry count, suggests complexity classification, prompts for knowledge ingestion.

FILE="$1"
BEFORE="$2"
DURATION="${3:-0}"
TOKENS="${4:-0}"
BUILDS="${5:-0}"

if [ -z "$FILE" ] || [ -z "$BEFORE" ]; then
    echo "Usage: $0 <file> <expected_sorry_before> [duration_s] [tokens] [builds]"
    exit 1
fi

echo "=== POST-AGENT CHECKLIST ==="

# 1. Check sorry count
AFTER=$(grep -c ' sorry$' "$FILE" 2>/dev/null || echo "?")
echo "Sorry: $BEFORE → $AFTER"

if [ "$AFTER" -lt "$BEFORE" ] 2>/dev/null; then
    echo "✅ Sorry reduced! Commit this."

    # 2. Classify complexity for proof_knowledge
    if [ "$BUILDS" -le 1 ] && [ "$TOKENS" -lt 50000 ] 2>/dev/null; then
        echo "📊 Complexity: LOW (≤1 build, <50K tokens)"
        echo "   → Record in proof_knowledge.yaml: workflow: 'Low complexity'"
    elif [ "$BUILDS" -le 5 ] 2>/dev/null; then
        echo "📊 Complexity: MEDIUM ($BUILDS builds, ${TOKENS}K tokens)"
    else
        echo "📊 Complexity: HIGH ($BUILDS builds, ${TOKENS}K tokens)"
        echo "   → Record in proof_knowledge.yaml: workflow: 'High complexity, provide skeleton'"
    fi
else
    echo "❌ Sorry NOT reduced."
    echo "   → stuck_rounds += 1"
    echo "   → If stuck ≥ 3: trigger R6 (WebSearch)"
    echo "   → If stuck ≥ 5: trigger counterexample search"
    echo "   → Consider: main session writes code (limit 1 build)"
fi

# 3. Check for new anti-patterns
echo ""
echo "=== ANTI-PATTERN CHECK ==="
echo "Did the agent discover any dead-end routes? If yes:"
echo "  python3 scripts/ingest_knowledge.py --input /tmp/new_knowledge.yaml"

# 4. Build check
echo ""
echo "=== BUILD CHECK ==="
echo "Run: lake build $(echo $FILE | sed 's|/|.|g' | sed 's|\.lean$||')"
