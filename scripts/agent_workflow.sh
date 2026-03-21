#!/bin/bash
# Unified agent workflow script. Replaces manual checklist.
# Usage:
#   agent_workflow.sh pre  <file> <sorry_line>     -- before launching agent
#   agent_workflow.sh post <file> <before_sorry>   -- after agent returns
#   agent_workflow.sh commit <file> <message>       -- auto-commit if sorry reduced
#   agent_workflow.sh stuck <sorry_id>              -- increment stuck count + check R6

set -e
CMD="$1"
shift

case "$CMD" in

pre)
    # === PRE-AGENT: generate context + check knowledge + check stuck ===
    FILE="$1"; LINE="$2"
    [ -z "$FILE" ] && { echo "Usage: agent_workflow.sh pre <file> <sorry_line>"; exit 1; }

    echo "=== SORRY CONTEXT ==="
    SORRY_COUNT=$(grep -c ' sorry$' "$FILE" 2>/dev/null || echo "?")
    echo "File: $FILE | Sorry: $SORRY_COUNT | Target line: $LINE"
    echo ""
    sed -n "$((LINE-15)),$((LINE+15))p" "$FILE" 2>/dev/null

    echo ""
    echo "=== PROOF_KNOWLEDGE MATCHES ==="
    CONTEXT=$(sed -n "$((LINE-5)),$((LINE+5))p" "$FILE" 2>/dev/null)
    FOUND=0
    for kw in integral cdf charFun Fourier bracket kernel smoothing sSup iSup convolution Lipschitz density; do
        if echo "$CONTEXT" | grep -qi "$kw"; then
            M=$(grep -i "$kw" theme/proof_knowledge.yaml 2>/dev/null | head -2)
            if [ -n "$M" ]; then echo "  [$kw]: $M"; FOUND=1; fi
        fi
    done
    [ "$FOUND" = 0 ] && echo "  (no matches)"

    echo ""
    echo "=== STUCK STATUS ==="
    STUCK=$(grep -A5 "$(basename $FILE .lean)" theme/input/sorry_backlog.yaml 2>/dev/null | grep -o 'stuck_rounds: [0-9]*' | grep -o '[0-9]*')
    STUCK=${STUCK:-0}
    echo "stuck_rounds: $STUCK"
    if [ "$STUCK" -ge 5 ]; then
        echo "⚠️  STUCK ≥ 5: COUNTEREXAMPLE SEARCH REQUIRED before next agent"
    elif [ "$STUCK" -ge 3 ]; then
        echo "⚠️  STUCK ≥ 3: R6 REQUIRED (WebSearch + engineering route)"
    fi
    ;;

post)
    # === POST-AGENT: check sorry + classify + suggest next action ===
    FILE="$1"; BEFORE="$2"
    [ -z "$FILE" ] && { echo "Usage: agent_workflow.sh post <file> <before_sorry>"; exit 1; }
    # Find sorry line for context extraction
    LINE_HINT=$(grep -n ' sorry$' "$FILE" 2>/dev/null | head -1 | cut -d: -f1)
    LINE_HINT=${LINE_HINT:-1}

    AFTER=$(grep -c ' sorry$' "$FILE" 2>/dev/null || echo "?")
    echo "=== RESULT: sorry $BEFORE → $AFTER ==="

    if [ "$AFTER" -lt "$BEFORE" ] 2>/dev/null; then
        echo "✅ SORRY REDUCED. Actions:"
        echo "  1. lake build <module> (verify)"
        echo "  2. git add $FILE && git commit -m 'prove: ...'"
        echo "  3. Run: agent_workflow.sh commit $FILE 'prove: <lemma>'"
    else
        echo "❌ SORRY NOT REDUCED."
        echo ""
        # Check stuck count and output EXACT next commands
        STUCK=$(grep -A5 "$(basename $FILE .lean)" theme/input/sorry_backlog.yaml 2>/dev/null | grep -o 'stuck_rounds: [0-9]*' | grep -o '[0-9]*')
        STUCK=${STUCK:-0}
        NEW_STUCK=$((STUCK + 1))
        echo "stuck_rounds: $STUCK → $NEW_STUCK"
        echo ""

        if [ "$NEW_STUCK" -ge 3 ]; then
            # Extract keywords from sorry context for WebSearch query
            KEYWORDS=$(sed -n "$((LINE_HINT-5)),$((LINE_HINT+5))p" "$FILE" 2>/dev/null | grep -oE '[A-Za-z]{5,}' | sort -u | head -5 | tr '\n' ' ')

            echo "╔══════════════════════════════════════════════════════╗"
            echo "║  R6 REQUIRED: WebSearch BEFORE next agent launch    ║"
            echo "║  Copy-paste these commands:                         ║"
            echo "╚══════════════════════════════════════════════════════╝"
            echo ""
            echo '>>> WebSearch "Lean 4 Mathlib '"$KEYWORDS"'proof formalization 2025 2026"'
            echo '>>> WebSearch "'"$KEYWORDS"'elementary proof technique arXiv"'
            echo ""
            echo "After WebSearch: python3 scripts/gen_agent_prompt.py $FILE <line> --route '<from search>'"
        fi

        if [ "$NEW_STUCK" -ge 5 ]; then
            echo ""
            echo "╔══════════════════════════════════════════════════════╗"
            echo "║  COUNTEREXAMPLE SEARCH REQUIRED                    ║"
            echo "║  Check: is the sorry statement actually TRUE?      ║"
            echo "╚══════════════════════════════════════════════════════╝"
        fi

        echo ""
        echo "NEXT STEPS (in order):"
        echo "  1. agent_workflow.sh stuck <sorry_id>"
        if [ "$NEW_STUCK" -ge 3 ]; then
            echo "  2. DO THE WEBSEARCH ABOVE (mandatory, not optional)"
            echo "  3. THEN gen_agent_prompt.py with route from search"
        else
            echo "  2. Extract findings → add to next prompt"
            echo "  3. gen_agent_prompt.py $FILE <line> --route '...'"
        fi
    fi
    ;;

commit)
    # === AUTO-COMMIT: verify build + commit + push ===
    FILE="$1"; MSG="$2"
    [ -z "$MSG" ] && { echo "Usage: agent_workflow.sh commit <file> '<message>'"; exit 1; }

    echo "Building..."
    MODULE=$(echo "$FILE" | sed 's|/|.|g' | sed 's|\.lean$||')
    if lake build "$MODULE" 2>&1 | tail -3 | grep -q "Build completed successfully"; then
        echo "✅ Build OK"
        git add "$FILE"
        git commit -m "$MSG

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>"
        echo "✅ Committed. Push with: git push origin main"
    else
        echo "❌ Build FAILED. Fix before committing."
    fi
    ;;

stuck)
    # === INCREMENT STUCK COUNT ===
    SORRY_ID="$1"
    [ -z "$SORRY_ID" ] && { echo "Usage: agent_workflow.sh stuck <sorry_id>"; exit 1; }

    echo "Incrementing stuck_rounds for $SORRY_ID..."
    # Simple: just print the instruction since YAML editing is fragile in bash
    echo "TODO: In theme/input/sorry_backlog.yaml, find '$SORRY_ID' and increment stuck_rounds"
    echo ""
    STUCK=$(grep -A5 "$SORRY_ID" theme/input/sorry_backlog.yaml 2>/dev/null | grep -o 'stuck_rounds: [0-9]*' | grep -o '[0-9]*')
    STUCK=${STUCK:-0}
    NEW=$((STUCK + 1))
    echo "Current: $STUCK → New: $NEW"
    if [ "$NEW" -ge 5 ]; then
        echo "⚠️  COUNTEREXAMPLE SEARCH REQUIRED"
    elif [ "$NEW" -ge 3 ]; then
        echo "⚠️  R6 REQUIRED (WebSearch for engineering route)"
    fi
    ;;

*)
    echo "Usage: agent_workflow.sh {pre|post|commit|stuck} <args>"
    echo "  pre  <file> <sorry_line>    -- before launching agent"
    echo "  post <file> <before_sorry>  -- after agent returns"
    echo "  commit <file> <message>     -- auto-commit if build OK"
    echo "  stuck <sorry_id>            -- increment stuck counter"
    ;;
esac
