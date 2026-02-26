#!/usr/bin/env bash
# audit_sorry.sh — Check sorry status across the Statlean library.
# Usage: ./scripts/audit_sorry.sh
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

echo "============================================"
echo " StatLean Sorry Audit"
echo "============================================"
echo ""

# 1. Build Verified (should be zero sorry)
echo ">>> Building Statlean.Verified (clean entry point)..."
VERIFIED_SORRY=$(lake build Statlean.Verified 2>&1 | grep -c 'declaration uses.*sorry' || true)
if [ "$VERIFIED_SORRY" -eq 0 ]; then
  echo "    ✅ Statlean.Verified: ZERO sorry"
else
  echo "    ❌ Statlean.Verified: $VERIFIED_SORRY sorry warnings!"
  lake build Statlean.Verified 2>&1 | grep 'sorry'
fi
echo ""

# 2. Check each Proved module individually
echo ">>> Checking Proved modules..."
ALL_CLEAN=true
for mod in \
  Statlean.Basic \
  Statlean.RaoBlackwell_MSE \
  Statlean.Concentration.Basic \
  Statlean.Concentration.Density \
  Statlean.Concentration.EfronSteinProved \
  Statlean.Concentration.GaussianPoincareProved \
  Statlean.Concentration.HermiteOrthogonality \
  Statlean.Concentration.LogSobolevProved \
  Statlean.Concentration.GaussianLipschitzProved \
  Statlean.Concentration.BerryEsseenProved; do
  count=$(lake build "$mod" 2>&1 | grep -c 'declaration uses.*sorry' || true)
  if [ "$count" -eq 0 ]; then
    echo "    ✅ $mod"
  else
    echo "    ❌ $mod ($count sorry warnings)"
    ALL_CLEAN=false
  fi
done
echo ""

# 3. Count declarations in Proved modules
echo ">>> Declaration counts (Proved modules):"
TOTAL=0
for f in \
  Statlean/Basic.lean \
  Statlean/RaoBlackwell_MSE.lean \
  Statlean/Concentration/Basic.lean \
  Statlean/Concentration/Density.lean \
  Statlean/Concentration/EfronSteinProved.lean \
  Statlean/Concentration/GaussianPoincareProved.lean \
  Statlean/Concentration/HermiteOrthogonality.lean \
  Statlean/Concentration/LogSobolevProved.lean \
  Statlean/Concentration/GaussianLipschitzProved.lean \
  Statlean/Concentration/BerryEsseenProved.lean; do
  n=$(grep -cE '^\s*(theorem|lemma|def |noncomputable |private |instance |abbrev )' "$f" 2>/dev/null || true)
  n=${n:-0}
  TOTAL=$((TOTAL + n))
  echo "    $(basename $f): $n"
done
echo "    ────────────"
echo "    Total: $TOTAL verified declarations"
echo ""

# 4. Sorry modules summary
echo ">>> Sorry modules (WIP):"
for f in \
  Statlean/Concentration/EfronStein.lean \
  Statlean/Concentration/GaussianPoincare.lean \
  Statlean/Concentration/LogSobolev.lean \
  Statlean/Concentration/GaussianLipschitz.lean \
  Statlean/Concentration/BerryEsseen.lean; do
  sorry_n=$(grep -c '  sorry$' "$f" 2>/dev/null || echo 0)
  echo "    $(basename $f): $sorry_n sorry"
done
echo ""

echo "============================================"
if [ "$ALL_CLEAN" = true ] && [ "$VERIFIED_SORRY" -eq 0 ]; then
  echo " Result: ALL VERIFIED MODULES CLEAN ✅"
else
  echo " Result: SOME VERIFIED MODULES HAVE SORRY ❌"
fi
echo "============================================"
