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

# 2. Check each verified module individually
echo ">>> Checking verified modules..."
ALL_CLEAN=true
for mod in \
  Statlean.Basic \
  Statlean.Gaussian.Basic \
  Statlean.Gaussian.Stein \
  Statlean.Gaussian.Hermite \
  Statlean.Gaussian.Sobolev \
  Statlean.Variance.RaoBlackwell \
  Statlean.Variance.EfronStein \
  Statlean.Entropy.Basic \
  Statlean.CharFun.Taylor; do
  count=$(lake build "$mod" 2>&1 | grep -c 'declaration uses.*sorry' || true)
  if [ "$count" -eq 0 ]; then
    echo "    ✅ $mod"
  else
    echo "    ❌ $mod ($count sorry warnings)"
    ALL_CLEAN=false
  fi
done
echo ""

# 3. Count declarations in verified modules
echo ">>> Declaration counts (verified modules):"
TOTAL=0
for f in \
  Statlean/Basic.lean \
  Statlean/Gaussian/Basic.lean \
  Statlean/Gaussian/Stein.lean \
  Statlean/Gaussian/Hermite.lean \
  Statlean/Gaussian/Sobolev.lean \
  Statlean/Variance/RaoBlackwell.lean \
  Statlean/Variance/EfronStein.lean \
  Statlean/Entropy/Basic.lean \
  Statlean/CharFun/Taylor.lean; do
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
  Statlean/Gaussian/Poincare.lean \
  Statlean/Entropy/LogSobolev.lean \
  Statlean/SubGaussian/Herbst.lean \
  Statlean/SubGaussian/Lipschitz.lean \
  Statlean/BerryEsseen.lean; do
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
