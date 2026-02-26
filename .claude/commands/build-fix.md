---
description: Build project, diagnose and fix all errors
allowed-tools: Bash(lake:*), Read, Edit, Grep, Glob
argument-hint: [module-name or blank for full build]
---

# Build and Fix Loop

Target: $ARGUMENTS (if blank, build entire project with `lake build`)

## Protocol

### Step 1: Build
```bash
# If module specified:
lake build <module>
# Otherwise:
lake build
```

### Step 2: Parse errors
For each error, extract:
- File path and line number
- Error type (type mismatch, unknown identifier, elaboration failed, etc.)
- The expected vs actual types

### Step 3: Fix (iterate up to 5 rounds)
For each error, apply the appropriate fix:

**Unknown identifier**: Search Mathlib for the correct name. Common renames:
- Check `MeasureTheory.` prefix
- Check `ProbabilityTheory.` prefix
- Check if import is missing

**Type mismatch**: Read the expected and actual types carefully.
- Use `Pi.pow_apply`, `Pi.mul_apply` etc. for pointwise operations
- Check `MemLp` vs `Integrable` confusion
- Check `MeasurableSpace` vs `MeasurableSet` confusion

**Elaboration failed**: Simplify the expression, add type annotations, or break into smaller steps.

**Missing instance**: Add the instance to the theorem hypotheses or find a derivation path.

### Step 4: Verify
After all errors fixed, rebuild to confirm clean build.

## Output
Report what was fixed and any remaining issues.
