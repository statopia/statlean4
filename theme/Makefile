SHELL := /bin/bash

ROOT ?= ..
THEME_DIR ?= .
INPUT_DIR ?= $(THEME_DIR)/input
OUT_DIR ?= $(THEME_DIR)/out
TEX ?= $(ROOT)/output.tex
PDF ?=
CONCEPTS ?=
NO_DEPS ?=
NO_CLAUDE ?=
PROVE_BUDGET ?= 3600
PROVE_MAX_ITERS ?= 10
PROVE_DEPTH ?= deep

.PHONY: formalize resolve ingest plan generate infra-audit build-check sync-backlog prove gate clean \
        from-tex tex-formalize from-pdf pdf-formalize \
        prove-fallback refresh-index

# ══════════════════════════════════════════════════════════
# Full pipeline: LaTeX → Lean → sync-backlog → prove → gate
# ══════════════════════════════════════════════════════════
formalize: resolve ingest plan generate infra-audit build-check sync-backlog prove gate

# Concept resolution: CONCEPTS → theorems.yaml (no-op if CONCEPTS is empty)
resolve:
	@if [ -n "$(CONCEPTS)" ]; then \
	  python3 $(THEME_DIR)/scripts/resolve_concepts.py \
	    --concepts "$(CONCEPTS)" \
	    --output "$(INPUT_DIR)/theorems.yaml" \
	    $(if $(PDF),--pdf "$(PDF)") \
	    $(if $(NO_DEPS),--no-deps) \
	    $(if $(NO_CLAUDE),--no-claude) ; \
	fi

ingest:
	$(THEME_DIR)/scripts/ingest.sh "$(INPUT_DIR)" "$(OUT_DIR)"

plan:
	$(THEME_DIR)/scripts/plan.sh "$(INPUT_DIR)" "$(OUT_DIR)"

generate:
	$(THEME_DIR)/scripts/generate.sh "$(INPUT_DIR)" "$(OUT_DIR)" "$(ROOT)"

infra-audit:
	cd "$(ROOT)" && python3 theme/scripts/infra_audit.py .

build-check:
	@echo "[build-check] verifying generated code compiles..."
	@cd "$(ROOT)" && lake build 2>&1 | tail -5 || \
	  { echo "[build-check] FAIL: generated code does not compile — aborting pipeline"; exit 1; }

sync-backlog:
	cd "$(ROOT)" && python3 theme/scripts/sync_sorry_backlog.py

prove:
	@if [ "$(PROVE_DEPTH)" = "shallow" ]; then \
	  echo "[prove] PROVE_DEPTH=shallow, skipping"; \
	else \
	  PROVE_BUDGET=$(PROVE_BUDGET) \
	  MAX_ITERS=$(PROVE_MAX_ITERS) \
	  MAX_PARALLEL=3 \
	  MANIFEST=$(OUT_DIR)/manifest.json \
	  $(THEME_DIR)/scripts/prove_loop.sh "$(ROOT)" || \
	    echo "[prove] prove loop ended with remaining sorry (non-blocking)"; \
	fi

gate:
	$(THEME_DIR)/scripts/gate.sh "$(ROOT)"

# ══════════════════════════════════════════════════════════
# Entry points — user-facing commands
# ══════════════════════════════════════════════════════════

# PDF → LaTeX extraction (MinerU)
from-pdf:
	@if [ -z "$(PDF)" ]; then echo "Usage: make from-pdf PDF=<file.pdf>"; exit 1; fi
	$(THEME_DIR)/scripts/pdf_extract.sh "$(PDF)" "$(INPUT_DIR)"

# PDF → full formalization (one command does everything)
pdf-formalize: from-pdf from-tex formalize

# LaTeX → structured YAML
from-tex:
	$(THEME_DIR)/scripts/from_tex.sh "$(TEX)" "$(INPUT_DIR)"

# LaTeX → full formalization
tex-formalize: from-tex formalize

# ══════════════════════════════════════════════════════════
# Utilities
# ══════════════════════════════════════════════════════════

# Fallback prove loop (CI / non-Claude-Code environments)
prove-fallback:
	$(THEME_DIR)/scripts/prove_loop.sh "$(ROOT)"

# Refresh Mathlib API index (run after Mathlib upgrade)
refresh-index:
	cd "$(ROOT)" && lake env lean scripts/gen_mathlib_index.lean > theme/mathlib_api_index.md

clean:
	rm -rf "$(OUT_DIR)"
