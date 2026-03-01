SHELL := /bin/bash

ROOT ?= ..
THEME_DIR ?= .
INPUT_DIR ?= $(THEME_DIR)/input
OUT_DIR ?= $(THEME_DIR)/out
TEX ?= $(ROOT)/output.tex
# GNU Make has a built-in default `TEX=tex`; override that default only.
ifeq ($(origin TEX), default)
TEX := $(ROOT)/output.tex
endif
PDF ?=
CONCEPTS ?=
NO_DEPS ?=
FORCE_CLAUDE ?=
AGENT_BACKEND ?= claude
PROVE_BUDGET ?= 3600
PROVE_MAX_ITERS ?= 10
PROVE_DEPTH ?= deep
MAX_PARALLEL ?= 3

.PHONY: formalize resolve ingest plan generate infra-audit build-check sync-backlog prove gate clean \
        from-tex tex-formalize from-pdf pdf-formalize \
        prove-fallback refresh-index auto-shelve \
        formalize-codex formalize-claude

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
	    $(if $(FORCE_CLAUDE),--force-claude) \
	    $(if $(FORCE_AI),--force-ai --ai-backend $(AGENT_BACKEND)) ; \
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
	@python3 $(THEME_DIR)/scripts/prove_select_targets.py \
	    --repo-root "$(ROOT)" \
	    --manifest "$(OUT_DIR)/manifest.json" \
	    --max-targets $(MAX_PARALLEL) \
	    --output "$(OUT_DIR)/prove_targets.json"
	@echo "[prove] targets ready — $(AGENT_BACKEND) backend will dispatch agents"

gate:
	$(THEME_DIR)/scripts/gate.sh "$(ROOT)"

# ══════════════════════════════════════════════════════════
# Entry points — user-facing commands
# ══════════════════════════════════════════════════════════

# PDF → LaTeX extraction (MinerU)
from-pdf:
	@if [ -z "$(PDF)" ]; then echo "Usage: make from-pdf PDF=<file.pdf|keyword>"; exit 1; fi
	$(THEME_DIR)/scripts/pdf_extract.sh "$(PDF)" "$(INPUT_DIR)"

# PDF → full formalization (one command does everything)
pdf-formalize: TEX := $(INPUT_DIR)/paper.tex
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
	AGENT_BACKEND=$(AGENT_BACKEND) $(THEME_DIR)/scripts/prove_loop.sh "$(ROOT)"

# Convenience targets for specific backends
formalize-codex:
	$(MAKE) formalize AGENT_BACKEND=codex

formalize-claude:
	$(MAKE) formalize AGENT_BACKEND=claude

# Refresh Mathlib API index (run after Mathlib upgrade)
refresh-index:
	cd "$(ROOT)" && lake env lean scripts/gen_mathlib_index.lean > theme/mathlib_api_index.md

auto-shelve:
	python3 $(THEME_DIR)/scripts/auto_shelve.py --repo-root "$(ROOT)" --fix

clean:
	rm -rf "$(OUT_DIR)"
