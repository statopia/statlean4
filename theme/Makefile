SHELL := /bin/bash

ROOT ?= ..
THEME_DIR ?= .
INPUT_DIR ?= $(THEME_DIR)/input
OUT_DIR ?= $(THEME_DIR)/out
TEX ?= $(ROOT)/output.tex
PDF ?=
# Agent backend for prove-loop: "codex" (default) or "claude"
export AGENT_BACKEND ?= codex

.PHONY: formalize ingest plan generate prove-loop promote stabilize gate clean \
        from-tex tex-formalize from-pdf pdf-formalize \
        formalize-claude formalize-parallel prove-sorry refresh-index

# ══════════════════════════════════════════════════════════
# Full pipeline: LaTeX → Lean → prove → promote → gate
# ══════════════════════════════════════════════════════════
formalize: ingest plan generate prove-loop promote stabilize gate

ingest:
	$(THEME_DIR)/scripts/ingest.sh "$(INPUT_DIR)" "$(OUT_DIR)"

plan:
	$(THEME_DIR)/scripts/plan.sh "$(INPUT_DIR)" "$(OUT_DIR)"

generate:
	$(THEME_DIR)/scripts/generate.sh "$(INPUT_DIR)" "$(OUT_DIR)" "$(ROOT)"

prove-loop:
	$(THEME_DIR)/scripts/prove_loop.sh "$(OUT_DIR)" "$(ROOT)"

promote:
	$(THEME_DIR)/scripts/promote.sh "$(OUT_DIR)" "$(ROOT)"

stabilize:
	$(THEME_DIR)/scripts/stabilize.sh "$(OUT_DIR)" "$(ROOT)"

gate:
	$(THEME_DIR)/scripts/gate.sh "$(OUT_DIR)" "$(ROOT)"

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
# Shortcuts
# ══════════════════════════════════════════════════════════

# Full pipeline with Claude backend
formalize-claude:
	AGENT_BACKEND=claude $(MAKE) formalize

# Parallel Claude — one agent per theorem ID
formalize-parallel:
	AGENT_BACKEND=claude PARALLEL=1 $(MAKE) formalize

# Sorry elimination on existing Statlean/ modules
prove-sorry:
	cd "$(ROOT)" && python3 scripts/auto_prove.py

# Refresh Mathlib API index (run after Mathlib upgrade)
refresh-index:
	cd "$(ROOT)" && lake env lean scripts/gen_mathlib_index.lean > theme/mathlib_api_index.md

clean:
	rm -rf "$(OUT_DIR)"
