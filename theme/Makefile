SHELL := /bin/bash

ROOT ?= ..
THEME_DIR ?= .
INPUT_DIR ?= $(THEME_DIR)/input
OUT_DIR ?= $(THEME_DIR)/out
TEX ?= $(ROOT)/output.tex
# Agent backend for prove-loop: "codex" (default) or "claude"
export AGENT_BACKEND ?= codex

.PHONY: formalize ingest plan generate prove-loop promote stabilize gate clean from-tex tex-formalize formalize-claude

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

from-tex:
	$(THEME_DIR)/scripts/from_tex.sh "$(TEX)" "$(INPUT_DIR)"

tex-formalize: from-tex formalize

# Shortcut: run full pipeline with Claude as agent backend
formalize-claude:
	AGENT_BACKEND=claude $(MAKE) formalize

clean:
	rm -rf "$(OUT_DIR)"
