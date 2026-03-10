.PHONY: all clean

MAIN = main

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex
	@if command -v latexmk >/dev/null 2>&1; then \
		latexmk -xelatex -interaction=nonstopmode -halt-on-error $(MAIN).tex; \
	elif command -v tectonic >/dev/null 2>&1; then \
		tectonic $(MAIN).tex; \
	else \
		xelatex -interaction=nonstopmode -halt-on-error $(MAIN).tex && \
		xelatex -interaction=nonstopmode -halt-on-error $(MAIN).tex; \
	fi

clean:
	rm -f *.aux *.log *.nav *.out *.snm *.toc *.vrb *.fls *.fdb_latexmk *.xdv
