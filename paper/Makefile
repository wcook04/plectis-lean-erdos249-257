# Build the exposition PDF.
#
# Preferred: tectonic (self-contained, fetches TeX packages on first run):
#     https://tectonic-typesetting.github.io
# Fallback: a standard TeX Live install (run pdflatex twice for the TOC/refs).

PAPERS = erdos249-257-exposition erdos249-transport-curvature
ALIASES = module-aliases.tex

.PHONY: all clean

all: $(PAPERS:%=%.pdf)

$(ALIASES): $(PAPERS:%=%.tex) ../scripts/build_paper_module_aliases.py
	python3 ../scripts/build_paper_module_aliases.py

%.pdf: %.tex $(ALIASES)
	@if command -v tectonic >/dev/null 2>&1; then \
	  tectonic $< ; \
	else \
	  pdflatex $< && pdflatex $< ; \
	fi

clean:
	rm -f $(PAPERS:%=%.pdf) $(PAPERS:%=%.aux) $(PAPERS:%=%.log) \
	  $(PAPERS:%=%.out) $(PAPERS:%=%.toc)
