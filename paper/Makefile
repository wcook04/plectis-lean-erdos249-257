# Build the exposition PDF.
#
# Preferred: tectonic (self-contained, fetches TeX packages on first run):
#     https://tectonic-typesetting.github.io
# Fallback: a standard TeX Live install (run pdflatex twice for the TOC/refs).

PAPERS = erdos249-257-main-paper erdos249-transport-curvature-companion-note \
  claim-faithful-publication-systems-paper
ALIASES = module-aliases.tex

.PHONY: all check clean sync-root

all: $(PAPERS:%=%.pdf) sync-root

sync-root: $(PAPERS:%=%.pdf)
	@for paper in $(PAPERS); do \
	  cp "$$paper.pdf" "../$$paper.pdf"; \
	done

check: all
	python3 ../scripts/check_rendered_paper_boundary.py

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
