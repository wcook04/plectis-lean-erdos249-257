# Build the exposition PDF.
#
# Preferred: tectonic (self-contained, fetches TeX packages on first run):
#     https://tectonic-typesetting.github.io
# Fallback: a standard TeX Live install (run pdflatex twice for the TOC/refs).

PAPER = erdos249-257-exposition

.PHONY: all clean

all: $(PAPER).pdf

$(PAPER).pdf: $(PAPER).tex
	@if command -v tectonic >/dev/null 2>&1; then \
	  tectonic $(PAPER).tex ; \
	else \
	  pdflatex $(PAPER).tex && pdflatex $(PAPER).tex ; \
	fi

clean:
	rm -f $(PAPER).pdf $(PAPER).aux $(PAPER).log $(PAPER).out $(PAPER).toc
