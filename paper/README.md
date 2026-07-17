<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Papers

For the repository layout, sources of truth, build path, and release
infrastructure, start with the plain-language
[`ARCHITECTURE.md`](../ARCHITECTURE.md) at the repository root. The files in
this directory are authored papers with narrower jobs.

`erdos249-257-main-paper.tex` is the mathematical gateway for readers who do
not read Lean. It states, in ordinary notation, what the Lean development
proves, cites, and leaves open.

Every formal statement links to the exact source
line on GitHub, pinned to the formal-source checkpoint named in
`docs/claims.json`, so a reader can go from a sentence of prose to the checked
proof in one click. The visible link text is theorem-specific: important
anchors use short authored mathematical labels, while the default links turn
the exact declaration name into a spaced, lower-case phrase. The file, line,
and declaration remain in each link target and are verified against the
released source by `scripts/check_release.py`. The document adds no mathematics
beyond what the Lean sources contain; the proofs are the sources it links to.

The manuscript layer (this `.tex` and the rendered PDF) is licensed CC-BY-4.0;
see `REUSE.toml` at the repository root.

There is deliberately no specialist companion note. A former #249-only note
was scrapped and deleted (it survives only in git history) because a
one-sided companion does not give readers a coherent paper set for a
repository about both #249 and #257. Add specialist notes only as a matched
#249/#257 pair; otherwise keep one mathematical gateway paper.

`claim-faithful-publication-systems-paper.tex` is the printable architecture
and access guide. It names the real source files, reviewed records, generated
views, release commands, CI jobs, and human trust boundary, then follows one
claim from Lean proof to public page. The historical checker example appears
only after the architecture and illustrates its coverage limit; it is not a
score and adds no mathematical result.

That ten-page paper is still a draft, not a finished exemplar. Its revision
target and cold-reader loop are recorded in
`claim-faithful-publication-systems-revision-brief.md`.

## Build

```sh
# with tectonic (recommended; fetches TeX packages on first run)
tectonic erdos249-257-main-paper.tex

# or with a TeX Live install
pdflatex erdos249-257-main-paper.tex && pdflatex erdos249-257-main-paper.tex

# or
make
```

The outputs are `erdos249-257-main-paper.pdf` and
`claim-faithful-publication-systems-paper.pdf`; `make` also synchronises the
tracked reader-facing copies at repository root.

## Contents

- The Mersenne–Lambert ladder that places both constants on one line.
- Erdős–Borwein-type irrationality (the #257 direction): full support at every base, plus named infinite-support cases.
- The totient constant `S` (Erdős #249): the unconditional denominator bound, the coprimality reading, and the exact reduction to finite certificates.
- Formalisation architecture and mathematical lessons: how infinite questions are separated from finite kernel-checkable witnesses.
- The formalisation method: how checked statements, finite computations, exact reductions, and the unresolved steps in Erdős #249 and #257 are kept distinct.
- Artefact availability, verification, and a conclusion stating the exact open boundaries once.
- Auxiliary binary-carry criteria and the compact declaration map in appendices.
- The sublogarithmic zero-window theorem for divisor coverage forced by a hypothetical rational support value.
