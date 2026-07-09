<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Exposition

A guide to this repository for mathematicians who do not read Lean.

`erdos249-257-exposition.tex` states, in ordinary notation, what the Lean development
proves, cites, and leaves open. Every formal statement links to the exact source
line on GitHub, pinned to commit `4fb5915`, so a reader can go from a sentence of
prose to the checked proof in one click. The document adds no mathematics beyond
what the Lean sources contain; the proofs are the sources it links to.

## Build

```sh
# with tectonic (recommended; fetches TeX packages on first run)
tectonic erdos249-257-exposition.tex

# or with a TeX Live install
pdflatex erdos249-257-exposition.tex && pdflatex erdos249-257-exposition.tex

# or
make
```

The output is `erdos249-257-exposition.pdf`.

## Contents

- The Mersenne–Lambert ladder that places both constants on one line.
- Erdős–Borwein-type irrationality (the #257 direction): full support at every base, plus named infinite-support cases.
- The totient constant `S` (Erdős #249): the unconditional denominator record, the coprimality reading, and the reduction to finite certificates.
- Where the work sits among the numbered Erdős problems (#249, #257, #1049, #250, #258, #69).
- What is proved, what is only cited, and what is open, matching the machine-checked non-claims in `../snapshot/NON_CLAIMS.md`.
- An index of the principal declarations with drill-down links.
