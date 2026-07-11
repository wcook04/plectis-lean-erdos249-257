<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Exposition

A guide to this repository for mathematicians who do not read Lean.

`erdos249-257-exposition.tex` states, in ordinary notation, what the Lean development
proves, cites, and leaves open. Every formal statement links to the exact source
line on GitHub, pinned to commit `59f9cc4`, so a reader can go from a sentence of
prose to the checked proof in one click. The visible link text is intentionally
quiet; the file, line, and declaration remain in each link target and in the
release-time paper-link verifier. The document adds no mathematics beyond what the
Lean sources contain; the proofs are the sources it links to.

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
- The totient constant `S` (Erdős #249): the unconditional denominator bound, the coprimality reading, and the exact reduction to finite certificates.
- Formalization architecture and mathematical lessons: how infinite questions are separated from finite kernel-checkable witnesses.
- Artefact availability, verification, and a conclusion stating the exact open boundaries once.
- Auxiliary binary-carry criteria and the compact declaration map in appendices.
