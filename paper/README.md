<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Exposition

A guide to this repository for mathematicians who do not read Lean.

`erdos249-257-exposition.tex` states, in ordinary notation, what the Lean development
proves, cites, and leaves open. Every formal statement links to the exact source
line on GitHub, pinned to the release tag `v0.6.0`, so a reader can go from a
sentence of prose to the checked proof in one click. The visible link text is
intentionally quiet; the file, line, and declaration remain in each link target
and are verified against the released source by `scripts/check_release.py`. The
document adds no mathematics beyond what the Lean sources contain; the proofs
are the sources it links to.

The manuscript layer (this `.tex` and the rendered PDF) is licensed CC-BY-4.0;
see `REUSE.toml` at the repository root.

`erdos249-transport-curvature.tex` is the technical companion for the
transport/curvature frontier. It separates unconditional affine-channel
cancellation, sharp finite consumers, and the fixed-precision no-go theorem
from the explicitly open unbounded-supply and first-harmonic hypotheses.

## Build

```sh
# with tectonic (recommended; fetches TeX packages on first run)
tectonic erdos249-257-exposition.tex

# or with a TeX Live install
pdflatex erdos249-257-exposition.tex && pdflatex erdos249-257-exposition.tex

# or
make
```

The outputs are `erdos249-257-exposition.pdf` and
`erdos249-transport-curvature.pdf`.

## Contents

- The Mersenne–Lambert ladder that places both constants on one line.
- Erdős–Borwein-type irrationality (the #257 direction): full support at every base, plus named infinite-support cases.
- The totient constant `S` (Erdős #249): the unconditional denominator bound, the coprimality reading, and the exact reduction to finite certificates.
- Formalisation architecture and mathematical lessons: how infinite questions are separated from finite kernel-checkable witnesses.
- The formalisation method: how checked statements, finite computations, exact reductions, and the unresolved steps in Erdős #249 and #257 are kept distinct.
- Artefact availability, verification, and a conclusion stating the exact open boundaries once.
- Auxiliary binary-carry criteria and the compact declaration map in appendices.
- The sublogarithmic zero-window theorem for divisor coverage forced by a hypothetical rational support value.
