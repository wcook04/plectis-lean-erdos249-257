<!--
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0
-->

# Wave index

Wave labels are **development chronology**, not Lean import order.

Read order for humans:

1. `Erdos249257.lean` — import graph / package map
2. this file — chronology
3. `docs/SOURCE_MAP.md` — intention-based module routes
4. `paper/erdos249-257-exposition.tex` — mathematical exposition

## Chronology map

| Band | Where it lives | Notes |
|---|---|---|
| Pre-wave / early kernel mass | `Erdos249257/CertificateKernel.lean` | Core #257 support-family and certificate machinery assembled before the separately named #249 modules |
| Waves 8–16 | mainly `CertificateKernel.lean` | Earlier kernel layers retained inside the assembled microkernel |
| Waves 17–25 | separately named modules under `Erdos249257/` | Reader-facing ladder in the README table |
| Wave 26–27 | public material inside `CertificateKernel.lean` | Not a separate top-level module |
| Wave 30 | referenced in `LcmConeNonflat.lean` | Small-prime support of the cone-window argument |
| Generated certificates | `GeneratedCertificates.lean` + `GeneratedCertificates/*` | Generated finite certificate layers, not waves |

## Waves 17–25 (named modules)

| Wave | Module |
|---|---|
| 17 | `GapFareyBound` |
| 18 | `MersenneLambertLadder` |
| 19 | `GeometricCoprimality` |
| 20 | `GcdMomentCalculus` |
| 21 | `TotientTailPeriodKiller` |
| 22 | `CarrySurvivorExtinction` |
| 23 | `LcmDiagonalReduction` |
| 24 | `LcmConeFlatness` |
| 25 | `LcmConeNonflat` |

The old README table covered only waves 17–25. That was a reader-facing subset, not the whole development mass.
