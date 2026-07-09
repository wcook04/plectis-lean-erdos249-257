<!--
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0
-->

# Source map

User-facing route:

- read `Erdos249257.lean` for the import graph
- read `docs/WAVE_INDEX.md` for chronology
- read the paper for mathematical exposition

## Build entrypoint

- `Erdos249257.lean`
- Lake package: `erdos249257`
- Lean library / stable root import: `Erdos249257`

## #257 / Erdős–Borwein families

- `Erdos249257.CertificateKernel`
- Relevant declarations include: `irrational_erdosSum_full_support`, `irrational_erdosBorwein_series`, `irrational_erdosSum_factorial_support`, `irrational_erdosSum_two_pow_support`

## #249 / totient denominator exclusions

- `Erdos249257.GapFareyBound`
- `Erdos249257.CertificateKernel`

## #249 / certificate reductions

- `Erdos249257.TotientTailPeriodKiller`
- `Erdos249257.CarrySurvivorExtinction`
- `Erdos249257.LcmDiagonalReduction`
- `Erdos249257.LcmConeFlatness`
- `Erdos249257.LcmConeNonflat`

Supporting ladder modules:

- `Erdos249257.MersenneLambertLadder`
- `Erdos249257.GeometricCoprimality`
- `Erdos249257.GcdMomentCalculus`

## Generated finite certificates

- `Erdos249257.GeneratedCertificates`
- `Erdos249257.GeneratedCertificates.*`

## Public adapter

- `PlectisSnapshot.PublicAPI` imports `Erdos249257`, `Erdos249257.CertificateKernel`, and `Erdos249257.GeneratedCertificates`
