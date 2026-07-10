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

## Binary-carry trunk (post-wave carry layer)

Builds on `Erdos249257.CertificateKernel`; not part of the wave chronology. Reading order: `GenericTailOrbitRigidity → GreedyAchievementSet → BooleanMobiusCarry → RationalSupportCarrySkeleton`.

- `Erdos249257.GenericTailOrbitRigidity`
- Relevant declarations include: `temperedBinaryOrbit_eq_scaledTail`, `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`, `not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit`

- `Erdos249257.GreedyAchievementSet`
- Relevant declarations include: `mem_mersenneAchievementSet_iff_greedy_survival`, `certifiedGreedyMersenneDeath_not_mem`, `three_fourths_not_mem_mersenneAchievementSet`, `rational_member_support_bit_iff`

- `Erdos249257.BooleanMobiusCarry`
- Relevant declarations include: `erdosSupportSeries_rational_iff_exists_temperedCarry`, `support_fraction_iff_exists_temperedCarry`, `exists_normalized_support_fraction_iff_exists_booleanMobiusCarry`, `mobius_carryQuotient_recovers_support`

- `Erdos249257.RationalSupportCarrySkeleton`
- Relevant declarations include: `sum_doublingResidue_eq_mul_wrapCount`, `one_div_oddOrder_le_reciprocalMass_of_support_fraction`, `reciprocalMass_eq_residueMean_add_excessMean`, `dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`, `exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`

## Generated finite certificates

- `Erdos249257.GeneratedCertificates`
- `Erdos249257.GeneratedCertificates.*`
