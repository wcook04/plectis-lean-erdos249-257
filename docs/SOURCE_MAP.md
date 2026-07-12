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

## #249 / diagonal pincer frontier

Read this band after the certificate reductions above.  It sharpens the same
open obligation; it does not prove the required unbounded supply.

- `Erdos249257.DiagonalPincerDecomposition` — exact full-target interval
  characterisation and the target-avoidance-to-irrationality reduction.
- `Erdos249257.SquaredMersenneDiagonalEnclosure` — Lambert-projected centre,
  exact signed square tail, and a sharp separation criterion.
- `Erdos249257.DiagonalFreshLossBridge` — exact fresh-loss projection and
  stronger adjacent-suffix supply interfaces.
- `Erdos249257.DiagonalPincerCertificates` and
  `Erdos249257.DiagonalPincerCertificatesT*` — the finite diagonal segment,
  currently assembled at 22 explicit scales through `t = 43`.
- `Erdos249257.DiagonalPincerPrimeCertificates.*` — finite prime certificate
  shards used by that assembled segment; read the aggregators first.

Algebraic support for the same band:

- `MersenneShadowCyclotomicNoncollapse → MersenneShadowDenominatorGrowth`
- `RadicalMobiusShadow → RepunitMobiusNumerator → CyclicTensorMobiusShadow`
- `CyclotomicProjectionOfShadow → PrimePowerJumpDynamics`
- `RationalDenominatorSurvival`, `LambertDiagonalEnclosure`,
  `FullTargetPrimeAdjunctionNoGo`, and `DyadicPrefixCompression`

Exploratory exact interfaces with explicit conditional boundaries live in
`PrimitiveRationalGapSupply`, `PrimitiveSupportBridge`,
`ActualForeignResidueProjection`, `SternBrocotRunGeometry`, and
`SupportDilationDifferences`.

### Transport and curvature companion band

Read `CurvatureCarry → ExponentOnlyTransport → JointExponentTransport` for the
main proof spine, then `PrimeJumpMigration → PrimeJumpWindow` and
`ThreeTransportBoundary` for the new-prime and balanced finite consumers.
`FirstHarmonicGap` is the analytic interface: a constant-saving cosine bound
forces a direct certificate, but no cofinal estimate is asserted.
`TropicalCurvatureCarry` is a proved negative result showing that bounded
valuation–unit precision alone cannot exclude all centred completions.

- `CurvatureCarry` — exact curvature window, sharp radius, recurrence, and
  conditional unbounded-supply endpoints.
- `ExponentOnlyTransport` — squarefree support stability and the exact
  periodic affine slope/intercept state.
- `JointExponentTransport` — universal two-moment old-channel annihilation and
  the anchored `(3,5)` four-vertex consumer.
- `PrimeJumpMigration` / `PrimeJumpWindow` — migrated-channel correction,
  sharp direct radius, and the finite `(12,5,15)` certificate.
- `ThreeTransportBoundary` — balanced `(1,2,3,6)` consumer and the finite
  `(60,12)` certificate.
- `FirstHarmonicGap` — deterministic conversion of a blockwise harmonic gap
  into a direct certificate.
- `TropicalCurvatureCarry` — fixed-precision local-signature no-go theorem.

The technical exposition is `paper/erdos249-transport-curvature.tex`.  This
band is included as a separate companion because it has its own definitions
and proof spine; folding it into the principal paper would obscure the latter's
global result map.  Every irrationality endpoint in the band remains a
conditional reduction.

### Paper-curation boundary

The paper treats `GcdMomentCalculus` as supporting mathematical exposition: its
squared Lambert transform, gcd moments, reduced-direction law, and cylinder
recursion explain the representation containing the #249 Möbius-square atom.
`FullTargetPrimeAdjunctionNoGo` is included as a proved negative result because
it closes a recurring prime-adjunction strategy without changing the open
claim. `SternBrocotRunGeometry` remains source-map-only supporting
combinatorics: its continuant/Fibonacci stability theorems are exact, but no
principal claim or current argument edge consumes them. Promoting that module
to a paper result would therefore confuse formal infrastructure with a new
contribution; the cylinder law actually used in the exposition is owned by
`GcdMomentCalculus`.

## Binary-carry trunk (post-wave carry layer)

Builds on `Erdos249257.CertificateKernel`; not part of the wave chronology. Reading order: `GenericTailOrbitRigidity → GreedyAchievementSet → BooleanMobiusCarry → RationalSupportCarrySkeleton → SublogDivisorCoverage`.

- `Erdos249257.GenericTailOrbitRigidity`
- Relevant declarations include: `temperedBinaryOrbit_eq_scaledTail`, `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`, `balancedPulse_fanout_unbounded`, `balancedPulse_no_autonomous_decoder`

- `Erdos249257.GreedyAchievementSet`
- Relevant declarations include: `volume_mersenneAchievementSet`, `perfect_mersenneAchievementSet`, `isNowhereDense_mersenneAchievementSet`, `mem_mersenneAchievementSet_iff_greedy_survival`, `certifiedGreedyMersenneDeath_not_mem`, `three_fourths_not_mem_mersenneAchievementSet`, `rational_member_support_bit_iff`, `half_mem_mersenneAchievementSet_of_prefixForcingChain` (conditional interface only)

- `Erdos249257.BooleanMobiusCarry`
- Relevant declarations include: `erdosSupportSeries_rational_iff_exists_temperedCarry`, `support_fraction_iff_exists_temperedCarry`, `exists_normalized_support_fraction_iff_exists_booleanMobiusCarry`, `mobius_carryQuotient_recovers_support`, `support_half_iff_affineBinaryOrbit_tempered`

- `Erdos249257.RationalSupportCarrySkeleton`
- Relevant declarations include: `sum_doublingResidue_eq_mul_wrapCount`, `one_div_oddOrder_le_reciprocalMass_of_support_fraction`, `reciprocalMass_eq_residueMean_add_excessMean`, `dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`, `exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`

- `Erdos249257.SublogDivisorCoverage`
- Relevant declarations include: `supportCoeffZeroWindow_length_le_eps_logb_add`

## Claim registry

- `docs/claims.json` — the single owner of release identity, claim statuses, and declaration coordinates (file and line), cross-checked by `scripts/check_release.py`

## Generated finite certificates

- `Erdos249257.GeneratedCertificates`
- `Erdos249257.GeneratedCertificates.*`

The complete 538-module import graph and every declaration are generated in
`docs/claims.json::machine_readable_paper.module_graph` and
`docs/declaration_atlas.json`; use those surfaces when a grouped route above is
not specific enough.
