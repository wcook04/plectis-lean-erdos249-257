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
| Carry trunk | four post-wave modules under `Erdos249257/` | Not waves; a shared binary-carry layer over the kernel, see the section below |

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

## Carry trunk (post-wave modules)

These four modules are **not waves**. They form a shared binary-carry layer added after the chronology above, building on `CertificateKernel`. Reading order: `GenericTailOrbitRigidity → GreedyAchievementSet → BooleanMobiusCarry → RationalSupportCarrySkeleton`.

| Module | What it proves | Main theorems | Depends on |
|---|---|---|---|
| `GenericTailOrbitRigidity` | For coefficients `c(n) ≤ n`, the binary series `∑ c(n)/2ⁿ` is rational exactly when a tempered integer carry orbit exists (`u(N+1) = 2·u(N) − v·c(N+1)` with `u(N)/2ᴺ → 0`); every such orbit is rigid, equal to the scaled analytic tail `v·T_c(N)`. The tempered boundary is essential; positivity alone is deliberately not offered as an equivalent criterion. | `temperedBinaryOrbit_eq_scaledTail`, `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit` | `CertificateKernel` |
| `GreedyAchievementSet` | Greedy geometry for the Mersenne achievement set (values `∑_{n∈A} 1/(2ⁿ−1)`): strict superincreasing tail inequalities, the quantitative gap asymptotic `(2/3)·4⁻ⁿ + O(8⁻ⁿ)`, exact real and rational greedy recurrences, membership ⇔ all-level greedy survival, sound one-sided finite rational death certificates (the exact level-one certificate excludes `3/4`), and uniqueness of normalized support coding. Certificates prove nonmembership only. | `mem_mersenneAchievementSet_iff_greedy_survival`, `certifiedGreedyMersenneDeath_not_mem`, `three_fourths_not_mem_mersenneAchievementSet` | `CertificateKernel` |
| `BooleanMobiusCarry` | Boolean–Möbius carry coordinates for support series: the Lambert coefficient `f_A(n) = #{a ∈ A : a ∣ n}` satisfies `f_A = 1_A * ζ` and `μ * f_A = 1_A` on positive integers; rationality of the support series is equivalent to a tempered carry orbit whose carry quotient is exactly `f_A`; normalized nonempty supports with value `p/q` correspond exactly to quotient-only Boolean Möbius carry certificates. Worked support `{2,3}`: value `10/21`, period-six orbit `10, 20, 19, 17, 13, 26`. | `erdosSupportSeries_rational_iff_exists_temperedCarry`, `exists_normalized_support_fraction_iff_exists_booleanMobiusCarry`, `mobius_carryQuotient_recovers_support` | `GenericTailOrbitRigidity` |
| `RationalSupportCarrySkeleton` | Residue wraps and reciprocal mass: the binary repetend identity (least positive residues in a complete doubling cycle sum to odd modulus × number of wraps), an algebraic one-wrap classification, the Cesàro identification of mean support tails with the reciprocal mass `∑_{a∈A} 1/a`, the exact excess-mean identity, the rationality-forced lower bound `1/ord_v(2)` on reciprocal mass, the dyadic strengthening (mass divergent or `> 1` for infinite dyadic-rational supports), and global unboundedness of the positive carry state attached to any infinite support with rational value. | `sum_doublingResidue_eq_mul_wrapCount`, `one_div_oddOrder_le_reciprocalMass_of_support_fraction`, `dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`, `exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction` | `BooleanMobiusCarry` |

None of these modules claims a solution of Erdős #249 or #257, and all carry-trunk theorems are literature-novelty-unchecked: they are formal interfaces, not novelty claims.
