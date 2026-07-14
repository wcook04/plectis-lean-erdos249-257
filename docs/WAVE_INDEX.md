<!--
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0
-->

# Wave index

Wave labels are **development chronology**, not Lean import order.

Read order for humans:

1. `Erdos249257.lean` — import graph / package map
2. this file — chronology and module reference
3. `docs/SOURCE_MAP.md` — intention-based module routes
4. `paper/erdos249-257-exposition.tex` — mathematical exposition

## Chronology map

| Band | Where it lives | Notes |
|---|---|---|
| Pre-wave / early kernel mass | `Erdos249257/CertificateKernel.lean` | Core #257 support-family and certificate machinery assembled before the separately named #249 modules |
| Waves 8–16 | mainly `CertificateKernel.lean` | Earlier kernel layers retained inside the assembled microkernel |
| Waves 17–25 | separately named modules under `Erdos249257/` | Reader-facing ladder, detailed below |
| Wave 26–27 | public material inside `CertificateKernel.lean` | Not a separate top-level module |
| Wave 30 | referenced in `LcmConeNonflat.lean` | Small-prime support of the cone-window argument |
| Generated certificates | `GeneratedCertificates.lean` + `GeneratedCertificates/*` | Generated finite certificate layers, not waves |
| Carry trunk | five post-wave modules under `Erdos249257/` | Not waves; a shared binary-carry layer over the kernel, see below |
| Diagonal pincer frontier | exact decomposition modules, algebraic support, and finite prime-certificate shards | Post-wave #249 work; sharpens the open certificate-supply obligation without closing it |

## Waves 17–25 (named modules)

Each module is a self-contained step with a header docstring stating its own honest boundary. The import chain is `GapFareyBound → MersenneLambertLadder → … → LcmConeNonflat → CertificateKernel ← GeneratedCertificates`.

| Wave | Module | What it establishes |
|---|---|---|
| 17 | `GapFareyBound.lean` | **Farey-gap denominator bounds.** A mediant/Farey argument places any rational `m/q` inside a forbidden gap, so no `q` below the bound can represent `S`. Elementary and per-window; clears `q ≤ 2.49×10¹⁷` (`K=120`) and `q ≤ 7.96×10³⁴` (`K=240`). |
| 18 | `MersenneLambertLadder.lean` | **The Mersenne–Lambert ladder**, machine-checked: the rational rungs `L(μ)=1/2`, `L(φ)=2`, the positive lift `L(A)=S`, and the Möbius-square lens `S = 1/2 + ∑ μ(d)/(2^d−1)²`. Engine: a signed, linear-growth weighted Lambert rearrangement. |
| 19 | `GeometricCoprimality.lean` | **`S` as coprime-pair mass.** `#{(a,b) : a+b=n, 0<a, gcd(a,b)=1} = φ(n)`, so at `r=1/2`, `S − 1/2 = P(gcd(X,Y)=1)` for independent fair-coin waiting times. Base 2 is the unique self-normalising point of the geometric law. |
| 20 | `GcdMomentCalculus.lean` | **The squared transform** `L₂(f) = ∑ f(d)/(2^d−1)² = E[(f * ζ)(gcd(X,Y))]`, since gcd-divisibility factorises across independent coordinates. Yields `L₂(μ) = S − 1/2`, the gcd-moment ladder, and Pillai's gcd-sum function. |
| 21 | `TotientTailPeriodKiller.lean` | **Period, not digits.** Rationality of `S` forces the tail-period law `R_{N+h} − R_N ∈ ℤ`; missing that integer by a decidable margin is a finite "kill". Reduction: `irrational_totient_series_of_certificate_supply`. |
| 22 | `CarrySurvivorExtinction.lean` | **Multiple-period collapse.** Every multiple of a period is a period, so the obligation collapses onto the one-parameter family `periodLcm t = lcm(1..t)`. Adds the carry-survivor orbit certificate (a bounded integer orbit that must escape a narrow strip). |
| 23 | `LcmDiagonalReduction.lean` | **Diagonal collapse.** Standing on the ray (`N = periodLcm t`) removes the second parameter: #249 follows from one ℕ-indexed decidable sequence `∃ L, certifiedKill (periodLcm t) (periodLcm t) L` holding infinitely often. |
| 24 | `LcmConeFlatness.lean` | **Cone-flatness law.** Rationality forces one fractional constant on the whole lcm cone `{k·periodLcm t}`. Certificate **completeness**: a kill exists iff the tail difference is a non-integer (`exists_certifiedKill_iff_tail_diff_notMem_int`). Plus rank-2 second-difference certificates. |
| 25 | `LcmConeNonflat.lean` | **Cone non-flatness refuter.** Interrogates a whole menu of cone vertices at once: if their one-sided arcs shared a common fractional part, the minimal-deep-tail vertex would be a common endpoint, and its certificate row denies exactly that. Sharper than pairwise; genuinely joint for menus of size ≥ 3. |

## Carry trunk (post-wave modules)

These five modules are **not waves**. They form a shared binary-carry layer added after the chronology above, building on `CertificateKernel`: what rationality of a binary series forces on its integer carry states. Reading order: `GenericTailOrbitRigidity → GreedyAchievementSet → BooleanMobiusCarry → RationalSupportCarrySkeleton → SublogDivisorCoverage`.

| Module | What it proves | Main theorems | Depends on |
|---|---|---|---|
| `GenericTailOrbitRigidity` | For coefficients `c(n) ≤ n`, the binary series `∑ c(n)/2ⁿ` is rational exactly when a tempered integer carry orbit exists (`u(N+1) = 2·u(N) − v·c(N+1)` with `u(N)/2ᴺ → 0`); every such orbit is rigid, equal to the scaled analytic tail `v·T_c(N)`. Balanced pulses also prove unbounded exact successor fan-out, ruling out a generic autonomous finite-state decoder. | `temperedBinaryOrbit_eq_scaledTail`, `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`, `balancedPulse_no_autonomous_decoder` | `CertificateKernel` |
| `GreedyAchievementSet` | Greedy geometry for the Mersenne achievement set (values `∑_{n∈A} 1/(2ⁿ−1)`): strict superincreasing tail inequalities, the quantitative gap asymptotic `(2/3)·4⁻ⁿ + O(8⁻ⁿ)`, compact/perfect/totally-disconnected/nowhere-dense structure with Lebesgue measure one, exact real and rational greedy recurrences, membership ⇔ all-level greedy survival, sound one-sided finite rational death certificates (the exact level-one certificate excludes `3/4`), and uniqueness of normalised support coding. Certificates prove nonmembership only. | `volume_mersenneAchievementSet`, `isNowhereDense_mersenneAchievementSet`, `mem_mersenneAchievementSet_iff_greedy_survival`, `certifiedGreedyMersenneDeath_not_mem` | `CertificateKernel` |
| `BooleanMobiusCarry` | Boolean–Möbius carry coordinates for support series: the Lambert coefficient `f_A(n) = #{a ∈ A : a ∣ n}` satisfies `f_A = 1_A * ζ` and `μ * f_A = 1_A` on positive integers; rationality of the support series is equivalent to a tempered carry orbit whose carry quotient is exactly `f_A`; normalised nonempty supports with value `p/q` correspond exactly to quotient-only Boolean Möbius carry certificates. The displayed value `1/2` has a canonical affine-orbit criterion. Worked support `{2,3}`: value `10/21`, period-six orbit `10, 20, 19, 17, 13, 26`. | `erdosSupportSeries_rational_iff_exists_temperedCarry`, `exists_normalized_support_fraction_iff_exists_booleanMobiusCarry`, `support_half_iff_affineBinaryOrbit_tempered` | `GenericTailOrbitRigidity` |
| `RationalSupportCarrySkeleton` | Residue wraps and reciprocal mass: the binary repetend identity (least positive residues in a complete doubling cycle sum to odd modulus × number of wraps), an algebraic one-wrap classification, the Cesàro identification of mean support tails with the reciprocal mass `∑_{a∈A} 1/a`, the exact excess-mean identity, the rationality-forced lower bound `1/ord_v(2)` on reciprocal mass, the dyadic strengthening (mass divergent or `> 1` for infinite dyadic-rational supports), and global unboundedness of the positive carry state attached to any infinite support with rational value. | `sum_doublingResidue_eq_mul_wrapCount`, `one_div_oddOrder_le_reciprocalMass_of_support_fraction`, `dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`, `exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction` | `BooleanMobiusCarry` |
| `SublogDivisorCoverage` | **Sublogarithmic divisor coverage.** If an Erdős support series has a rational value, consecutive zero windows in its divisor-count coefficient `f_A` have length at most `ε log₂(N+1) + O_{ε,c,v}(1)` for every `ε > 0`, uniformly in the support. The proof composes an explicit fixed-power divisor bound (`τ(n)^k ≤ (k^{2^k})^k n`), a binary-tail estimate, and the exact carry recurrence. This constrains support coverage; it does not solve universal #257. | `supportCoeffZeroWindow_length_le_eps_logb_add` | `RationalSupportCarrySkeleton` |

None of these modules claims a solution of Erdős #249 or #257. The contribution boundary is theorem-family-specific: the carry recurrence and strict-tail geometry have direct prior art (Wang–Grau Ribas; Kovač–Tao); Möbius inversion, repetend algebra, and divisor averaging are classical; the converse/rigidity, certificate-normal-form, and coupled reciprocal-mass families remain exact-source-comparison candidates. No priority claim is made.

## Diagonal pincer frontier (post-wave #249 band)

This band refines the lcm-diagonal reduction.  Its main reading chain is
`DiagonalPincerDecomposition → SquaredMersenneDiagonalEnclosure →
DiagonalFreshLossBridge`.  The first module makes diagonal integrality exactly
equivalent to a foreign-defect term hitting a full-target interval.  The second
centres the diagonal expression at a Lambert projection and bounds the signed
squared-Mersenne tail.  The third turns the remaining fresh loss into an exact
integer projection and then into binary suffix conditions.  Every
irrationality theorem in this band retains an explicit unbounded-supply
hypothesis.

`DiagonalPincerCertificates` and the `DiagonalPincerCertificatesT*`
aggregators assemble 22 checked scales through `t = 43`; the many
`DiagonalPincerPrimeCertificates.*` files are finite proof shards, not separate
mathematical claims.  The denominator/cyclotomic chain
`RadicalMobiusShadow → RepunitMobiusNumerator → CyclicTensorMobiusShadow →
CyclotomicProjectionOfShadow → PrimePowerJumpDynamics →
MersenneShadowCyclotomicNoncollapse → MersenneShadowDenominatorGrowth`
supplies exact rational-denominator information used by the frontier.  The
remaining named modules provide finite identities or conditional interfaces;
their headers state the boundary locally.

## Transport and curvature companion band

This post-wave #249 band forms a second, self-contained reading chain:
`CurvatureCarry → ExponentOnlyTransport → JointExponentTransport`, with
`PrimeJumpMigration → PrimeJumpWindow`, `ThreeTransportBoundary`,
`FirstHarmonicGap`, and `TropicalCurvatureCarry` as adjacent branches.  It
proves exact dyadic window decompositions, affine old-channel annihilation,
new-channel migration, two concrete finite certificates, and a
fixed-precision strategy no-go.  It does not prove an unbounded certificate
supply or a first-harmonic estimate, so #249 remains open.  The mathematical
argument is given separately in `paper/erdos249-transport-curvature.tex`.

<!-- BEGIN generated_package_shape -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Package shape

- `CertificateKernel.lean` (0.83 MiB, 18,950 lines, 840 declarations; 512 theorems and 275 lemmas): the assembled microkernel and headline interfaces.
- `GeneratedCertificates.lean` (1.18 MiB, 27,728 lines, 1,174 declarations) plus 3 generated shards: finite certificate instances checked by the Lean kernel.
- The diagonal-pincer family contains 480 isolated prime-certificate modules and 10 scale aggregators. The shards are indexed through aggregators rather than presented as separate mathematical claims.
- Entire checked corpus: 548 modules, 6,525 declarations, 5,958 theorem-like declarations, and 1,681 generated-certificate declarations. The release gate rejects `sorry`, `admit`, custom `axiom` declarations, and `native_decide`.

These are generated inventory facts, not mathematical claim counts. The declaration atlas
and Lean source remain the drilldown owners.
<!-- END generated_package_shape -->
