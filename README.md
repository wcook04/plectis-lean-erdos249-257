<img width="1920" height="1080" alt="image-1783625330775" src="https://github.com/user-attachments/assets/b9a5c21e-058e-4fe9-9eff-92f76379089b" />


<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Erdős #249/#257: a Lean formalization

This snapshot does not solve either open problem; it formalises bounded irrationality results, reductions, certificates, and non-claims around them.

[![Lean CI](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml/badge.svg)](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml)

### Quick navigation

| | |
|:--|:--|
| **[Plectis repository](https://github.com/wcook04/plectis)** | Public claim-testing surface: 88 fixture-backed components with bounded evidence classes, local checks, and receipts. |
| **[Plectis website](https://wcook04.github.io/plectis/)** | Browseable wrapper over the Plectis map: component cards, docs, evidence classes, and scope limits. |
| **[Formal math docs](https://wcook04.github.io/plectis/docs/area-formal-math.html)** | The formal-math & proof area: Lean pipeline components, certificates, and scope limits. |
| **[Architecture docs](https://wcook04.github.io/plectis/docs/architecture.html)** | How the 88 components fit together on one shared path. |
| **[Tour](https://wcook04.github.io/plectis/docs/tour.html)** | A plain walkthrough of what Plectis is, what a component is, and where claims stop. |

A machine-checked Lean 4 (Mathlib) development around two Erdős irrationality problems. It **proves** irrationality for a broad family of Erdős–Borwein-type series, gives an **unconditional** exclusion of every small-denominator rational value for the open totient constant, and **reduces** that open problem to a single sequence of finite, decidable certificates. It does **not** claim to settle either open problem, and it ships machine-checked non-claims and a standalone verifier that say so.

This repository is a pinned, self-verifying public snapshot: everything needed to build and check it is here, and nothing private is required. Toolchain `leanprover/lean4:v4.29.1`, Mathlib pinned in `lake-manifest.json`. No `sorry`, no `admit`, no custom `axiom`; proofs are checked by the Lean kernel (`decide`, never `native_decide`). More than 1,600 theorem declarations across the package; continuous integration builds it on every push.

**Read the exposition (no Lean required):** [`erdos249-257-exposition.pdf`](erdos249-257-exposition.pdf) at the repository root is a companion write-up in ordinary notation. It states what is proved, cited, and open, and links every claim to the exact Lean source line. The LaTeX source and build live in [`paper/`](paper/) (`tectonic paper/erdos249-257-exposition.tex`, or `make -C paper`).

**Where this comes from.** `ai_workflow` is a private agentic system that turns intent into validated, receipt-backed work on disk. [Plectis](https://github.com/wcook04/plectis) is the public claim-testing surface adjacent to that work: fixture-backed components, bounded evidence classes, local checks, and receipts you can audit by cloning the repository. This Lean repository is a separate lane focused on Erdős #249 and #257. It is useful to read beside Plectis because it shows the same evidence discipline around a mathematical frontier, but none of that tooling is proof authority here: **the proof authority is the Lean source in this repository, checked by the Lean kernel.**

---

## Contents

- [The two problems](#the-two-problems): what is asked, what is proved, what is open
- [The Mersenne–Lambert ladder](#the-mersennelambert-ladder): the organizing identity
- [The wave ladder, module by module](#the-wave-ladder-module-by-module): what each file contains
- [What is proved, cited, and open](#what-is-proved-cited-and-open): the honest boundary
- [Related Erdős problems](#related-erdős-problems): where this sits among #249/#257/#1049/#250/#258/#69
- [Where to look in the source](#where-to-look-in-the-source): headline declarations, by file and line
- [The machinery](#the-machinery): kernel, generated certificates, verifier, provenance
- [Build and verify](#build-and-verify)
- [Repository layout](#repository-layout)
- [Related work in progress: Ramanujan Machine Challenge](#related-work-in-progress-ramanujan-machine-challenge)
- [Non-claims and license](#non-claims-and-license)

---

## The two problems

Everything is read at base 2 unless a base `b` is named. Two Dirichlet series carry the story:

- **Erdős–Borwein constant** `E = ∑_{n≥1} 1/(2ⁿ − 1)`.
- **Totient constant** `S = ∑_{n≥1} φ(n)/2ⁿ`, where `φ` is Euler's totient.

### Erdős #257 direction: Erdős–Borwein-type irrationality

The question is whether Erdős–Borwein-type sums `∑_k 1/(b^{a_k} − 1)` are irrational. This snapshot **proves** several genuine cases, all machine-checked and for every base `b ≥ 2`:

| Result | Series | Declaration |
|---|---|---|
| Full support, every base | `∑_{k≥0} 1/(b^{k+1} − 1)` irrational for all `b ≥ 2` | `irrational_erdosSum_full_support` |
| Erdős–Borwein constant | `E = ∑ 1/(2ⁿ − 1)` irrational (base-2 corollary) | `irrational_erdosBorwein_series` |
| Factorial support | `∑_{k≥0} 1/(b^{(k+1)!} − 1)` irrational | `irrational_erdosSum_factorial_support` |
| Power-of-two support | `∑_{k≥0} 1/(b^{2^k} − 1)` irrational | `irrational_erdosSum_two_pow_support` |

**Period noncollapse** is the mechanism behind these: a prime-valuation-deficit witness (`PrimeComponentWitness`, `witness_certificate_implies_period_noncollapse`) shows the multiplicative period of the base modulo the relevant modulus does not collapse, which forbids the long digit blocks a rational value would need. Beyond the four rows above, the same support calculus formalizes further named supports: multiples, pairwise-coprime sets with summable reciprocals (Erdős's condition), eventually-periodic supports, residue classes, and the odd numbers; none is claimed as new mathematics. What remains **open** (and is *not* claimed here) is the fully universal statement: irrationality for *every* infinite support sequence. Proved families are not the universal theorem.

### Erdős #249: irrationality of the totient constant `S`

Whether `S = ∑ φ(n)/2ⁿ` is irrational is **open**. This snapshot contributes two things, and claims neither as a solution.

**Unconditional.** No rational with a small denominator can equal `S`. The strongest landed rung excludes every denominator up to about `7.96 × 10³⁴`:

```
S ≠ p / q   for every integer p and every 1 ≤ q ≤ 79 639 646 646 701 375 323 355 774 875 831 053
```

(`tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`). The ladder of such bounds is `4838 → 4 194 304 (2²²) → 2.49×10¹⁷ (Farey K=120) → 7.96×10³⁴ (Farey K=240)`, each an elementary finite exclusion.

**Conditional reduction.** Via the Möbius-square lens `S = 1/2 + ∑_{d≥1} μ(d)/(2^d − 1)²`, rationality of `S` is equivalent to eventual periodicity of its binary expansion, and periodicity is killed by a finite, decidable certificate. Waves 21–25 collapse the obligation onto a single one-parameter family, e.g.

```
(∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (periodLcm t) (periodLcm t) L)  →  Irrational S
```

(`irrational_totient_series_of_lcm_diagonal_certificate_supply`). The initial segment of that supply is machine-checked to be non-empty (`certifiedKill_all_small`, `certifiedKill_periodLcm_diagonal_upto_six`), but the **unboundedness** of the supply, equivalently the unboundedness of the Farey gap denominators, is the analytic core and is deliberately **untouched**. The reduction is real; the closure is not asserted.

---

## The Mersenne–Lambert ladder

Define the Lambert transform `L(f) = ∑_{n≥1} f(n)/(2ⁿ − 1) = ∑_{m≥1} (∑_{d∣m} f(d)) / 2^m`. One Dirichlet convolution by `ζ` walks a ladder whose rungs have completely different arithmetic character:

| Input `f` | `L(f)` | Value | Status |
|---|---|---|---|
| `μ` (Möbius) | `L(μ)` | `1/2` | rational (proved) |
| `φ` (totient) | `L(φ)` | `2` | rational (proved) |
| `1` (constant one) | `L(1)` | `E` | **irrational, machine-checked** |
| `A = φ * μ` | `L(A)` | `S` | **open: Erdős #249** |
| `Id` | `L(Id)` | `∑ σ(m)/2^m` | transcendental (Nesterenko 1996, cited only) |

The primitive-conductor weight is `A = φ * μ` (`primWeight = totientZ * moebius`), with `primWeight p = p − 2` on primes and `A * ζ = φ`. So one convolution by `ζ` separates the open constant `S` from the rational `2`, and one more separates rational from transcendental (`φ * ζ = Id`, `Id * ζ = σ`). The open constant sits one rung from the machine-checked irrational `E`.

---

## The wave ladder, module by module

Each module is a self-contained step with a header docstring stating its own honest boundary. Wave numbers are development order; the import chain is `GapFareyBound → MersenneLambertLadder → … → LcmConeNonflat → CertificateKernel ← GeneratedCertificates`.

| Wave | Module | What it establishes |
|---|---|---|
| 17 | `GapFareyBound.lean` | **Farey-gap denominator bounds.** A mediant/Farey argument places any rational `m/q` inside a forbidden gap, so no `q` below the bound can represent `S`. Elementary and per-window; clears `q ≤ 2.49×10¹⁷` (`K=120`) and `q ≤ 7.96×10³⁴` (`K=240`). |
| 18 | `MersenneLambertLadder.lean` | **The ladder above**, machine-checked: the rational rungs `L(μ)=1/2`, `L(φ)=2`, the positive lift `L(A)=S`, and the Möbius-square lens `S = 1/2 + ∑ μ(d)/(2^d−1)²`. Engine: a signed, linear-growth weighted Lambert rearrangement. |
| 19 | `GeometricCoprimality.lean` | **`S` as coprime-pair mass.** `#{(a,b) : a+b=n, 0<a, gcd(a,b)=1} = φ(n)`, so at `r=1/2`, `S − 1/2 = P(gcd(X,Y)=1)` for independent fair-coin waiting times. Base 2 is the unique self-normalizing point of the geometric law. |
| 20 | `GcdMomentCalculus.lean` | **The squared transform** `L₂(f) = ∑ f(d)/(2^d−1)² = E[(f * ζ)(gcd(X,Y))]`, since gcd-divisibility factorizes across independent coordinates. Yields `L₂(μ) = S − 1/2`, the gcd-moment ladder, and Pillai's gcd-sum function. |
| 21 | `TotientTailPeriodKiller.lean` | **Period, not digits.** Rationality of `S` forces the tail-period law `R_{N+h} − R_N ∈ ℤ`; missing that integer by a decidable margin is a finite "kill". Reduction: `irrational_totient_series_of_certificate_supply`. |
| 22 | `CarrySurvivorExtinction.lean` | **Multiple-period collapse.** Every multiple of a period is a period, so the obligation collapses onto the one-parameter family `periodLcm t = lcm(1..t)`. Adds the carry-survivor orbit certificate (a bounded integer orbit that must escape a narrow strip). |
| 23 | `LcmDiagonalReduction.lean` | **Diagonal collapse.** Standing on the ray (`N = periodLcm t`) removes the second parameter: #249 follows from one ℕ-indexed decidable sequence `∃ L, certifiedKill (periodLcm t) (periodLcm t) L` holding infinitely often. |
| 24 | `LcmConeFlatness.lean` | **Cone-flatness law.** Rationality forces one fractional constant on the whole lcm cone `{k·periodLcm t}`. Certificate **completeness**: a kill exists iff the tail difference is a non-integer (`exists_certifiedKill_iff_tail_diff_notMem_int`). Plus rank-2 second-difference certificates. |
| 25 | `LcmConeNonflat.lean` | **Cone non-flatness refuter.** Interrogates a whole menu of cone vertices at once: if their one-sided arcs shared a common fractional part, the minimal-deep-tail vertex would be a common endpoint, and its certificate row denies exactly that. Sharper than pairwise; genuinely joint for menus of size ≥ 3. |

**Assembled:** `CertificateKernel.lean` (18,887 lines, 483 theorems) imports all nine modules plus real Mathlib number theory and holds the irrationality proofs, the ladder identities, and the reductions. `GeneratedCertificates.lean` (27,728 lines, 1,026 theorems) plus three shards (`b10_L6_A11`, `b2_L105_A75047`, `b2_L210_A21371`) are machine-generated finite certificate instances, each discharged by `decide`.

---

## What is proved, cited, and open

**Proved (machine-checked in Lean, no `sorry`, no `admit`):**

- Irrationality of `∑ 1/(b^{k+1} − 1)` for every `b ≥ 2` (full support), the base-2 Erdős–Borwein constant, and the factorial and power-of-two support families.
- The Mersenne–Lambert ladder identities, including the Möbius-square lens for `S`.
- **Unconditional** exclusion: `S ≠ p/q` for every `q ≤ 7.96 × 10³⁴`.
- The full chain of **conditional** #249 reductions (periodicity ⟹ tail-period law ⟹ certificate supply ⟹ lcm-diagonal ⟹ cone flatness/non-flatness), plus certificate completeness, and a non-empty initial segment of certified kills.

**Cited, not formalized here:** transcendence of `∑ σ(m)/2^m` (Nesterenko, 1996) and the q-zeta / q-Padé anchor (Postelmans–Van Assche). They are named as ladder neighbours, not re-proved.

**Open (explicitly not solved in this repository):**

- Irrationality of `S = ∑ φ(n)/2ⁿ` (Erdős #249). The conditional reductions turn it into "the certificate supply is unbounded"; producing that unbounded supply is the untouched analytic core.
- The fully universal Erdős–Borwein statement (#257): irrationality for *every* infinite support, beyond the families proved above.

The exact bibliographic problem-numbering for #249/#257 is still being finalized, which is why the bundled verifier reports publication status as `blocked`. That is by design, not an oversight.

---

## Related Erdős problems

Where this work sits among the numbered problems it is near. Statuses are as listed on the individual problem pages ([249](https://www.erdosproblems.com/249), [257](https://www.erdosproblems.com/257), [1049](https://www.erdosproblems.com/1049), [69](https://www.erdosproblems.com/69), [250](https://www.erdosproblems.com/250), [258](https://www.erdosproblems.com/258)) in July 2026; none of the external results is re-proved here.

| Problem | Status | Relation in this repository |
|---|---|---|
| **#249** `∑ φ(n)/2ⁿ` | open | the target: an unconditional denominator exclusion and a conditional reduction, no solution |
| **#257** `∑_{n∈A} 1/(2ⁿ−1)` | open | named infinite-support cases and full support (`A = ℕ`), not the universal statement |
| **#1049** `∑ 1/(tⁿ−1)`, rational `t>1` | open (rational `t`) | the integer-base case `b ≥ 2` is exactly `irrational_erdosSum_full_support`; the rational case is untouched |
| **#69** `∑ ω(n)/2ⁿ` | solved (Tao–Teräväinen) | the prime-support case of #257; only the identity bridge to `∑_p 1/(2ᵖ−1)` is formalized, not the irrationality |
| **#250** `∑ σ(n)/2ⁿ` | solved (Nesterenko 1996) | the ladder neighbour `L(Id)`; cited, not re-proved |
| **#258** `∑ τ(n)/(a₁···aₙ)` | solved | not addressed here; the monotone φ/σ sequel is the sibling territory of #249 |

The one-line summary: a formalization of Erdős–Borwein-type irrationality, an unconditional record, and a finite-certificate reduction for the open totient constant. Not a solution to #249 or to the universal #257.

---

## Where to look in the source

| Claim | Declaration | Location |
|---|---|---|
| `∑ 1/(bⁿ⁺¹−1)` irrational, all `b ≥ 2` | `irrational_erdosSum_full_support` | `CertificateKernel.lean:7999` |
| Erdős–Borwein `E` irrational | `irrational_erdosBorwein_series` | `CertificateKernel.lean:8006` |
| Factorial-support family | `erdos257_family_factorial_instance` | `CertificateKernel.lean:5753` |
| Power-of-two-support family | `erdos257_family_two_pow_instance` | `CertificateKernel.lean:5761` |
| Period-noncollapse witness | `witness_certificate_implies_period_noncollapse` | `CertificateKernel.lean:1270` |
| `S ≠ p/q` for `q ≤ 7.96×10³⁴` | `tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053` | `CertificateKernel.lean:18055` |
| Möbius-square lens `S = 1/2 + ∑ μ(d)/(2^d−1)²` | `totient_series_eq_half_add_moebius_mersenne_square` | `CertificateKernel.lean:18125` |
| Ladder rational rung `L(φ)=2` | `tsum_totient_div_two_pow_sub_one_eq_two` | `CertificateKernel.lean:18100` |
| #249 reduction (period) | `irrational_totient_series_of_certificate_supply` | `TotientTailPeriodKiller.lean:386` |
| #249 reduction (lcm diagonal) | `irrational_totient_series_of_lcm_diagonal_certificate_supply` | `LcmDiagonalReduction.lean:92` |
| Rationality forces cone flatness | `rational_totient_series_forces_lcm_cone_flatness` | `LcmConeFlatness.lean:90` |
| Certificate completeness | `exists_certifiedKill_iff_tail_diff_notMem_int` | `LcmConeFlatness.lean:316` |
| Non-empty certified-kill segment | `certifiedKill_all_small`, `certifiedKill_periodLcm_diagonal_upto_six` | `TotientTailPeriodKiller.lean:396`, `LcmDiagonalReduction.lean:217` |

---

## The machinery

Beyond the mathematics, the snapshot ships the release discipline that produced it.

- **`CertificateKernel.lean`** (~0.85 MB): the assembled microkernel. Imports all nine wave modules plus real Mathlib number theory (`NumberTheory.Real.Irrational`, cyclotomic eval/expand/roots, `TsumDivisorsAntidiagonal`, factorization, `Bertrand`, geometric and infinite sums).
- **`GeneratedCertificates.lean`** (~1.18 MB) and the shards under `GeneratedCertificates/`: machine-generated finite certificate instances. Names encode base `b`, window/level `L`, and the residue/bound `A`. Each is checked by `decide` in the Lean kernel.
- **Kernel-checked, no compiler trust.** Zero uses of `native_decide` and zero `sorry`/`admit` across the package.
- **`scripts/verify_snapshot.py`**: a standard-library-only verifier. It recomputes the tree digest against `snapshot/RELEASE_PROVENANCE.json`, checks the Apache license text, the SPDX/REUSE metadata, the public-API adapter, and the required non-claims. On this snapshot it reports `structural_status: pass` and, deliberately, `status: blocked` until the exact bibliography and a public tag are attached.
- **Provenance and contracts.** Under [`snapshot/`](snapshot/): `RELEASE_PROVENANCE.json` (SLSA-style build statement), `CLAIM_TO_REFERENCE_MAP.json`, `PUBLIC_API_CONTRACT.json`, `PLECTIS_INTEGRATION.json`, `NON_CLAIMS.md`, plus root `REUSE.toml` and full SPDX headers. `PlectisSnapshot/PublicAPI.lean` exposes stable metadata (schema id, source-snapshot hash, non-claim ids) so a consumer can pin this snapshot by hash.

---

## Build and verify

```sh
# Build (downloads the prebuilt Mathlib cache, then builds this package)
lake exe cache get
lake build

# Verify the snapshot with no dependencies beyond the Python standard library
python3 scripts/verify_snapshot.py                  # structural_status: pass; status: blocked (by design)
python3 scripts/verify_snapshot.py --allow-blocked  # exits 0 on structural pass
```

The build is heavy: with more than 1,600 theorem declarations and thousands of `decide`-discharged certificates, a cold `lake build` takes several minutes even with the Mathlib cache. It is exercised on GitHub Actions on every push (see the badge above).

---

## Source maps

- Import graph: [`Erdos249257.lean`](Erdos249257.lean)
- Chronology: [`docs/WAVE_INDEX.md`](docs/WAVE_INDEX.md)
- Intention routes: [`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md)
- Legacy private provenance: [`docs/PROVENANCE.md`](docs/PROVENANCE.md)
- Snapshot contract: [`snapshot/`](snapshot/)
- Non-claims: [`snapshot/NON_CLAIMS.md`](snapshot/NON_CLAIMS.md)
- Release boundary: [`snapshot/RELEASE_BOUNDARY.md`](snapshot/RELEASE_BOUNDARY.md)

## Repository layout

```
Erdos249257.lean            root module (imports kernel + certificates)
Erdos249257/
  CertificateKernel.lean                  assembled microkernel (18,887 lines, 483 theorems)
  GeneratedCertificates.lean              generated finite certificates (27,728 lines, 1,026 theorems)
  GeneratedCertificates/                  per-base certificate shards
  GapFareyBound.lean                      wave 17  Farey-gap denominator bounds
  MersenneLambertLadder.lean              wave 18  the Lambert-transform ladder
  GeometricCoprimality.lean               wave 19  S as coprime-pair mass
  GcdMomentCalculus.lean                  wave 20  the squared (gcd) transform
  TotientTailPeriodKiller.lean            wave 21  rationality => periodicity => kills
  CarrySurvivorExtinction.lean            wave 22  multiple-period collapse
  LcmDiagonalReduction.lean               wave 23  one-parameter diagonal reduction
  LcmConeFlatness.lean                    wave 24  cone-flatness law + completeness
  LcmConeNonflat.lean                     wave 25  joint cone non-flatness refuter
PlectisSnapshot/PublicAPI.lean            stable public-API metadata adapter
scripts/verify_snapshot.py                standalone snapshot verifier
erdos249-257-exposition.pdf                      compiled companion paper (tracked, root-visible)
paper/                                    exposition source for non-Lean readers (LaTeX + build)
snapshot/                         Plectis export contract: manifest, provenance,
                                  non-claims, API contract, references, release notes
lakefile.toml  lake-manifest.json  lean-toolchain                       build pins
```

---

## Related work in progress: Ramanujan Machine Challenge

A separate, in-progress project targets the [Ramanujan Machine Challenge](https://www.ramanujanmachine.com/ramanujan-challenge/): ten problems, released in July 2026, on explicit formulas for constants such as π, e, Catalan's constant, and zeta values. That work lives in a separate Lean lane and is not part of this snapshot. No challenge target is claimed solved or fully formalized here; the table below is a coarse status map.

| Target | Public theme | Status |
|---|---|---|
| 2.1 | polynomial continued fraction for a π-type constant | partial Lean kernel started |
| 2.2 | Euler's constant γ as an Apéry-type limit | partial Lean kernel started |
| 2.3 | π + e as an Apéry-type limit | in progress |
| 2.4 | harmonic-number series for polylog / zeta values | in progress |
| 2.5 | rational approximation of Catalan's constant | in progress |
| 2.6 | series for ζ(2) + ζ(3) | exploratory; not formalized |
| 2.7 | four-term recurrence for ζ(2) + ζ(3) | in progress |
| 2.8 | fast rational approximation of √10005 / π | in progress; target identity conjectural |
| 3.1 | knot-polynomial integral for π² | in progress; statement is an open conjecture |
| 3.2 | Apéry ζ(3) irrationality-measure bound | in progress; statement is an open conjecture |

Ten targets tracked, all ten statements normalized, two partial Lean kernels, zero full formalizations. The release discipline carries over from this package; the theorems do not.

---

## Non-claims and license

The machine-checked non-claims (`snapshot/NON_CLAIMS.md`) are part of the artifact:

- `not_erdos_257_solution`, `not_erdos_249_solution`: this does not solve either problem.
- `not_publication_authority`, `not_private_root_equivalence`, `not_provider_proof_authority`, `not_hidden_proof_body_authority`: a snapshot, not a claim of authority over the private frontier or a hidden proof.

Licensed under Apache-2.0 (`LICENSE`, with SPDX/REUSE metadata). Copyright 2026 Will Cook.
