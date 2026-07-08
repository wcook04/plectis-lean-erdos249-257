<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Erdős period-noncollapse: a Lean formalization toward #249 and #257

[![Lean CI](https://github.com/wcook04/plectis-lean-erdos257-period-noncollapse/actions/workflows/lean.yml/badge.svg)](https://github.com/wcook04/plectis-lean-erdos257-period-noncollapse/actions/workflows/lean.yml)

A machine-checked Lean 4 (Mathlib) development around two Erdős irrationality problems. It **proves** the classical Erdős–Borwein irrationality, builds an exact "Mersenne–Lambert" ladder of Dirichlet-convolution identities around the open constant, and then reduces the open problem to a single sequence of finite, decidable certificates. It does **not** solve the open problems, and it says so in its own machine-checked non-claims.

This repository is a pinned, self-verifying snapshot exported from a larger private system (Plectis). Everything needed to build and check it is here; nothing private is.

---

## The two constants

Everything is read at base 2. Two Dirichlet series carry the whole story:

- **Erdős–Borwein constant** `E = ∑_{n≥1} 1/(2ⁿ − 1)`. Erdős (1948) proved it irrational. That proof is **formalized here**: `irrational_erdosBorwein_series` (in `CertificateKernel.lean`), with no `sorry`.
- **The totient constant** `S = ∑_{n≥1} φ(n)/2ⁿ`, where `φ` is Euler's totient. Whether `S` is irrational is **open**. In this project's framing this is Erdős **#249**; the general base-`b` period-noncollapse question is filed under **#257**. Both are open, and neither is claimed here.

Equivalently, via the Möbius-square lens proved in the ladder,

```
S = 1/2 + ∑_{d≥1} μ(d) / (2^d − 1)²
```

so the irrationality of `S` is the irrationality of that signed Möbius–Mersenne sum.

---

## Contents

- [The Mersenne–Lambert ladder](#the-mersennelambert-ladder) — the organizing identity
- [The wave ladder (module by module)](#the-wave-ladder-module-by-module) — what each file proves
- [What is proven, what is cited, what is open](#what-is-proven-what-is-cited-what-is-open) — the honest boundary
- [The machinery](#the-machinery) — kernel, generated certificates, verifier, provenance
- [Build and verify](#build-and-verify)
- [Repository layout](#repository-layout)
- [Non-claims and license](#non-claims-and-license)

---

## The Mersenne–Lambert ladder

Define the Lambert transform `L(f) = ∑_{n≥1} f(n)/(2ⁿ − 1) = ∑_{m≥1} (∑_{d∣m} f(d)) / 2^m`. Sliding an arithmetic function by one Dirichlet convolution with `ζ` walks along a ladder whose rungs have completely different arithmetic character:

| Input `f` | `L(f)` | Value | Status |
|---|---|---|---|
| `μ` (Möbius) | `L(μ)` | `1/2` | rational (proved) |
| `φ` (totient) | `L(φ)` | `2` | rational (proved) |
| `1` (constant one) | `L(1)` | `E` | **irrational, machine-checked** |
| `A = φ * μ` | `L(A)` | `S` | **open — this is #249** |
| `Id` | `L(Id)` | `∑ σ(m)/2^m` | transcendental (Nesterenko 1996, cited only) |

One convolution by `ζ` separates the open constant from a trivially rational value (`A * ζ = φ`); one more separates rational from transcendental (`φ * ζ = Id`, `Id * ζ = σ`). The open constant `S` sits one rung away from the irrational `E` and one rung from the rational `2`. That is the geometry the rest of the development exploits.

---

## The wave ladder (module by module)

Each module is a self-contained step. The wave numbers are the development order. Every module states its own honest boundary in its header docstring.

| Module | Wave | What it establishes |
|---|---|---|
| `GapFareyBound.lean` | 17 | **Farey-gap denominator bounds.** A denominator `q` cannot represent `S` if a mediant/Farey argument places `m/q` inside a forbidden gap. Elementary, per-window, no bulk `decide`: clears every denominator up to `≈ 2.5×10¹⁷` (window `K=120`) and `≈ 7.96×10³⁴` (`K=240`). Closing #249 this way would need the gap denominators to be unbounded; that is exactly the analytic core left untouched. |
| `MersenneLambertLadder.lean` | 18 | **The ladder above**, machine-checked: the two rational rungs, the positive lift `L(A) = S`, and the signed Möbius-square lens `S = 1/2 + ∑ μ(d)/(2^d−1)²`. Engine: a signed, linear-growth weighted Lambert rearrangement (`weighted_lambert_series_identity` and its signed extension). |
| `GeometricCoprimality.lean` | 19 | **`S` as coprime-pair mass.** For every `n`, `#{(a,b) : a+b=n, 0<a, gcd(a,b)=1} = φ(n)`. Summed against `2⁻ⁿ` this reads `S` as visible-lattice mass, and `S − 1/2 = P(gcd(X,Y)=1)` for independent fair-coin waiting times `X, Y` (base 2 is the unique self-normalizing point of the geometric law). |
| `GcdMomentCalculus.lean` | 20 | **The squared transform** `L₂(f) = ∑ f(d)/(2^d−1)² = E[(f * ζ)(gcd(X,Y))]`, since divisibility of the gcd factorizes across independent coordinates. Gives `L₂(μ) = S − 1/2`, the gcd-moment ladder, Pillai's gcd-sum function, and a q-zeta anchor (cited). |
| `TotientTailPeriodKiller.lean` | 21 | **Change of target: period, not digits.** Rationality of `S` is equivalent to eventual periodicity of its binary expansion, which forces the tail-period law `R_{N+h} − R_N ∈ ℤ`. Missing that integer by a decidable margin is a finite "kill". Reduction: `irrational_totient_series_of_certificate_supply`. |
| `CarrySurvivorExtinction.lean` | 22 | **Multiple-period collapse.** Every multiple of a period is a period, so the obligation collapses onto the one-parameter family `lcm(1..t)` (`irrational_totient_series_of_lcm_survivor_supply`). Adds the carry-survivor orbit certificate: an integer tail difference launches a bounded integer orbit that must escape a narrow strip. |
| `LcmDiagonalReduction.lean` | 23 | **Diagonal collapse.** Standing on the ray (`N = H_t = lcm(1..t)`) removes the second parameter: #249 follows from ONE ℕ-indexed decidable sequence `P t := ∃ L, certifiedKill (H_t, H_t, L)` holding infinitely often (`irrational_totient_series_of_lcm_diagonal_certificate_supply`). Includes the window/totient factorization on the ray. |
| `LcmConeFlatness.lean` | 24 | **Cone-flatness law.** Rationality forces a single fractional constant on the entire lcm cone `{k·H_t}`, and the cones at all scales form one directed system. **Certificate completeness**: a kill exists IFF the tail difference is a non-integer (`exists_certifiedKill_iff_tail_diff_notMem_int`). Plus rank-2 second-difference certificates. |
| `LcmConeNonflat.lean` | 25 | **Cone non-flatness refuter.** Interrogates a whole menu of cone vertices at once: if their one-sided arcs shared a common fractional part, the minimal-deep-tail vertex would be a common endpoint, and its certificate row denies exactly that (`exists_nonintegral_pair_of_coneNonflatCert`). Sharper than pairwise kills; genuinely joint for menus of size ≥ 3. |

---

## What is proven, what is cited, what is open

This is the part a careful reader should read first.

**Proven (machine-checked in Lean, no `sorry`, no `admit`):**

- The Erdős–Borwein constant `E = ∑ 1/(2ⁿ−1)` is irrational — `irrational_erdosBorwein_series`.
- The Mersenne–Lambert ladder identities, including the Möbius-square lens for `S` — `weighted_lambert_series_identity` and the wave-18/19/20 identities.
- The full chain of **conditional** reductions of #249: periodicity ⟹ tail-period law ⟹ certificate supply ⟹ lcm-diagonal ⟹ cone flatness, e.g. `irrational_totient_series_of_certificate_supply`, `irrational_totient_series_of_lcm_diagonal_certificate_supply`, `irrational_totient_series_of_lcm_cone_certificate_supply`.
- Certificate completeness: `exists_certifiedKill_iff_tail_diff_notMem_int`.
- The finite certificate instances themselves, discharged by the kernel-checked `decide`.

**Cited, not formalized here:** the transcendence of `∑ σ(m)/2^m` (Nesterenko, 1996) and the q-zeta / q-Padé irrationality anchor (Postelmans–Van Assche). These are named as ladder neighbours; they are not re-proved.

**Open (explicitly NOT solved in this repository):**

- Irrationality of `S = ∑ φ(n)/2ⁿ` (Erdős #249).
- The general base-`b` period-noncollapse question (#257).

The reductions are **conditional**: they turn #249 into "the certificate supply is unbounded" (equivalently, the Farey gaps grow without bound). Producing that unbounded supply is the analytic core, and it is deliberately **untouched**. This repository provides the reduction and the finite certified initial segment, not the closure. The exact bibliographic problem-numbering for #249/#257 is still being finalized, which is why the bundled verifier reports publication status as `blocked` (see below). This is by design, not an oversight.

---

## The machinery

Beyond the mathematics, the snapshot ships the release discipline that produced it. This is the "how it was made and how you can check it" layer.

- **`CertificateKernel.lean`** (~0.85 MB): the assembled microkernel. Imports all nine wave modules plus real Mathlib number theory (irrationality, cyclotomic polynomials, divisor-sum antidiagonals, prime factorization, Bertrand's postulate, geometric sums, infinite sums). Holds the Erdős–Borwein proof, the ladder identities, and the reduction theorems.
- **`GeneratedCertificates.lean`** (~1.18 MB) and the shards under `GeneratedCertificates/` (`b10_L6_A11`, `b2_L105_A75047`, `b2_L210_A21371`): machine-generated finite certificate instances. The names encode base `b`, window/level `L`, and the residue/bound `A`. Each is checked by `decide` in the Lean kernel.
- **Kernel-checked, no compiler trust.** The certificates use `decide` (evaluated by the Lean kernel), not `native_decide` (which would trust the compiler). There are zero uses of `native_decide` and zero `sorry`/`admit` in the development.
- **`scripts/verify_snapshot.py`**: a dependency-free (standard-library-only) verifier. It recomputes the tree digest against `RELEASE_PROVENANCE.json`, checks the Apache license text, the SPDX/REUSE metadata, the public-API adapter, and the required non-claims, then reports its own status. On this snapshot it prints `structural_status: pass` and, deliberately, `status: blocked` until the exact bibliography and a public tag are attached.
- **Provenance and contracts.** `RELEASE_PROVENANCE.json` (SLSA-style build statement), `CLAIM_TO_REFERENCE_MAP.json`, `PUBLIC_API_CONTRACT.json`, `PLECTIS_INTEGRATION.json`, `NON_CLAIMS.md`, `REUSE.toml`, and full SPDX headers. `PlectisSnapshot/PublicAPI.lean` exposes stable metadata (schema id, source-snapshot hash, non-claim ids) so a downstream consumer can pin this snapshot by hash.

---

## Build and verify

Toolchain: `leanprover/lean4:v4.29.1`, Mathlib pinned via `lake-manifest.json`. Continuous integration builds the whole package on every push (see the badge above).

```sh
# Build (downloads the prebuilt Mathlib cache, then builds this package)
lake exe cache get
lake build

# Verify the snapshot with no dependencies beyond a Python standard library
python3 scripts/verify_snapshot.py                 # structural_status: pass; status: blocked (by design)
python3 scripts/verify_snapshot.py --allow-blocked  # exits 0 on structural pass
```

The build is heavy: the certificates are discharged by `decide`, so a cold `lake build` takes several minutes even with the Mathlib cache.

---

## Repository layout

```
Erdos257PeriodNoncollapse.lean            root module (imports kernel + certificates)
Erdos257PeriodNoncollapse/
  CertificateKernel.lean                  assembled microkernel (~0.85 MB)
  GeneratedCertificates.lean              generated finite certificates (~1.18 MB)
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
NON_CLAIMS.md  RELEASE_PROVENANCE.json  PUBLIC_API_CONTRACT.json  ...   release metadata
lakefile.toml  lake-manifest.json  lean-toolchain                       build pins
```

---

## Non-claims and license

The machine-checked non-claims (`NON_CLAIMS.md`) are part of the artifact:

- `not_erdos_257_solution`, `not_erdos_249_solution` — this does not solve either problem.
- `not_publication_authority`, `not_private_root_equivalence`, `not_provider_proof_authority`, `not_hidden_proof_body_authority` — a snapshot, not a claim of authority over the private frontier or a hidden proof.

Licensed under Apache-2.0 (`LICENSE`, with SPDX/REUSE metadata). Copyright 2026 Will Cook.
