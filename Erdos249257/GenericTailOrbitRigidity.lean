import Erdos249257.CertificateKernel

/-!
# Generic tempered tail-orbit rigidity

This module isolates the shared binary carry trunk for the
Erdős #249/#257 problems.  For a nonnegative integer coefficient sequence
`c` satisfying `c(n) ≤ n`, write

`X_c = ∑_{n≥1} c(n) / 2^n`

and let `T_c(N)` be its scaled tail after the first `N` digits.  The main
theorem says that `X_c` is rational exactly when there is a positive integer
`v` and an integer orbit

`u(N+1) = 2*u(N) - v*c(N+1)`

whose growth is tempered by `u(N) / 2^N → 0`.  Every such orbit is rigid:
`u(N) = v*T_c(N)` for every `N`.

The tempered boundary is essential.  Positivity alone is deliberately not
used as a hypothesis and is not advertised as an equivalent criterion: a
homogeneous `2^N` parasite can be added to any orbit without changing the
recurrence.  This is a NON_CLAIM guard against the superseded positive-orbit
route; it does not assert a solution of either Erdős problem.

No novelty or priority claim is made for the theorems in this file.  They are a
formal algebra/analysis interface, not publication authority.
-/

namespace Erdos249257

open Filter Set

/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

/-- A real number represented by an integer numerator and a positive natural
denominator.  This is the explicit positive-denominator form of membership in
`ℚ`; it keeps the carry multiplier visible in theorem statements. -/
def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)

/-- The explicit positive-denominator predicate is exactly standard
rationality (`¬ Irrational x`). -/
theorem hasRationalValue_iff_not_irrational (x : ℝ) :
    HasRationalValue x ↔ ¬ Irrational x := by
  constructor
  · rintro ⟨p, v, hv, hx⟩ hirr
    have hne := hirr.ne_rational p (v : ℤ)
    apply hne
    simpa using hx
  · intro hx
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hx
    refine ⟨q.num, q.den, q.den_pos, ?_⟩
    rw [hq]
    exact Rat.cast_def q

/-- The exact integer recurrence together with the subexponential boundary
`u(N) = o(2^N)`, expressed as convergence of the quotient. -/
def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)

/-- The scaled tail at `N = 0` is the original coefficient series. -/
@[simp] theorem binaryCoeffTail_zero (c : ℕ → ℕ) :
    binaryCoeffTail c 0 = binaryCoeffSeries c := by
  simp only [binaryCoeffTail, binaryCoeffSeries, zero_add]

/-- Nonnegative coefficients give a nonnegative scaled tail. -/
theorem binaryCoeffTail_nonneg (c : ℕ → ℕ) (N : ℕ) :
    0 ≤ binaryCoeffTail c N := by
  unfold binaryCoeffTail
  exact tsum_nonneg fun _ ↦ div_nonneg (Nat.cast_nonneg _) (by positivity)

/-- A linear-growth coefficient sequence has the uniform tail bound
`T_c(N) ≤ N+2`. -/
theorem binaryCoeffTail_le (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N : ℕ) :
    binaryCoeffTail c N ≤ (N : ℝ) + 2 := by
  have h := coeff_far_tail_le 2 N 0 c (by norm_num) hgrowth
  simpa [binaryCoeffTail, add_assoc, add_left_comm, add_comm] using h

/-- The scaled coefficient tail itself is subexponential. -/
theorem binaryCoeffTail_div_pow_tendsto_zero
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    Tendsto (fun N : ℕ ↦ binaryCoeffTail c N / (2 : ℝ) ^ N) atTop (nhds 0) := by
  have hnat : Tendsto (fun N : ℕ ↦ (N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have htwo : Tendsto (fun N : ℕ ↦ (2 : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hupper : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 2) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    simpa [add_div] using hnat.add htwo
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N ↦
      div_nonneg (binaryCoeffTail_nonneg c N) (by positivity))
    (Filter.Eventually.of_forall fun N ↦
      div_le_div_of_nonneg_right (binaryCoeffTail_le c hgrowth N) (by positivity))
    hupper

/-- Doubling the tail shifts the window by one and expels its head
coefficient. -/
theorem binaryCoeffTail_succ
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N : ℕ) :
    binaryCoeffTail c (N + 1) =
      2 * binaryCoeffTail c N - (c (N + 1) : ℝ) := by
  have hsum := summable_coeff_shift_tail 2 N c (by norm_num) hgrowth
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hhead :
      ∑ j ∈ Finset.range 1, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) =
        (c (N + 1) : ℝ) / 2 := by
    rw [Finset.sum_range_one]
    norm_num
  have htail :
      ∑' j : ℕ, (c (N + (j + 1) + 1) : ℝ) / (2 : ℝ) ^ ((j + 1) + 1) =
        binaryCoeffTail c (N + 1) / 2 := by
    unfold binaryCoeffTail
    rw [← tsum_div_const]
    exact tsum_congr fun j ↦ by
      rw [show N + (j + 1) + 1 = N + 1 + j + 1 from by omega, div_div, ← pow_succ]
  have hkey :
      (c (N + 1) : ℝ) / 2 + binaryCoeffTail c (N + 1) / 2 =
        binaryCoeffTail c N := by
    calc
      (c (N + 1) : ℝ) / 2 + binaryCoeffTail c (N + 1) / 2 =
          (∑ j ∈ Finset.range 1,
              (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) +
            ∑' j : ℕ,
              (c (N + (j + 1) + 1) : ℝ) / (2 : ℝ) ^ ((j + 1) + 1) := by
            rw [hhead, htail]
      _ = binaryCoeffTail c N := hsplit
  linarith

/-! ## Generic finite-state non-closure

Rationality of a binary coefficient series does not make the exact tail
orbit autonomous.  The balanced pulses below all have the same dyadic value
and the same complete pre-pulse history, while their first post-pulse tails
have arbitrarily large fan-out.  Thus any exact successor interface must
carry unbounded fresh-input information unless it uses additional arithmetic
structure not present in the generic tail recurrence.
-/

/-- The radius of the balanced-pulse family at location `m`. -/
def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2

/-- A two-site pulse whose mass can be moved from position `m` to `m+1`
without changing its binary-series value. -/
def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0

@[simp] theorem balancedPulseCoeff_at_left (m r : ℕ) :
    balancedPulseCoeff m r m = balancedPulseRadius m - r := by
  simp [balancedPulseCoeff]

@[simp] theorem balancedPulseCoeff_at_right (m r : ℕ) :
    balancedPulseCoeff m r (m + 1) = 2 * r := by
  simp [balancedPulseCoeff]

theorem balancedPulseCoeff_eq_zero_of_ne
    {m r n : ℕ} (hnm : n ≠ m) (hnm1 : n ≠ m + 1) :
    balancedPulseCoeff m r n = 0 := by
  simp [balancedPulseCoeff, hnm, hnm1]

/-- Every admissible balanced pulse lies in the generic linear-growth class. -/
theorem balancedPulseCoeff_le_self
    {m r : ℕ} (hm : 2 ≤ m) (hr : r ≤ balancedPulseRadius m) :
    ∀ n : ℕ, balancedPulseCoeff m r n ≤ n := by
  intro n
  by_cases hnm : n = m
  · subst n
    simp only [balancedPulseCoeff_at_left]
    have hR : balancedPulseRadius m ≤ m := by
      unfold balancedPulseRadius
      omega
    omega
  by_cases hnm1 : n = m + 1
  · subst n
    simp only [balancedPulseCoeff_at_right]
    have hR2 : 2 * balancedPulseRadius m ≤ m + 1 := by
      unfold balancedPulseRadius
      have h := Nat.div_mul_le_self (m + 1) 2
      omega
    omega
  simp [balancedPulseCoeff_eq_zero_of_ne hnm hnm1]

/-- Exact cancellation: all pulse parameters have the same two-site binary
numerator.  This is the finite algebra behind equality of the rational series
and of every tail strictly before `m`. -/
theorem balancedPulse_weighted_pair
    {m r : ℕ} (hr : r ≤ balancedPulseRadius m) :
    2 * balancedPulseCoeff m r m + balancedPulseCoeff m r (m + 1) =
      2 * balancedPulseRadius m := by
  simp only [balancedPulseCoeff_at_left, balancedPulseCoeff_at_right]
  omega

/-- The first tail after the left pulse site decodes the fresh parameter
exactly. -/
theorem balancedPulse_endpoint_fanout (m r : ℕ) :
    balancedPulseCoeff m r (m + 1) / 2 = r := by
  simp

/-- Any exact label/decoder for the balanced-pulse successors is injective.
Consequently its label range has at least `balancedPulseRadius m + 1` elements,
which is unbounded with `m`. -/
theorem balancedPulse_label_injective
    {m : ℕ} {Λ : Type*} (label : Fin (balancedPulseRadius m + 1) → Λ)
    (decode : Λ → ℕ) (hdecode : ∀ r, decode (label r) = r) :
    Function.Injective label := by
  intro r s hrs
  apply Fin.ext
  exact
    (hdecode r).symm.trans <|
      (congrArg decode hrs).trans (hdecode s)

/-- Finite labels capable of exact balanced-pulse decoding need at least the
full pulse fan-out. -/
theorem balancedPulse_label_card_lower_bound
    {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ)
    (decode : Λ → ℕ) (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ := by
  simpa using Fintype.card_le_of_injective label
    (balancedPulse_label_injective label decode hdecode)

/-- The exact successor fan-out is unbounded along the even pulse locations. -/
theorem balancedPulse_fanout_unbounded (k : ℕ) :
    k + 1 ≤ balancedPulseRadius (2 * k) + 1 := by
  unfold balancedPulseRadius
  omega

/-- **Finite-state no-go.**  If a proposed predecessor state identifies all
members of one balanced-pulse family (as every state determined by the common
pre-`m` history must), no autonomous decoder can recover every exact
successor.  The contradiction already uses the parameters `0` and `1`;
`balancedPulse_label_injective` records the full unbounded fan-out. -/
theorem balancedPulse_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r := by
  rintro ⟨decode, hdecode⟩
  have hR : 1 < balancedPulseRadius m + 1 := by
    unfold balancedPulseRadius
    omega
  let zero : Fin (balancedPulseRadius m + 1) := ⟨0, by omega⟩
  let one : Fin (balancedPulseRadius m + 1) := ⟨1, hR⟩
  have hs : state zero = state one := (hstate zero).trans (hstate one).symm
  have hz := hdecode zero
  have ho := hdecode one
  rw [hs] at hz
  have : (zero : ℕ) = one := hz.symm.trans ho
  simp [zero, one] at this

/-! ## Growing-depth affine carry cocycle

The positive replacement for an autonomous state is an input-driven affine
orbit.  At depth `L`, two carries exposed to the same forcing word differ by
exactly `2^L` times their initial difference, hence become equal modulo
`2^L`.  Long jumps therefore synchronise fixed-depth residues; the terminal
forcing suffix, not the predecessor carry, is the information that must be
encoded.
-/

/-- The exact binary affine orbit driven by the fresh coefficient word `a`. -/
def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

@[simp] theorem affineBinaryOrbit_zero (a : ℕ → ℤ) (u0 : ℤ) :
    affineBinaryOrbit a u0 0 = u0 := rfl

@[simp] theorem affineBinaryOrbit_succ (a : ℕ → ℤ) (u0 : ℤ) (n : ℕ) :
    affineBinaryOrbit a u0 (n + 1) =
      2 * affineBinaryOrbit a u0 n - a (n + 1) := rfl

/-- Common forcing amplifies only the initial difference, by the exact
homogeneous factor `2^L`. -/
theorem affineBinaryOrbit_sub (a : ℕ → ℤ) (u0 v0 : ℤ) :
    ∀ L : ℕ,
      affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L =
        (2 : ℤ) ^ L * (u0 - v0) := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
      simp only [affineBinaryOrbit_succ, pow_succ]
      calc
        2 * affineBinaryOrbit a u0 L - a (L + 1) -
              (2 * affineBinaryOrbit a v0 L - a (L + 1)) =
            2 * (affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L) := by ring
        _ = 2 * ((2 : ℤ) ^ L * (u0 - v0)) := by rw [ih]
        _ = (2 : ℤ) ^ L * 2 * (u0 - v0) := by ring

/-- **Fixed-depth reset.**  After `L` common affine carry steps, the endpoint
residue modulo `2^L` is independent of the predecessor carry. -/
theorem affineBinaryOrbit_mod_twoPow_eq (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨v0 - u0, ?_⟩
  rw [affineBinaryOrbit_sub]

/-- A real orbit satisfying `d(N+1)=2d(N)` and `d(N)=o(2^N)` is identically
zero.  This is the abstract rigidity engine. -/
theorem doublingOrbit_eq_zero_of_tempered
    (d : ℕ → ℝ) (hrec : ∀ N : ℕ, d (N + 1) = 2 * d N)
    (htemp : Tendsto (fun N : ℕ ↦ d N / (2 : ℝ) ^ N) atTop (nhds 0)) :
    ∀ N : ℕ, d N = 0 := by
  have hclosed : ∀ N : ℕ, d N = (2 : ℝ) ^ N * d 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [show N + 1 = Nat.succ N from rfl, hrec N, ih, pow_succ]
        ring
  have hratio : ∀ N : ℕ, d N / (2 : ℝ) ^ N = d 0 := by
    intro N
    rw [hclosed N]
    field_simp
  have hconst : Tendsto (fun _ : ℕ ↦ d 0) atTop (nhds (d 0)) := tendsto_const_nhds
  have htozero : Tendsto (fun _ : ℕ ↦ d 0) atTop (nhds 0) :=
    htemp.congr' (Filter.Eventually.of_forall fun N ↦ hratio N)
  have hd0 : d 0 = 0 := tendsto_nhds_unique hconst htozero
  intro N
  rw [hclosed N, hd0, mul_zero]

/-- **Tail-orbit rigidity.**  Every tempered integer orbit is the canonical
scaled tail `v*T_c`. -/
theorem temperedBinaryOrbit_eq_scaledTail
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    {v : ℕ} {u : ℕ → ℤ} (horbit : IsTemperedBinaryOrbit c v u) :
    ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N := by
  rcases horbit with ⟨hrec, htemp⟩
  let d : ℕ → ℝ := fun N ↦ (u N : ℝ) - (v : ℝ) * binaryCoeffTail c N
  have hdrec : ∀ N : ℕ, d (N + 1) = 2 * d N := by
    intro N
    unfold d
    have hu := congrArg (λ z : ℤ ↦ (z : ℝ)) (hrec N)
    push_cast at hu
    rw [hu, binaryCoeffTail_succ c hgrowth N]
    ring
  have hdt : Tendsto (fun N : ℕ ↦ d N / (2 : ℝ) ^ N) atTop (nhds 0) := by
    have htail := (binaryCoeffTail_div_pow_tendsto_zero c hgrowth).const_mul (v : ℝ)
    have hsub := htemp.sub htail
    convert hsub using 1
    · funext N
      unfold d
      ring
    · simp
  have hd0 := doublingOrbit_eq_zero_of_tempered d hdrec hdt
  intro N
  have := hd0 N
  unfold d at this
  linarith

/-- Rationality supplies the canonical positive-multiplier tempered integer
orbit. -/
theorem exists_temperedBinaryOrbit_of_rational
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (hrat : HasRationalValue (binaryCoeffSeries c)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := by
  rcases hrat with ⟨p, v, hv, hvalue⟩
  let z : ℕ → ℤ := fun N ↦
    Classical.choose (bpow_mul_coeff_series_eq_int_add_tail 2 N c (by norm_num) hgrowth)
  have hz : ∀ N : ℕ,
      (2 : ℝ) ^ N * binaryCoeffSeries c =
        (z N : ℝ) + binaryCoeffTail c N := by
    intro N
    exact Classical.choose_spec
      (bpow_mul_coeff_series_eq_int_add_tail 2 N c (by norm_num) hgrowth)
  let u : ℕ → ℤ := fun N ↦ (2 : ℤ) ^ N * p - (v : ℤ) * z N
  have hutail : ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N := by
    intro N
    have hN := hz N
    rw [hvalue] at hN
    have hv0 : (v : ℝ) ≠ 0 := by positivity
    have hmul := congrArg (fun x : ℝ ↦ (v : ℝ) * x) hN
    change
      (v : ℝ) * ((2 : ℝ) ^ N * ((p : ℝ) / (v : ℝ))) =
        (v : ℝ) * ((z N : ℝ) + binaryCoeffTail c N) at hmul
    have hcancel :
        (v : ℝ) * ((2 : ℝ) ^ N * ((p : ℝ) / (v : ℝ))) =
          (2 : ℝ) ^ N * (p : ℝ) := by
      field_simp
    rw [hcancel] at hmul
    unfold u
    push_cast
    linarith
  refine ⟨v, hv, u, ?_, ?_⟩
  · intro N
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [hutail (N + 1), hutail N, binaryCoeffTail_succ c hgrowth N]
    ring
  · have htail := (binaryCoeffTail_div_pow_tendsto_zero c hgrowth).const_mul (v : ℝ)
    convert htail using 1
    · funext N
      rw [hutail N]
      ring
    · simp

/-- A tempered integer orbit forces rationality of the coefficient series. -/
theorem rational_of_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (horbit : ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u) :
    HasRationalValue (binaryCoeffSeries c) := by
  rcases horbit with ⟨v, hv, u, hu⟩
  have hrigid := temperedBinaryOrbit_eq_scaledTail c hgrowth hu 0
  rw [binaryCoeffTail_zero] at hrigid
  refine ⟨u 0, v, hv, ?_⟩
  have hv0 : (v : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hv0).2
  nlinarith

/-- **Subexponential tail-orbit rigidity, equivalence form (T7).** -/
theorem binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := by
  constructor
  · exact exists_temperedBinaryOrbit_of_rational c hgrowth
  · exact rational_of_exists_temperedBinaryOrbit c hgrowth

/-- T7 in Mathlib's standard irrationality vocabulary. -/
theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := by
  rw [← hasRationalValue_iff_not_irrational]
  exact binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit c hgrowth

end Erdos249257
