import Erdos249257.CertificateKernel

/-!
# Generic tempered tail-orbit rigidity

This module proves a self-contained rationality criterion for binary series
with linearly bounded coefficients.  For a nonnegative integer coefficient
sequence `c` satisfying `c(n) ≤ n`, write

`X_c = ∑_{n≥1} c(n) / 2^n`

and let `T_c(N)` be its scaled tail after the first `N` digits.  The main
theorem (`binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`) says
that `X_c` is rational exactly when there is a positive integer `v` and an
integer orbit

`u(N+1) = 2*u(N) - v*c(N+1)`

whose growth is tempered by `u(N) / 2^N → 0`.  Every such orbit is rigid
(`temperedBinaryOrbit_eq_scaledTail`): `u(N) = v*T_c(N)` for every `N`.
The equivalence is restated in Mathlib's standard irrationality vocabulary
by `not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit`.

The tempered boundary is essential.  Positivity alone is deliberately not
used as a hypothesis and is not advertised as an equivalent criterion: a
homogeneous `2^N` parasite can be added to any orbit without changing the
recurrence, so positivity of an orbit certifies nothing on its own.  This
is a NON_CLAIM guard; nothing in this file asserts a solution of Erdős
#249 or #257.

The forward mechanism here is not new: Wang and Grau Ribas, *Positive
dyadic density for rational weighted binary expansions* (arXiv:2606.24972,
2026), use the same integral carry recurrence forced by rationality for
weighted binary expansions with coefficients `c(n) = n·d(n)` — a special
case of the linearly bounded coefficients treated here.  What this module
contributes is the generic interface (arbitrary nonnegative `c(n) ≤ n`),
the explicit converse, and the rigidity theorem that every tempered orbit
equals the scaled analytic tail.  These are formalisation and abstraction
contributions, not a priority claim on the carry mechanism.
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
    exact hirr.ne_rational p (v : ℤ) (by simpa using hx)
  · intro hx
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hx
    exact ⟨q.num, q.den, q.den_pos, by rw [hq, Rat.cast_def]⟩

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

/-- A linearly bounded coefficient sequence has the tail bound
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

/-- The scaled-tail quotient `v*T_c(N) / 2^N` inherits the subexponential
decay.  Shared tendsto-transfer step for the rigidity and existence proofs. -/
private theorem scaledTail_div_pow_tendsto_zero
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (v : ℕ) :
    Tendsto (fun N : ℕ ↦ (v : ℝ) * binaryCoeffTail c N / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
  simpa [mul_div_assoc] using
    (binaryCoeffTail_div_pow_tendsto_zero c hgrowth).const_mul (v : ℝ)

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
        rw [hrec N, ih, pow_succ]
        ring
  have hratio : ∀ N : ℕ, d N / (2 : ℝ) ^ N = d 0 := by
    intro N
    rw [hclosed N]
    field_simp
  have hd0 : d 0 = 0 := tendsto_nhds_unique tendsto_const_nhds (htemp.congr hratio)
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
    have hsub := htemp.sub (scaledTail_div_pow_tendsto_zero c hgrowth v)
    rw [sub_zero] at hsub
    exact hsub.congr fun N ↦ by unfold d; ring
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
    have hmul :
        (v : ℝ) * ((2 : ℝ) ^ N * ((p : ℝ) / (v : ℝ))) =
          (v : ℝ) * ((z N : ℝ) + binaryCoeffTail c N) := by
      rw [hN]
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
  · exact (scaledTail_div_pow_tendsto_zero c hgrowth v).congr
      fun N ↦ by rw [hutail N]

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
  rw [eq_div_iff hv0, mul_comm]
  exact hrigid.symm

/-- **Subexponential tail-orbit rigidity, equivalence form.**  The series
`X_c` is rational exactly when some tempered integer orbit exists. -/
theorem binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u :=
  ⟨exists_temperedBinaryOrbit_of_rational c hgrowth,
    rational_of_exists_temperedBinaryOrbit c hgrowth⟩

/-- The equivalence in Mathlib's standard irrationality vocabulary
(`¬ Irrational`). -/
theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u :=
  (hasRationalValue_iff_not_irrational _).symm.trans
    (binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit c hgrowth)

end Erdos249257
