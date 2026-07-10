import Erdos249257.GenericTailOrbitRigidity
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Boolean–Möbius carry coordinates for Erdős #257

For a support `A ⊆ ℕ`, the binary Lambert expansion has positive-index
coefficient

`f_A(n) = #{a ∈ A : a ∣ n}`.

This file makes two exact coordinate changes kernel-visible.

* Dirichlet/Möbius: `f_A = 1_A * ζ` and `μ * f_A = 1_A` on positive
  integers (`positiveSupportBitAF_mul_zeta`, `moebius_mul_supportCoeffAF`).
  Conversely, every arithmetic function whose Möbius transform is Boolean
  is the divisor-count coefficient of the support selected by that Boolean
  transform (`eq_supportCoeffAF_booleanMobiusSupport_of_boolean`).
* Binary carry: rationality of the support series is equivalent to a
  tempered integer orbit for `f_A`; for a displayed fraction `p/q`, the
  orbit has multiplier `q`, initial value `p`
  (`support_fraction_iff_exists_temperedCarry`), and its carry quotient is
  exactly `f_A` (`temperedCarry_quotient_eq_supportCoeff`).

The two changes compose into the headline equivalence
`exists_normalized_support_fraction_iff_exists_booleanMobiusCarry`: a
normalized nonempty support with series value `p/q` exists if and only if
a quotient-only `BooleanMobiusCarryCertificate` does.  Supporting estimates
include the elementary divisor-pair bound `τ(n) ≤ 2⌊√n⌋`
(`card_divisors_le_two_mul_sqrt`) and the resulting square-root strip on
orbit states.

Exponent zero is analytically invisible because the existing support series
uses real division-by-zero conventions at `2^0 - 1`.  Accordingly, set-level
recovery is stated either on positive indices or under `0 ∉ A`.  Omitting
that guard would be false.

The worked support `{2,3}` gives `10/21` and the pure period-six orbit
`10,20,19,17,13,26` (`carryOrbit23_isTempered`).  These coordinate theorems
do **not** prove Erdős #257: they neither exclude infinite Boolean carry
paths nor turn finite search into a completeness argument.  Both Erdős #249
and #257 remain open.

The literature has not been audited for prior statements of these lemmas;
they are formal infrastructure, not claimed novelties.
-/

namespace Erdos249257

open ArithmeticFunction Filter Set
open scoped ArithmeticFunction.Moebius

/-! ## Arithmetic-function packaging -/

/-- The positive-index integer indicator of a support.  Arithmetic functions
must vanish at zero, which is also the correct normalization for the Lambert
coefficient calculus. -/
noncomputable def positiveSupportBit (A : Set ℕ) (n : ℕ) : ℤ :=
  letI := Classical.propDecidable (0 < n ∧ n ∈ A)
  if 0 < n ∧ n ∈ A then 1 else 0

/-- `positiveSupportBit` packaged as an integer-valued arithmetic function. -/
noncomputable def positiveSupportBitAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨positiveSupportBit A, by simp [positiveSupportBit]⟩

/-- The support divisor-count coefficient, cast to an integer-valued
arithmetic function. -/
noncomputable def supportCoeffAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ (supportCoeff A n : ℤ), by simp [supportCoeff]⟩

@[simp] theorem positiveSupportBit_zero (A : Set ℕ) :
    positiveSupportBit A 0 = 0 := by
  simp [positiveSupportBit]

theorem positiveSupportBit_eq_one_iff {A : Set ℕ} {n : ℕ} (hn : 0 < n) :
    positiveSupportBit A n = 1 ↔ n ∈ A := by
  classical
  simp [positiveSupportBit, hn]

@[simp] theorem positiveSupportBitAF_apply (A : Set ℕ) (n : ℕ) :
    positiveSupportBitAF A n = positiveSupportBit A n := rfl

@[simp] theorem supportCoeffAF_apply (A : Set ℕ) (n : ℕ) :
    supportCoeffAF A n = (supportCoeff A n : ℤ) := rfl

/-- The divisor-count coefficient is exactly `1_A * ζ`, with the support
indicator normalized at zero. -/
theorem positiveSupportBitAF_mul_zeta (A : Set ℕ) :
    positiveSupportBitAF A *
        (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)
      = supportCoeffAF A := by
  classical
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [positiveSupportBitAF_apply, supportCoeffAF_apply]
  change
    (∑ d ∈ n.divisors, positiveSupportBit A d) =
      (supportCoeff A n : ℤ)
  rw [supportCoeff_eq_card_filter A n, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  by_cases hA : d ∈ A <;> simp [positiveSupportBit, hdpos, hA]

/-- Exact Möbius recovery: `μ * f_A = 1_A` as arithmetic functions. -/
theorem moebius_mul_supportCoeffAF (A : Set ℕ) :
    ArithmeticFunction.moebius * supportCoeffAF A = positiveSupportBitAF A := by
  calc
    ArithmeticFunction.moebius * supportCoeffAF A =
        ArithmeticFunction.moebius *
          (positiveSupportBitAF A *
            (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
              ArithmeticFunction ℤ)) := by
          rw [positiveSupportBitAF_mul_zeta]
    _ = (ArithmeticFunction.moebius *
          (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℤ)) * positiveSupportBitAF A := by
          ac_rfl
    _ = positiveSupportBitAF A := by
          rw [ArithmeticFunction.moebius_mul_coe_zeta, one_mul]

/-- Pointwise positive-index form of Möbius recovery. -/
theorem mobius_supportCoeff_eq_one_iff (A : Set ℕ) {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 ↔ n ∈ A := by
  rw [moebius_mul_supportCoeffAF]
  exact positiveSupportBit_eq_one_iff hn

/-- The Möbius transform of every support coefficient is Boolean. -/
theorem mobius_supportCoeff_boolean (A : Set ℕ) (n : ℕ) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 0 ∨
      (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 := by
  rw [moebius_mul_supportCoeffAF]
  change positiveSupportBit A n = 0 ∨ positiveSupportBit A n = 1
  classical
  by_cases h : 0 < n ∧ n ∈ A <;> simp [positiveSupportBit, h]

/-- When `0 ∉ A`, the Boolean Möbius transform recovers the entire
support set, not merely its positive part. -/
theorem mobius_supportCoeff_recovers_support (A : Set ℕ) (hzero : 0 ∉ A) :
    {n : ℕ | (ArithmeticFunction.moebius * supportCoeffAF A) n = 1} = A := by
  ext n
  rw [moebius_mul_supportCoeffAF]
  change positiveSupportBit A n = 1 ↔ n ∈ A
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hzero]
  · simp [positiveSupportBit, hn]

/-! ## Converse Boolean inversion -/

/-- The positive support selected by the Boolean Möbius transform of `f`. -/
noncomputable def booleanMobiusSupport (f : ArithmeticFunction ℤ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ (ArithmeticFunction.moebius * f) n = 1}

@[simp] theorem zero_not_mem_booleanMobiusSupport (f : ArithmeticFunction ℤ) :
    0 ∉ booleanMobiusSupport f := by
  simp [booleanMobiusSupport]

/-- A Boolean Möbius transform is exactly the normalized indicator of the
support that it selects. -/
theorem moebius_mul_eq_positiveSupportBitAF_of_boolean
    (f : ArithmeticFunction ℤ)
    (hbool : ∀ n : ℕ, 0 < n →
      (ArithmeticFunction.moebius * f) n = 0 ∨
        (ArithmeticFunction.moebius * f) n = 1) :
    ArithmeticFunction.moebius * f =
      positiveSupportBitAF (booleanMobiusSupport f) := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rcases hbool n hn with hzero | hone
    · change (ArithmeticFunction.moebius * f) n =
          positiveSupportBit (booleanMobiusSupport f) n
      rw [hzero]
      classical
      unfold positiveSupportBit
      rw [if_neg]
      rintro ⟨_, hmem⟩
      change 0 < n ∧ (ArithmeticFunction.moebius * f) n = 1 at hmem
      omega
    · change (ArithmeticFunction.moebius * f) n =
          positiveSupportBit (booleanMobiusSupport f) n
      rw [hone]
      classical
      unfold positiveSupportBit
      rw [if_pos]
      exact ⟨hn, ⟨hn, hone⟩⟩

/-- **Boolean Möbius inversion, converse direction.**  Every integer-valued
arithmetic function with Boolean Möbius transform is the support coefficient
of the positive set selected by that transform.  No search or finiteness
hypothesis appears. -/
theorem eq_supportCoeffAF_booleanMobiusSupport_of_boolean
    (f : ArithmeticFunction ℤ)
    (hbool : ∀ n : ℕ, 0 < n →
      (ArithmeticFunction.moebius * f) n = 0 ∨
        (ArithmeticFunction.moebius * f) n = 1) :
    f = supportCoeffAF (booleanMobiusSupport f) := by
  have hbit := moebius_mul_eq_positiveSupportBitAF_of_boolean f hbool
  calc
    f = ((↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℤ) * ArithmeticFunction.moebius) * f := by
        rw [ArithmeticFunction.coe_zeta_mul_moebius, one_mul]
    _ = (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℤ) * (ArithmeticFunction.moebius * f) := by
        rw [mul_assoc]
    _ = (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℤ) *
            positiveSupportBitAF (booleanMobiusSupport f) := by rw [hbit]
    _ = positiveSupportBitAF (booleanMobiusSupport f) *
          (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℤ) := by rw [mul_comm]
    _ = supportCoeffAF (booleanMobiusSupport f) :=
          positiveSupportBitAF_mul_zeta _

/-! ## Sharp divisor and support-coefficient growth -/

/-- Elementary divisor-pair estimate `τ(n) ≤ 2⌊√n⌋`, sharper than the
trivial `τ(n) ≤ n`.  The partition below pairs every divisor above the
square root with its complementary divisor below it. -/
theorem card_divisors_le_two_mul_sqrt (n : ℕ) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let small := n.divisors.filter fun d => d ≤ Nat.sqrt n
  let large := n.divisors.filter fun d => ¬ d ≤ Nat.sqrt n
  have hsplit : small.card + large.card = n.divisors.card := by
    simpa [small, large] using
      (Finset.card_filter_add_card_filter_not (s := n.divisors)
        (fun d => d ≤ Nat.sqrt n))
  have hsmallsub : small ⊆ Finset.Icc 1 (Nat.sqrt n) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hddiv, hdle⟩
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hddiv, hdle⟩
  have hsmall : small.card ≤ Nat.sqrt n := by
    calc
      small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card :=
        Finset.card_le_card hsmallsub
      _ = Nat.sqrt n := by simp [Nat.card_Icc]
  have hcomplement : ∀ {d : ℕ}, d ∈ n.divisors → n / (n / d) = d := by
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdle : d ≤ n := Nat.le_of_dvd hnpos hdvd
    have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
    have hqdvd : n / d ∣ n := Nat.div_dvd_of_dvd hdvd
    apply (Nat.div_eq_iff_eq_mul_left hqpos hqdvd).2
    exact (Nat.mul_div_cancel' hdvd).symm
  have hlargeinj : Set.InjOn (fun d : ℕ => n / d) (↑large : Set ℕ) := by
    intro a ha b hb hab
    have hadiv : a ∈ n.divisors := (Finset.mem_filter.mp ha).1
    have hbdiv : b ∈ n.divisors := (Finset.mem_filter.mp hb).1
    change n / a = n / b at hab
    calc
      a = n / (n / a) := (hcomplement hadiv).symm
      _ = n / (n / b) := by rw [hab]
      _ = b := hcomplement hbdiv
  have himagesub :
      large.image (fun d : ℕ => n / d) ⊆ Finset.Icc 1 (Nat.sqrt n) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨d, hdlarge, rfl⟩
    rcases Finset.mem_filter.mp hdlarge with ⟨hddiv, hdnot⟩
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hddiv).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hddiv
    have hdle : d ≤ n := Nat.le_of_dvd hnpos hdvd
    have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
    have hfactor : n = (n / d) * d := (Nat.div_mul_cancel hdvd).symm
    rcases Nat.le_sqrt_of_eq_mul hfactor with hqle | hdleS
    · exact Finset.mem_Icc.mpr ⟨hqpos, hqle⟩
    · exact False.elim (hdnot hdleS)
  have hlarge : large.card ≤ Nat.sqrt n := by
    calc
      large.card = (large.image (fun d : ℕ => n / d)).card :=
        (Finset.card_image_iff.mpr hlargeinj).symm
      _ ≤ (Finset.Icc 1 (Nat.sqrt n)).card := Finset.card_le_card himagesub
      _ = Nat.sqrt n := by simp [Nat.card_Icc]
  omega

/-- The support coefficient inherits the sharp divisor-pair envelope. -/
theorem supportCoeff_le_two_mul_sqrt (A : Set ℕ) (n : ℕ) :
    supportCoeff A n ≤ 2 * Nat.sqrt n :=
  le_trans (supportCoeff_le_card_divisors A n)
    (card_divisors_le_two_mul_sqrt n)

/-- The floor-square-root of a shifted index is controlled by the fixed
root plus the shift. -/
theorem sqrt_shift_le_sqrt_add_index (N j : ℕ) :
    Nat.sqrt (N + j + 1) ≤ Nat.sqrt N + j + 1 := by
  have hN := Nat.sqrt_le_add N
  have hsq : N + j + 1 ≤
      (Nat.sqrt N + j + 1) * (Nat.sqrt N + j + 1) := by
    nlinarith
  have h := Nat.sqrt_le_sqrt hsq
  simpa using h

/-- **Sharp support-tail strip.**  The scaled binary support-coefficient
tail grows at most like `2√N + 4`, exactly the envelope used by the
Boolean carry certificate below. -/
theorem binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    (A : Set ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff A) N ≤
      2 * Real.sqrt (N : ℝ) + 4 := by
  have hsum : Summable
      (fun j : ℕ ↦
        ((supportCoeff A (N + j + 1) : ℝ)) /
          (2 : ℝ) ^ (j + 1)) :=
    summable_coeff_shift_tail 2 N (supportCoeff A)
      (by norm_num) (supportCoeff_le_self A)
  have hcmp : Summable
      (fun j : ℕ ↦
        (((Nat.sqrt N + 1 : ℕ) : ℝ) + (j : ℝ)) *
          ((1 : ℝ) / 2) ^ j) :=
    summable_const_add_mul_geometric (Nat.sqrt N + 1)
      (by norm_num) (by norm_num)
  have hterm : ∀ j : ℕ,
      ((supportCoeff A (N + j + 1) : ℝ)) /
          (2 : ℝ) ^ (j + 1) ≤
        (((Nat.sqrt N + 1 : ℕ) : ℝ) + (j : ℝ)) *
          ((1 : ℝ) / 2) ^ j := by
    intro j
    have hcoeff : supportCoeff A (N + j + 1) ≤
        2 * (Nat.sqrt N + j + 1) :=
      (supportCoeff_le_two_mul_sqrt A (N + j + 1)).trans
        (Nat.mul_le_mul_left 2 (sqrt_shift_le_sqrt_add_index N j))
    have hcoeffR : (supportCoeff A (N + j + 1) : ℝ) ≤
        2 * ((Nat.sqrt N + j + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcoeff
    calc
      ((supportCoeff A (N + j + 1) : ℝ)) /
          (2 : ℝ) ^ (j + 1)
          ≤ (2 * ((Nat.sqrt N + j + 1 : ℕ) : ℝ)) /
              (2 : ℝ) ^ (j + 1) := by gcongr
      _ = (((Nat.sqrt N + 1 : ℕ) : ℝ) + (j : ℝ)) *
            ((1 : ℝ) / 2) ^ j := by
          push_cast
          rw [pow_succ, div_pow, one_pow]
          field_simp
          ring
  unfold binaryCoeffTail
  calc
    (∑' j : ℕ, ((supportCoeff A (N + j + 1) : ℝ)) /
        (2 : ℝ) ^ (j + 1))
        ≤ ∑' j : ℕ,
            (((Nat.sqrt N + 1 : ℕ) : ℝ) + (j : ℝ)) *
              ((1 : ℝ) / 2) ^ j :=
          Summable.tsum_le_tsum hterm hsum hcmp
    _ ≤ 2 * (((Nat.sqrt N + 1 : ℕ) : ℝ)) + 2 :=
      tsum_const_add_mul_geometric_le (Nat.sqrt N + 1)
        (by norm_num) (by norm_num)
    _ ≤ 2 * Real.sqrt (N : ℝ) + 4 := by
      have hsqrt : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      push_cast
      linarith

/-- A single positive support element forces every scaled coefficient tail
to be strictly positive. -/
theorem binaryCoeffTail_supportCoeff_pos_of_exists_pos_mem
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A) (N : ℕ) :
    0 < binaryCoeffTail (supportCoeff A) N := by
  obtain ⟨a, ha, haA⟩ := hA
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  let j : ℕ := k * (N + 1)
  have hidx : N + j + 1 = (k + 1) * (N + 1) := by
    dsimp [j]
    ring
  have hcoeff : 0 < supportCoeff A (N + j + 1) := by
    apply supportCoeff_pos_of_mem_dvd A haA
    · rw [hidx]
      exact dvd_mul_right (k + 1) (N + 1)
    · rw [hidx]
      positivity
  have hterm :
      (0 : ℝ) <
        (supportCoeff A (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) := by
    positivity
  have hsum := summable_coeff_shift_tail 2 N (supportCoeff A)
    (by norm_num) (supportCoeff_le_self A)
  unfold binaryCoeffTail
  exact lt_of_lt_of_le hterm (hsum.le_tsum j (fun i _ ↦ by positivity))

/-! ## Lambert-series and tail-orbit bridge -/

/-- At base two, the support Lambert series is literally the generic binary
coefficient series of `supportCoeff A`. -/
theorem erdosSupportSeries_two_eq_binaryCoeffSeries (A : Set ℕ) :
    erdosSupportSeries 2 A = binaryCoeffSeries (supportCoeff A) := by
  rw [erdosSupportSeries_eq_tsum_supportCoeff 2 A (by norm_num)]
  rfl

/-- Rationality of the support series is exactly existence of a tempered
integer carry orbit for its support coefficient. -/
theorem erdosSupportSeries_rational_iff_exists_temperedCarry (A : Set ℕ) :
    HasRationalValue (erdosSupportSeries 2 A) ↔
      ∃ q : ℕ, 0 < q ∧ ∃ U : ℕ → ℤ,
        IsTemperedBinaryOrbit (supportCoeff A) q U := by
  rw [erdosSupportSeries_two_eq_binaryCoeffSeries]
  exact binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (supportCoeff A) (supportCoeff_le_self A)

/-- A displayed fraction produces an orbit with that exact denominator.
The proof constructs the integer prefix orbit and identifies it with the
scaled analytic tail. -/
theorem exists_temperedCarry_of_support_fraction
    (A : Set ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) :
    ∃ U : ℕ → ℤ, U 0 = p ∧
      IsTemperedBinaryOrbit (supportCoeff A) q U := by
  let z : ℕ → ℤ := fun N ↦
    Classical.choose
      (bpow_mul_coeff_series_eq_int_add_tail 2 N (supportCoeff A)
        (by norm_num) (supportCoeff_le_self A))
  have hz : ∀ N : ℕ,
      (2 : ℝ) ^ N * binaryCoeffSeries (supportCoeff A) =
        (z N : ℝ) + binaryCoeffTail (supportCoeff A) N := by
    intro N
    exact Classical.choose_spec
      (bpow_mul_coeff_series_eq_int_add_tail 2 N (supportCoeff A)
        (by norm_num) (supportCoeff_le_self A))
  let U : ℕ → ℤ := fun N ↦ (2 : ℤ) ^ N * p - (q : ℤ) * z N
  have htail : ∀ N : ℕ,
      (U N : ℝ) = (q : ℝ) * binaryCoeffTail (supportCoeff A) N := by
    intro N
    have hN := hz N
    rw [← erdosSupportSeries_two_eq_binaryCoeffSeries A, hvalue] at hN
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hmul := congrArg (fun x : ℝ ↦ (q : ℝ) * x) hN
    change
      (q : ℝ) * ((2 : ℝ) ^ N * ((p : ℝ) / (q : ℝ))) =
        (q : ℝ) * ((z N : ℝ) + binaryCoeffTail (supportCoeff A) N) at hmul
    have hcancel :
        (q : ℝ) * ((2 : ℝ) ^ N * ((p : ℝ) / (q : ℝ))) =
          (2 : ℝ) ^ N * (p : ℝ) := by
      field_simp
    rw [hcancel] at hmul
    unfold U
    push_cast
    linarith
  refine ⟨U, ?_, ?_, ?_⟩
  · apply Int.cast_injective (α := ℝ)
    rw [htail 0, binaryCoeffTail_zero,
      ← erdosSupportSeries_two_eq_binaryCoeffSeries A, hvalue]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    field_simp
  · intro N
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [htail (N + 1), htail N,
      binaryCoeffTail_succ (supportCoeff A) (supportCoeff_le_self A) N]
    ring
  · have hlim :=
      (binaryCoeffTail_div_pow_tendsto_zero
        (supportCoeff A) (supportCoeff_le_self A)).const_mul (q : ℝ)
    convert hlim using 1
    · funext N
      rw [htail N]
      ring
    · simp

/-- Every tempered carry orbit with initial numerator `p` certifies the
displayed fraction `p/q`. -/
theorem support_fraction_of_temperedCarry
    (A : Set ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (hU0 : U 0 = p)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) :
    erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  have htail := temperedBinaryOrbit_eq_scaledTail
    (supportCoeff A) (supportCoeff_le_self A) horbit 0
  rw [binaryCoeffTail_zero, ← erdosSupportSeries_two_eq_binaryCoeffSeries A,
    hU0] at htail
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hq0).2
  nlinarith

/-- Fixed-fraction equivalence: the support series equals `p/q` exactly
when a tempered carry orbit with initial value `p` exists. -/
theorem support_fraction_iff_exists_temperedCarry
    (A : Set ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q) :
    erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) ↔
      ∃ U : ℕ → ℤ, U 0 = p ∧
        IsTemperedBinaryOrbit (supportCoeff A) q U := by
  constructor
  · exact exists_temperedCarry_of_support_fraction A p q hq
  · rintro ⟨U, hU0, hU⟩
    exact support_fraction_of_temperedCarry A p q hq U hU0 hU

/-- The exact carry difference in a support orbit. -/
theorem temperedCarry_difference
    (A : Set ℕ) (q : ℕ) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    2 * U N - U (N + 1) =
      (q : ℤ) * (supportCoeff A (N + 1) : ℤ) := by
  have hrec := horbit.1 N
  push_cast at hrec
  omega

/-- Divisibility of every carry difference by the displayed denominator. -/
theorem denominator_dvd_temperedCarry_difference
    (A : Set ℕ) (q : ℕ) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    (q : ℤ) ∣ 2 * U N - U (N + 1) := by
  rw [temperedCarry_difference A q U horbit N]
  exact dvd_mul_right _ _

/-- After exact division, the carry quotient is precisely `f_A(N+1)`. -/
theorem temperedCarry_quotient_eq_supportCoeff
    (A : Set ℕ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    (2 * U N - U (N + 1)) / (q : ℤ) =
      (supportCoeff A (N + 1) : ℤ) := by
  rw [temperedCarry_difference A q U horbit N]
  exact Int.mul_ediv_cancel_left _ (Int.ofNat_ne_zero.mpr hq.ne')

/-- A positive support and positive multiplier force every state of a
tempered support carry to be a positive integer. -/
theorem temperedCarry_pos_of_exists_pos_mem
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    0 < U N := by
  have htail := binaryCoeffTail_supportCoeff_pos_of_exists_pos_mem A hA N
  have hid := temperedBinaryOrbit_eq_scaledTail
    (supportCoeff A) (supportCoeff_le_self A) horbit N
  have hreal : (0 : ℝ) < (U N : ℝ) := by
    rw [hid]
    positivity
  exact_mod_cast hreal

/-- Every tempered support carry lies in the sharp square-root strip. -/
theorem temperedCarry_le_denominator_mul_two_sqrt_add_four
    (A : Set ℕ) (q : ℕ) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    (U N : ℝ) ≤
      (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4) := by
  rw [temperedBinaryOrbit_eq_scaledTail
    (supportCoeff A) (supportCoeff_le_self A) horbit N]
  exact mul_le_mul_of_nonneg_left
    (binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A N)
    (Nat.cast_nonneg q)

/-- The square-root strip is strong enough to enforce the tempered boundary;
the proof deliberately relaxes `√N` to `N+1` and uses the already checked
linear-over-exponential limit. -/
theorem tendsto_div_pow_zero_of_nonnegative_sqrt_bound
    (q : ℕ) (U : ℕ → ℤ)
    (hnonneg : ∀ N : ℕ, 0 ≤ U N)
    (hbound : ∀ N : ℕ, (U N : ℝ) ≤
      (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4)) :
    Tendsto (fun N : ℕ ↦ (U N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0) := by
  have hsqrt : ∀ N : ℕ, Real.sqrt (N : ℝ) ≤ (N : ℝ) + 1 := by
    intro N
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith
  have hNlim : Tendsto (fun N : ℕ ↦ (N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have h1lim : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have huplim : Tendsto
      (fun N : ℕ ↦ (q : ℝ) * (2 * (N : ℝ) + 6) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    have h := (hNlim.const_mul (2 * (q : ℝ))).add
      (h1lim.const_mul (6 * (q : ℝ)))
    convert h using 1
    · funext N
      ring
    · simp
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N ↦
      div_nonneg (by exact_mod_cast hnonneg N) (by positivity))
    (Filter.Eventually.of_forall fun N ↦ ?_)
    huplim
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    (U N : ℝ) ≤ (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4) := hbound N
    _ ≤ (q : ℝ) * (2 * ((N : ℝ) + 1) + 4) := by
      gcongr
      exact hsqrt N
    _ = (q : ℝ) * (2 * (N : ℝ) + 6) := by ring

/-! ## The quotient-facing certificate interface -/

/-- The normalized integer carry quotient.  Index zero is forced to zero;
at positive index `n` this is `(2U(n-1)-U(n))/q`. -/
def carryQuotient (q : ℕ) (U : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else (2 * U (n - 1) - U n) / (q : ℤ)

/-- The carry quotient packaged as an arithmetic function. -/
def carryQuotientAF (q : ℕ) (U : ℕ → ℤ) : ArithmeticFunction ℤ :=
  ⟨carryQuotient q U, by simp [carryQuotient]⟩

/-- The quotient-only Boolean carry certificate.  It mentions no support
set: Boolean Möbius inversion reconstructs the unique normalized support
afterwards. -/
structure BooleanMobiusCarryCertificate (p : ℤ) (q : ℕ) (U : ℕ → ℤ) : Prop where
  initial : U 0 = p
  positive : ∀ N : ℕ, 0 < U N
  sqrtBound : ∀ N : ℕ, (U N : ℝ) ≤
    (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4)
  divisible : ∀ N : ℕ, (q : ℤ) ∣ 2 * U N - U (N + 1)
  mobiusBoolean : ∀ n : ℕ, 0 < n →
    (ArithmeticFunction.moebius * carryQuotientAF q U) n = 0 ∨
      (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1

@[simp] theorem carryQuotient_zero (q : ℕ) (U : ℕ → ℤ) :
    carryQuotient q U 0 = 0 := by simp [carryQuotient]

/-- A tempered support carry recovers the whole divisor-count coefficient
through exact quotient extraction. -/
theorem carryQuotientAF_eq_supportCoeffAF
    (A : Set ℕ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) :
    carryQuotientAF q U = supportCoeffAF A := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [carryQuotientAF]
  · obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    change carryQuotient q U (N + 1) = (supportCoeff A (N + 1) : ℤ)
    rw [carryQuotient, if_neg (by omega)]
    simpa using temperedCarry_quotient_eq_supportCoeff A q hq U horbit N

/-- The Möbius transform of the carry quotient is the normalized support
bit: `μ * f_U = 1_A`. -/
theorem moebius_mul_carryQuotientAF
    (A : Set ℕ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) :
    ArithmeticFunction.moebius * carryQuotientAF q U =
      positiveSupportBitAF A := by
  rw [carryQuotientAF_eq_supportCoeffAF A q hq U horbit,
    moebius_mul_supportCoeffAF]

/-- Hence the Möbius transform of every exact carry quotient is Boolean. -/
theorem mobius_carryQuotient_boolean
    (A : Set ℕ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (n : ℕ) :
    (ArithmeticFunction.moebius * carryQuotientAF q U) n = 0 ∨
      (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1 := by
  rw [carryQuotientAF_eq_supportCoeffAF A q hq U horbit]
  exact mobius_supportCoeff_boolean A n

/-- With `0 ∉ A`, the carry quotient's Boolean Möbius transform recovers
the support literally as a set. -/
theorem mobius_carryQuotient_recovers_support
    (A : Set ℕ) (hzero : 0 ∉ A)
    (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) :
    {n : ℕ | (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A := by
  rw [carryQuotientAF_eq_supportCoeffAF A q hq U horbit]
  exact mobius_supportCoeff_recovers_support A hzero

/-- **Forward direction.**  A normalized nonempty support with value `p/q`
produces a positive square-root-bounded integer orbit whose differences are
divisible by `q`, whose carry quotient has Boolean Möbius transform, and
whose selected support is exactly the original `A`. -/
theorem exists_booleanMobiusCarry_of_support_fraction
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) :
    ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A := by
  obtain ⟨U, hU0, horbit⟩ :=
    exists_temperedCarry_of_support_fraction A p q hq hvalue
  refine ⟨U, ?_, ?_⟩
  · refine ⟨hU0, ?_, ?_, ?_, ?_⟩
    · exact fun N ↦ temperedCarry_pos_of_exists_pos_mem A hpos q hq U horbit N
    · exact fun N ↦
        temperedCarry_le_denominator_mul_two_sqrt_add_four A q U horbit N
    · exact fun N ↦
        denominator_dvd_temperedCarry_difference A q U horbit N
    · exact fun n _ ↦ mobius_carryQuotient_boolean A q hq U horbit n
  · exact mobius_carryQuotient_recovers_support A hzero q hq U horbit

/-- **Converse direction.**  A quotient-only Boolean carry certificate
reconstructs a normalized support `A` and certifies the exact value `p/q`;
`reconstructsSupport` below exposes the intermediate objects. -/
theorem support_fraction_of_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧ erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  let A := booleanMobiusSupport (carryQuotientAF q U)
  have hcoeff : carryQuotientAF q U = supportCoeffAF A :=
    eq_supportCoeffAF_booleanMobiusSupport_of_boolean
      (carryQuotientAF q U) cert.mobiusBoolean
  have hrec : ∀ N : ℕ,
      U (N + 1) = 2 * U N -
        ((q * supportCoeff A (N + 1) : ℕ) : ℤ) := by
    intro N
    have hquot :
        (2 * U N - U (N + 1)) / (q : ℤ) =
          (supportCoeff A (N + 1) : ℤ) := by
      have happ := congrArg
        (fun f : ArithmeticFunction ℤ ↦ f (N + 1)) hcoeff
      change carryQuotient q U (N + 1) =
        (supportCoeff A (N + 1) : ℤ) at happ
      rw [carryQuotient, if_neg (by omega)] at happ
      simpa using happ
    have hmul := Int.mul_ediv_cancel' (cert.divisible N)
    rw [hquot] at hmul
    push_cast
    omega
  have htemp : Tendsto (fun N : ℕ ↦ (U N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_div_pow_zero_of_nonnegative_sqrt_bound q U
      (fun N ↦ (cert.positive N).le) cert.sqrtBound
  have horbit : IsTemperedBinaryOrbit (supportCoeff A) q U := ⟨hrec, htemp⟩
  refine ⟨zero_not_mem_booleanMobiusSupport _, ?_⟩
  exact support_fraction_of_temperedCarry A p q hq U cert.initial horbit

/-- A quotient-only Boolean carry certificate exposes every reconstructed
object used by the converse, not only the final scalar identity. -/
theorem BooleanMobiusCarryCertificate.reconstructsSupport
    {p : ℤ} {q : ℕ} {U : ℕ → ℤ} (hq : 0 < q)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧
      carryQuotientAF q U = supportCoeffAF A ∧
      IsTemperedBinaryOrbit (supportCoeff A) q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A ∧
      erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  let A := booleanMobiusSupport (carryQuotientAF q U)
  have hzero : 0 ∉ A :=
    zero_not_mem_booleanMobiusSupport (carryQuotientAF q U)
  have hcoeff : carryQuotientAF q U = supportCoeffAF A := by
    simpa [A] using
      eq_supportCoeffAF_booleanMobiusSupport_of_boolean
        (carryQuotientAF q U) cert.mobiusBoolean
  have hrec : ∀ N : ℕ,
      U (N + 1) =
        2 * U N - ((q * supportCoeff A (N + 1) : ℕ) : ℤ) := by
    intro N
    have hquot := congrArg
      (fun f : ArithmeticFunction ℤ ↦ f (N + 1)) hcoeff
    change carryQuotient q U (N + 1) =
      (supportCoeff A (N + 1) : ℤ) at hquot
    rw [carryQuotient, if_neg (by omega)] at hquot
    have hqZ : (q : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hq.ne'
    have hdifference :
        2 * U N - U (N + 1) =
          (supportCoeff A (N + 1) : ℤ) * (q : ℤ) :=
      (Int.ediv_eq_iff_eq_mul_left hqZ (cert.divisible N)).mp hquot
    have hdifference' :
        2 * U N - U (N + 1) =
          (q : ℤ) * (supportCoeff A (N + 1) : ℤ) := by
      simpa [mul_comm] using hdifference
    push_cast
    omega
  have htemp := tendsto_div_pow_zero_of_nonnegative_sqrt_bound q U
    (fun N ↦ (cert.positive N).le) cert.sqrtBound
  have horbit : IsTemperedBinaryOrbit (supportCoeff A) q U :=
    ⟨hrec, htemp⟩
  have hrecovery :
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A :=
    mobius_carryQuotient_recovers_support A hzero q hq U horbit
  have hvalue : erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) :=
    support_fraction_of_temperedCarry A p q hq U cert.initial horbit
  exact ⟨hzero, hcoeff, horbit, hrecovery, hvalue⟩

/-- **Certificate-level equivalence.**  Positive normalized supports with
value `p/q` are in exact correspondence at the existence level with
quotient-only Boolean Möbius carry certificates.  The converse support is
not guessed: it is reconstructed as `booleanMobiusSupport` of the carry
quotient. -/
theorem exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U := by
  constructor
  · rintro ⟨A, hzero, hpos, hvalue⟩
    obtain ⟨U, cert, _⟩ :=
      exists_booleanMobiusCarry_of_support_fraction
        A hzero hpos p q hq hvalue
    exact ⟨U, cert⟩
  · rintro ⟨U, cert⟩
    let A := booleanMobiusSupport (carryQuotientAF q U)
    have hpair : 0 ∉ A ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
      simpa [A] using support_fraction_of_booleanMobiusCarry p q hq U cert
    have hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A := by
      by_contra hnone
      have hnone' : ∀ a : ℕ, 0 < a → a ∉ A := by
        intro a ha haA
        exact hnone ⟨a, ha, haA⟩
      have hAempty : A = ∅ := by
        ext n
        constructor
        · intro hnA
          have hnpos : 0 < n := by
            change 0 < n ∧
              (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1 at hnA
            exact hnA.1
          exact False.elim (hnone' n hnpos hnA)
        · simp
      have hvalue := hpair.2
      rw [hAempty] at hvalue
      have hzeroValue : (0 : ℝ) = (p : ℝ) / (q : ℝ) := by
        simpa [erdosSupportSeries] using hvalue
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      have hpcast : (p : ℝ) = 0 := by
        field_simp [hq0] at hzeroValue
        linarith
      have hpzero : p = 0 := by exact_mod_cast hpcast
      have hppos : 0 < p := by
        rw [← cert.initial]
        exact cert.positive 0
      omega
    exact ⟨A, hpair.1, hpos, hpair.2⟩

/-! ## Exact regression fixture: `A = {2,3}` -/

/-- The two-point support used in the explicit orbit check below. -/
def support23 : Set ℕ := {2, 3}

/-- The positive-index coefficient `f_{\{2,3\}}`, represented by its six
residue values.  Its value at zero is a table convenience and is never used
as an arithmetic-function value. -/
def supportCoeff23Residue (n : ℕ) : ℕ :=
  match n % 6 with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | _ => 0

/-- The pure period-six numerator orbit for `{2,3}`. -/
def carryOrbit23 (N : ℕ) : ℤ :=
  match N % 6 with
  | 0 => 10
  | 1 => 20
  | 2 => 19
  | 3 => 17
  | 4 => 13
  | _ => 26

private theorem mod_six_cases (n : ℕ) :
    n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨
      n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
  have h := Nat.mod_lt n (by norm_num : 0 < 6)
  omega

/-- Residue form equals the expected pair of divisibility indicators. -/
theorem supportCoeff23Residue_eq_divisibility (n : ℕ) :
    supportCoeff23Residue n =
      (if 2 ∣ n then 1 else 0) + (if 3 ∣ n then 1 else 0) := by
  rcases mod_six_cases n with h | h | h | h | h | h <;>
    simp [supportCoeff23Residue, h, Nat.dvd_iff_mod_eq_zero] <;>
    split_ifs <;> omega

/-- The residue table is not an auxiliary model: on positive integers it
is exactly the kernel's `supportCoeff` for `{2,3}`. -/
theorem supportCoeff_support23_eq_residue {n : ℕ} (hn : 0 < n) :
    supportCoeff support23 n = supportCoeff23Residue n := by
  classical
  unfold supportCoeff
  rw [Finset.card_filter]
  have hpoint : ∀ d : ℕ,
      (if d ∈ support23 then 1 else 0) =
        (if d = 2 then 1 else 0) + (if d = 3 then 1 else 0) := by
    intro d
    simp only [support23, Set.mem_insert_iff, Set.mem_singleton_iff]
    split_ifs <;> omega
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq',
    supportCoeff23Residue_eq_divisibility n]
  simp [Nat.mem_divisors, hn.ne']

/-- Exact value of the support series: `1/3 + 1/7 = 10/21`. -/
theorem erdosSupportSeries_support23_eq_ten_div_twenty_one :
    erdosSupportSeries 2 support23 = (10 : ℝ) / 21 := by
  unfold erdosSupportSeries
  rw [tsum_eq_sum (s := {2, 3})]
  · norm_num [support23, Set.indicator]
  · intro b hb
    rw [Set.indicator_of_notMem]
    simpa [support23] using hb

/-- The six listed orbit values, in their unambiguous order `U₀,...,U₅`. -/
theorem carryOrbit23_initial_cycle :
    carryOrbit23 0 = 10 ∧ carryOrbit23 1 = 20 ∧
      carryOrbit23 2 = 19 ∧ carryOrbit23 3 = 17 ∧
      carryOrbit23 4 = 13 ∧ carryOrbit23 5 = 26 := by
  norm_num [carryOrbit23]

/-- The orbit is purely periodic with period six. -/
theorem carryOrbit23_periodic (N : ℕ) :
    carryOrbit23 (N + 6) = carryOrbit23 N := by
  simp [carryOrbit23]

/-- Uniform positive bounds for the explicit orbit. -/
theorem carryOrbit23_bounds (N : ℕ) :
    10 ≤ carryOrbit23 N ∧ carryOrbit23 N ≤ 26 := by
  rcases mod_six_cases N with h | h | h | h | h | h <;>
    simp [carryOrbit23, h]

/-- Exact carry recurrence for the explicit orbit. -/
theorem carryOrbit23_recurrence (N : ℕ) :
    carryOrbit23 (N + 1) =
      2 * carryOrbit23 N -
        ((21 * supportCoeff support23 (N + 1) : ℕ) : ℤ) := by
  rw [supportCoeff_support23_eq_residue (by omega : 0 < N + 1)]
  rcases mod_six_cases N with h | h | h | h | h | h
  · have hs : (N + 1) % 6 = 1 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 2 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 3 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 4 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 5 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 0 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]

/-- The explicit six-cycle is a genuine tempered integer carry orbit, not
merely a finite recurrence check. -/
theorem carryOrbit23_isTempered :
    IsTemperedBinaryOrbit (supportCoeff support23) 21 carryOrbit23 := by
  refine ⟨carryOrbit23_recurrence, ?_⟩
  have hlim : Tendsto (fun N : ℕ ↦ (26 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N ↦ ?_)
    (Filter.Eventually.of_forall fun N ↦ ?_)
    hlim
  · apply div_nonneg
    · have h : (0 : ℤ) ≤ carryOrbit23 N :=
        le_trans (by norm_num) (carryOrbit23_bounds N).1
      exact_mod_cast h
    · positivity
  · apply div_le_div_of_nonneg_right
    · exact_mod_cast (carryOrbit23_bounds N).2
    · positivity

/-- The displayed fraction is reduced. -/
theorem ten_coprime_twenty_one : Nat.Coprime 10 21 := by norm_num

/-- Exact divisibility of every difference in the explicit six-cycle. -/
theorem twenty_one_dvd_carryOrbit23_difference (N : ℕ) :
    (21 : ℤ) ∣ 2 * carryOrbit23 N - carryOrbit23 (N + 1) :=
  denominator_dvd_temperedCarry_difference
    support23 21 carryOrbit23 carryOrbit23_isTempered N

/-- Exact quotient recovery in the explicit six-cycle. -/
theorem carryOrbit23_quotient_eq_supportCoeff (N : ℕ) :
    (2 * carryOrbit23 N - carryOrbit23 (N + 1)) / (21 : ℤ) =
      (supportCoeff support23 (N + 1) : ℤ) :=
  temperedCarry_quotient_eq_supportCoeff
    support23 21 (by norm_num) carryOrbit23 carryOrbit23_isTempered N

/-- The explicit quotient's Möbius transform recovers exactly `{2,3}`. -/
theorem mobius_carryOrbit23_recovers_support :
    {n : ℕ |
      (ArithmeticFunction.moebius * carryQuotientAF 21 carryOrbit23) n = 1} =
        support23 := by
  apply mobius_carryQuotient_recovers_support
    support23 (by norm_num [support23]) 21 (by norm_num)
      carryOrbit23 carryOrbit23_isTempered

/-- The analytic scaled-tail identity behind the six-cycle. -/
theorem carryOrbit23_eq_twenty_one_mul_tail (N : ℕ) :
    (carryOrbit23 N : ℝ) =
      21 * binaryCoeffTail (supportCoeff support23) N :=
  temperedBinaryOrbit_eq_scaledTail
    (supportCoeff support23) (supportCoeff_le_self support23)
      carryOrbit23_isTempered N

/-- The explicit orbit satisfies the sharp positive square-root strip. -/
theorem carryOrbit23_positive_and_sqrt_bounded (N : ℕ) :
    0 < carryOrbit23 N ∧
      (carryOrbit23 N : ℝ) ≤ 21 * (2 * Real.sqrt (N : ℝ) + 4) := by
  constructor
  · have h := (carryOrbit23_bounds N).1
    omega
  · exact temperedCarry_le_denominator_mul_two_sqrt_add_four
      support23 21 carryOrbit23 carryOrbit23_isTempered N

end Erdos249257
