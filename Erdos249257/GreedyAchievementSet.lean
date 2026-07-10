import Erdos249257.CertificateKernel
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Greedy geometry for the Mersenne achievement set

For positive exponents put `w(n) = 1 / (2^n - 1)` and let `T(n)` be the
mass strictly after exponent `n`.  The Mersenne achievement set is the set
of reals obtainable as subset sums of these weights.  This file formalizes
the greedy analysis of that set, supporting infrastructure for the study of
Erdős problem #257:

* summability, the exact tail recurrence, and strict superincreasingness
  (`mersenneTail_lt_weight`): every positive-index weight exceeds the
  entire tail after it;
* the quantitative gap asymptotic `w_n - T_n = (2/3)·4⁻ⁿ + O(8⁻ⁿ)`, with
  the explicit constant `3` (`mersenneGap_isBigOWith`);
* normalized support coding through the certificate kernel's
  `erdosSupportSeries` (`positiveMersenneSupportValue_eq_erdosSupportSeries`);
* exact real and rational greedy recurrences, agreeing under casting
  (`cast_greedyMersenneRemainderRat`);
* the greedy membership criterion
  (`mem_mersenneAchievementSet_iff_greedy_survival`): a real belongs to the
  achievement set exactly when it is nonnegative and every greedy residual
  is at most the remaining tail — the nonnegativity guard is necessary;
* finite rational upper enclosures for tails and sound death certificates
  (`certifiedGreedyMersenneDeath_not_mem`), with the exact level-one
  certificate excluding `3/4`
  (`three_fourths_not_mem_mersenneAchievementSet`);
* uniqueness of normalized support coding
  (`positiveMersenneSupportValue_injective_normalized`), and computable
  support bits for a rational value already known to belong to the
  achievement set (`rational_member_support_bit_iff`).

`CertifiedGreedyMersenneDeath` is one-sided: a certificate proves
nonmembership, while failure to find a certificate, or survival through any
finite depth, proves nothing about membership.  The index-zero support bit
is normalized away because its analytic weight is zero.  Nothing here
settles Erdős #257, and no finite computation is promoted to an
infinite-support claim.

The literature has not been audited for prior statements of these lemmas;
they are formal infrastructure, not claimed novelties.

NON_CLAIM: this module does not formalize the measure-one, perfect, or
nowhere-dense geometry of the achievement set.  In particular, the name
“fat Cantor set” is not promoted to a Lean-checked theorem here.
-/

namespace Erdos249257

open Filter Set

/-! ## Weights and tails -/

/-- The exact rational Mersenne weight `1 / (2^n - 1)`.  Its meaningful
support indices are positive; at index zero Lean's division convention gives
zero. -/
def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

/-- The real Mersenne weight `1 / (2^n - 1)`. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

@[simp] theorem mersenneWeightRat_zero : mersenneWeightRat 0 = 0 := by
  norm_num [mersenneWeightRat]

@[simp] theorem mersenneWeight_zero : mersenneWeight 0 = 0 := by
  norm_num [mersenneWeight]

@[simp] theorem cast_mersenneWeightRat (n : ℕ) :
    ((mersenneWeightRat n : ℚ) : ℝ) = mersenneWeight n := by
  simp [mersenneWeightRat, mersenneWeight]

theorem mersenneWeight_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneWeight n := by
  unfold mersenneWeight
  have hpow : (1 : ℝ) < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  exact one_div_pos.mpr (sub_pos.mpr hpow)

theorem mersenneWeightRat_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneWeightRat n := by
  unfold mersenneWeightRat
  have hpow : (1 : ℚ) < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  exact one_div_pos.mpr (sub_pos.mpr hpow)

/-- The positive-index Mersenne weights form a summable real series. -/
theorem summable_mersenneWeight :
    Summable (fun k : ℕ => mersenneWeight (k + 1)) := by
  simpa [mersenneWeight] using
    (summable_erdos_term 2 (by norm_num) (fun k : ℕ => k + 1)
      (fun _ _ h => Nat.add_lt_add_right h 1) (by norm_num))

/-- The remaining mass after processing exponents `1, ..., n`. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

theorem summable_mersenneTail (n : ℕ) :
    Summable (fun k : ℕ => mersenneWeight (n + k + 1)) := by
  have h := (summable_nat_add_iff n).mpr summable_mersenneWeight
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem mersenneTail_nonneg (n : ℕ) : 0 ≤ mersenneTail n := by
  unfold mersenneTail
  exact tsum_nonneg fun k => (mersenneWeight_pos (by omega : 0 < n + k + 1)).le

theorem mersenneTail_pos (n : ℕ) : 0 < mersenneTail n := by
  unfold mersenneTail
  exact (summable_mersenneTail n).tsum_pos
    (fun k => (mersenneWeight_pos (by omega : 0 < n + k + 1)).le)
    0 (mersenneWeight_pos (by omega : 0 < n + 0 + 1))

/-- Splitting off the next positive exponent gives the exact tail recurrence. -/
theorem mersenneTail_eq_weight_add (n : ℕ) :
    mersenneTail n = mersenneWeight (n + 1) + mersenneTail (n + 1) := by
  unfold mersenneTail
  rw [(summable_mersenneTail n).tsum_eq_zero_add]
  congr 1
  apply tsum_congr
  intro k
  congr 1
  omega

/-- Adjacent weights shrink by strictly more than a factor of two. -/
theorem two_mul_mersenneWeight_succ_lt {n : ℕ} (hn : 0 < n) :
    2 * mersenneWeight (n + 1) < mersenneWeight n := by
  have hx : (1 : ℝ) < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
    rw [pow_succ]
    ring
  rw [mersenneWeight, mersenneWeight, hpow]
  have hden₁ : (0 : ℝ) < 2 ^ n - 1 := by linarith
  have hden₂ : (0 : ℝ) < 2 * 2 ^ n - 1 := by linarith
  rw [mul_one_div, div_lt_div_iff₀ hden₂ hden₁]
  linarith

/-- Iterating the adjacent ratio gives a geometric envelope. -/
theorem mersenneWeight_add_le_geometric (n j : ℕ) (hn : 0 < n) :
    mersenneWeight (n + j) ≤ mersenneWeight n * ((1 : ℝ) / 2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := two_mul_mersenneWeight_succ_lt (n := n + j) (by omega)
      calc
        mersenneWeight (n + (j + 1)) = mersenneWeight (n + j + 1) := by
          congr 1
        _ ≤ mersenneWeight (n + j) / 2 := by linarith
        _ ≤ (mersenneWeight n * ((1 : ℝ) / 2) ^ j) / 2 := by linarith
        _ = mersenneWeight n * ((1 : ℝ) / 2) ^ (j + 1) := by
          rw [pow_succ]
          ring

/-- A simple closed-form upper enclosure for the remaining infinite tail. -/
theorem mersenneTail_le_two_mul_weight (n : ℕ) :
    mersenneTail n ≤ 2 * mersenneWeight (n + 1) := by
  have hf := summable_mersenneTail n
  have hg : Summable
      (fun k : ℕ => mersenneWeight (n + 1) * ((1 : ℝ) / 2) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)).mul_left _
  calc
    mersenneTail n
        ≤ ∑' k : ℕ, mersenneWeight (n + 1) * ((1 : ℝ) / 2) ^ k := by
          unfold mersenneTail
          exact hf.tsum_le_tsum
            (fun k => by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                mersenneWeight_add_le_geometric (n + 1) k (by omega)) hg
    _ = mersenneWeight (n + 1) *
          ∑' k : ℕ, ((1 : ℝ) / 2) ^ k := tsum_mul_left
    _ = 2 * mersenneWeight (n + 1) := by
      rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)]
      norm_num
      ring

/-- **Strict superincreasingness.**  Every positive-index weight is larger
than the entire tail following it. -/
theorem mersenneTail_lt_weight {n : ℕ} (hn : 0 < n) :
    mersenneTail n < mersenneWeight n := by
  exact lt_of_le_of_lt (mersenneTail_le_two_mul_weight n)
    (two_mul_mersenneWeight_succ_lt hn)

/-- The one-step enclosure is in fact strict. -/
theorem mersenneTail_lt_two_mul_weight (n : ℕ) :
    mersenneTail n < 2 * mersenneWeight (n + 1) := by
  rw [mersenneTail_eq_weight_add]
  have h := mersenneTail_lt_weight (n := n + 1) (by omega)
  linarith

/-- The remaining Mersenne mass tends to zero. -/
theorem tendsto_mersenneTail_zero :
    Tendsto mersenneTail atTop (nhds 0) := by
  have h := tendsto_sum_nat_add (fun k : ℕ => mersenneWeight (k + 1))
  have hshift := h.comp (tendsto_add_atTop_nat 0)
  simpa [mersenneTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift

/-! ## Quantitative gap asymptotic -/

/-- The contribution of geometric channels of order at least three in one
Mersenne weight. -/
noncomputable def mersenneWeightRemainder (n : ℕ) : ℝ :=
  ((1 : ℝ) / 8) ^ n / (1 - ((1 : ℝ) / 2) ^ n)

/-- Exact separation of the first two geometric channels. -/
theorem mersenneWeight_eq_two_channels_add_remainder
    {n : ℕ} (hn : 0 < n) :
    mersenneWeight n
      = ((1 : ℝ) / 2) ^ n
        + ((1 : ℝ) / 4) ^ n
        + mersenneWeightRemainder n := by
  have hpow : (1 : ℝ) < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  have hden : (2 : ℝ) ^ n - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hpow)
  have hpow0 : (2 : ℝ) ^ n ≠ 0 :=
    ne_of_gt (pow_pos (by norm_num) n)
  have hone : 1 - ((1 : ℝ) / 2) ^ n ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr
      (pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hn)))
  have hfour : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    conv_lhs => rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have height : (8 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 3 := by
    conv_lhs => rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  unfold mersenneWeight mersenneWeightRemainder
  simp only [div_pow, one_pow]
  rw [hfour, height]
  field_simp
  ring

theorem mersenneWeightRemainder_nonneg
    {n : ℕ} (hn : 0 < n) :
    0 ≤ mersenneWeightRemainder n := by
  unfold mersenneWeightRemainder
  exact div_nonneg (by positivity) (sub_nonneg.mpr (by
    exact
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans
        (by norm_num)))

/-- Uniform third-channel bound for one weight. -/
theorem mersenneWeightRemainder_le
    {n : ℕ} (hn : 0 < n) :
    mersenneWeightRemainder n ≤ 2 * ((1 : ℝ) / 8) ^ n := by
  have hxle : ((1 : ℝ) / 2) ^ n ≤ (1 : ℝ) / 2 := by
    calc
      ((1 : ℝ) / 2) ^ n ≤ ((1 : ℝ) / 2) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = (1 : ℝ) / 2 := pow_one _
  have hden : 0 < 1 - ((1 : ℝ) / 2) ^ n := by linarith
  unfold mersenneWeightRemainder
  rw [div_le_iff₀ hden]
  have ha : 0 ≤ ((1 : ℝ) / 8) ^ n := by positivity
  nlinarith

/-- A shifted geometric series in the form used by all three channels. -/
theorem tsum_geometric_nat_add_succ
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑' k : ℕ, r ^ (n + k + 1) = r ^ (n + 1) * (1 - r)⁻¹ := by
  calc
    ∑' k : ℕ, r ^ (n + k + 1)
        = ∑' k : ℕ, r ^ (n + 1) * r ^ k := by
          apply tsum_congr
          intro k
          rw [← pow_add]
          congr 1
          omega
    _ = r ^ (n + 1) * ∑' k : ℕ, r ^ k := tsum_mul_left
    _ = r ^ (n + 1) * (1 - r)⁻¹ := by
      rw [tsum_geometric_of_lt_one hr0 hr1]

theorem tsum_half_nat_add_succ (n : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 2) ^ (n + k + 1) = ((1 : ℝ) / 2) ^ n := by
  rw [tsum_geometric_nat_add_succ _ (by norm_num) (by norm_num)]
  rw [pow_succ]
  norm_num
  ring

theorem tsum_quarter_nat_add_succ (n : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 4) ^ (n + k + 1)
      = (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n := by
  rw [tsum_geometric_nat_add_succ _ (by norm_num) (by norm_num)]
  rw [pow_succ]
  norm_num
  ring

theorem tsum_eighth_nat_add_succ (n : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 8) ^ (n + k + 1)
      = (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n := by
  rw [tsum_geometric_nat_add_succ _ (by norm_num) (by norm_num)]
  rw [pow_succ]
  norm_num
  ring

/-- The accumulated contribution of channels of order at least three after
exponent `n`. -/
noncomputable def mersenneWeightRemainderTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeightRemainder (n + k + 1)

theorem summable_mersenneWeightRemainderTail (n : ℕ) :
    Summable (fun k : ℕ => mersenneWeightRemainder (n + k + 1)) := by
  have hgeo : Summable (fun k : ℕ =>
      2 * ((1 : ℝ) / 8) ^ (n + k + 1)) := by
    have hbase := summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
    have hshift := (summable_nat_add_iff (n + 1)).mpr hbase
    have hmul := hshift.mul_left 2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul
  exact Summable.of_nonneg_of_le
    (fun k => mersenneWeightRemainder_nonneg (by omega))
    (fun k => mersenneWeightRemainder_le (by omega)) hgeo

theorem mersenneWeightRemainderTail_nonneg (n : ℕ) :
    0 ≤ mersenneWeightRemainderTail n := by
  unfold mersenneWeightRemainderTail
  exact tsum_nonneg fun k => mersenneWeightRemainder_nonneg (by omega)

/-- The accumulated higher-channel tail is at most `(2/7)·8⁻ⁿ`. -/
theorem mersenneWeightRemainderTail_le (n : ℕ) :
    mersenneWeightRemainderTail n
      ≤ (2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n := by
  have henv : Summable (fun k : ℕ =>
      2 * ((1 : ℝ) / 8) ^ (n + k + 1)) := by
    have hbase := summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
    have hshift := (summable_nat_add_iff (n + 1)).mpr hbase
    have hmul := hshift.mul_left 2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul
  calc
    mersenneWeightRemainderTail n
        ≤ ∑' k : ℕ, 2 * ((1 : ℝ) / 8) ^ (n + k + 1) := by
          unfold mersenneWeightRemainderTail
          exact (summable_mersenneWeightRemainderTail n).tsum_le_tsum
            (fun k => mersenneWeightRemainder_le (by omega)) henv
    _ = 2 * ∑' k : ℕ, ((1 : ℝ) / 8) ^ (n + k + 1) := tsum_mul_left
    _ = (2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n := by
      rw [tsum_eighth_nat_add_succ]
      ring

/-- Exact tail expansion through the second geometric channel. -/
theorem mersenneTail_eq_two_channels_add_remainderTail (n : ℕ) :
    mersenneTail n
      = ((1 : ℝ) / 2) ^ n
        + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
        + mersenneWeightRemainderTail n := by
  have hhalf : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (n + k + 1)) := by
    have hbase := summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have hshift := (summable_nat_add_iff (n + 1)).mpr hbase
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hquarter : Summable (fun k : ℕ => ((1 : ℝ) / 4) ^ (n + k + 1)) := by
    have hbase := summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 : ℝ) / 4 < 1)
    have hshift := (summable_nat_add_iff (n + 1)).mpr hbase
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hrem := summable_mersenneWeightRemainderTail n
  calc
    mersenneTail n
        = ∑' k : ℕ, (((1 : ℝ) / 2) ^ (n + k + 1)
            + ((1 : ℝ) / 4) ^ (n + k + 1)
            + mersenneWeightRemainder (n + k + 1)) := by
          unfold mersenneTail
          apply tsum_congr
          intro k
          exact mersenneWeight_eq_two_channels_add_remainder (by omega)
    _ = (∑' k : ℕ, ((1 : ℝ) / 2) ^ (n + k + 1))
          + (∑' k : ℕ, ((1 : ℝ) / 4) ^ (n + k + 1))
          + ∑' k : ℕ, mersenneWeightRemainder (n + k + 1) := by
          rw [(hhalf.add hquarter).tsum_add hrem, hhalf.tsum_add hquarter]
    _ = ((1 : ℝ) / 2) ^ n
          + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
          + mersenneWeightRemainderTail n := by
          rw [tsum_half_nat_add_succ, tsum_quarter_nat_add_succ]
          rfl

/-- The Mersenne gap has leading term `(2/3)·4⁻ⁿ`; its exact error is the
difference of the one-weight and tail higher-channel remainders. -/
theorem mersenneGap_sub_main_eq_remainder_sub_tail
    {n : ℕ} (hn : 0 < n) :
    (mersenneWeight n - mersenneTail n)
        - (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
      = mersenneWeightRemainder n - mersenneWeightRemainderTail n := by
  rw [mersenneWeight_eq_two_channels_add_remainder hn,
    mersenneTail_eq_two_channels_add_remainderTail]
  ring

/-- Explicit norm certificate for the gap asymptotic. -/
theorem mersenneGap_asymptotic_bound {n : ℕ} (hn : 0 < n) :
    ‖(mersenneWeight n - mersenneTail n)
        - (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n‖
      ≤ 3 * ‖((1 : ℝ) / 8) ^ n‖ := by
  rw [mersenneGap_sub_main_eq_remainder_sub_tail hn]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hR0 := mersenneWeightRemainder_nonneg hn
  have hT0 := mersenneWeightRemainderTail_nonneg n
  have hR := mersenneWeightRemainder_le hn
  have hT := mersenneWeightRemainderTail_le n
  have hpow : 0 ≤ ((1 : ℝ) / 8) ^ n := by positivity
  calc
    |mersenneWeightRemainder n - mersenneWeightRemainderTail n|
        ≤ |mersenneWeightRemainder n| + |mersenneWeightRemainderTail n| :=
          abs_sub _ _
    _ = mersenneWeightRemainder n + mersenneWeightRemainderTail n := by
      rw [abs_of_nonneg hR0, abs_of_nonneg hT0]
    _ ≤ 2 * ((1 : ℝ) / 8) ^ n
          + (2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n := add_le_add hR hT
    _ ≤ 3 * |((1 : ℝ) / 8) ^ n| := by
      rw [abs_of_nonneg hpow]
      nlinarith

/-- **Gap asymptotic.**  In positive indexing,
`w_n - T_n = (2/3)·4⁻ⁿ + O(8⁻ⁿ)`, with an explicit valid `O` constant `3`. -/
theorem mersenneGap_isBigOWith :
    Asymptotics.IsBigOWith 3 atTop
      (fun n : ℕ =>
        (mersenneWeight n - mersenneTail n)
          - (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n)
      (fun n : ℕ => ((1 : ℝ) / 8) ^ n) := by
  apply Asymptotics.IsBigOWith.of_bound
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact mersenneGap_asymptotic_bound (by omega)

/-! ## Normalized support coding -/

/-- The value coded by a set of positive exponents.  The sequence index is
zero-based while the exponent supplied to the weight is `k+1`. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

theorem summable_positiveMersenneSupportIndicator (A : Set ℕ) :
    Summable (fun k : ℕ => Set.indicator A mersenneWeight (k + 1)) := by
  have h := summable_mersenneWeight.indicator {k : ℕ | k + 1 ∈ A}
  refine h.congr fun k => ?_
  by_cases hk : k + 1 ∈ A
  · simp [hk]
  · simp [hk]

/-- The portion of a support code strictly after exponent `n`. -/
noncomputable def positiveMersenneSupportSuffix (A : Set ℕ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (n + k + 1)

theorem summable_positiveMersenneSupportSuffix (A : Set ℕ) (n : ℕ) :
    Summable (fun k : ℕ => Set.indicator A mersenneWeight (n + k + 1)) := by
  have h := (summable_nat_add_iff n).mpr
    (summable_positiveMersenneSupportIndicator A)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem positiveMersenneSupportSuffix_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ positiveMersenneSupportSuffix A n := by
  unfold positiveMersenneSupportSuffix
  exact tsum_nonneg fun k => by
    by_cases hk : n + k + 1 ∈ A
    · rw [Set.indicator_of_mem hk]
      exact (mersenneWeight_pos (by omega)).le
    · rw [Set.indicator_of_notMem hk]

/-- A coded suffix is bounded by the full remaining mass. -/
theorem positiveMersenneSupportSuffix_le_tail (A : Set ℕ) (n : ℕ) :
    positiveMersenneSupportSuffix A n ≤ mersenneTail n := by
  unfold positiveMersenneSupportSuffix mersenneTail
  exact (summable_positiveMersenneSupportSuffix A n).tsum_le_tsum
    (fun k => by
      by_cases hk : n + k + 1 ∈ A
      · rw [Set.indicator_of_mem hk]
      · rw [Set.indicator_of_notMem hk]
        exact (mersenneWeight_pos (by omega)).le)
    (summable_mersenneTail n)

/-- Exact recurrence for a coded support suffix. -/
theorem positiveMersenneSupportSuffix_eq_indicator_add
    (A : Set ℕ) (n : ℕ) :
    positiveMersenneSupportSuffix A n
      = Set.indicator A mersenneWeight (n + 1)
        + positiveMersenneSupportSuffix A (n + 1) := by
  unfold positiveMersenneSupportSuffix
  rw [(summable_positiveMersenneSupportSuffix A n).tsum_eq_zero_add]
  congr 1
  apply tsum_congr
  intro k
  congr 2
  omega

/-- Finite-prefix decomposition of a normalized support code. -/
theorem positiveMersenneSupportValue_eq_prefix_add_suffix
    (A : Set ℕ) (n : ℕ) :
    positiveMersenneSupportValue A
      = (∑ k ∈ Finset.range n, Set.indicator A mersenneWeight (k + 1))
        + positiveMersenneSupportSuffix A n := by
  have h := (summable_positiveMersenneSupportIndicator A).sum_add_tsum_nat_add n
  simpa [positiveMersenneSupportValue, positiveMersenneSupportSuffix,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

/-- The reindexed support value is exactly the certificate kernel's #257
support series. -/
theorem positiveMersenneSupportValue_eq_erdosSupportSeries (A : Set ℕ) :
    positiveMersenneSupportValue A = erdosSupportSeries 2 A := by
  have hwhole : Summable (fun a : ℕ => Set.indicator A mersenneWeight a) := by
    refine (summable_erdosSupport_indicator 2 A (by norm_num)).congr fun a => ?_
    rfl
  have hsplit := hwhole.tsum_eq_zero_add
  have hzero : Set.indicator A mersenneWeight 0 = 0 := by
    by_cases hA : 0 ∈ A <;> simp [hA]
  calc
    positiveMersenneSupportValue A
        = ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1) := rfl
    _ = ∑' k : ℕ, Set.indicator A mersenneWeight k := by
      simpa [hzero] using hsplit.symm
    _ = erdosSupportSeries 2 A := by rfl

/-- The Mersenne achievement set, with the analytically invisible zero bit
normalized away. -/
def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

/-! ## Exact greedy recurrences -/

/-- Real greedy residual after processing exponents `1, ..., n`. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

/-- Exact rational version of the greedy residual. -/
def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n

@[simp] theorem greedyMersenneRemainder_zero (x : ℝ) :
    greedyMersenneRemainder x 0 = x := rfl

@[simp] theorem greedyMersenneRemainderRat_zero (x : ℚ) :
    greedyMersenneRemainderRat x 0 = x := rfl

theorem greedyMersenneRemainder_succ (x : ℝ) (n : ℕ) :
    greedyMersenneRemainder x (n + 1)
      = if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
          greedyMersenneRemainder x n - mersenneWeight (n + 1)
        else greedyMersenneRemainder x n := rfl

theorem greedyMersenneRemainderRat_succ (x : ℚ) (n : ℕ) :
    greedyMersenneRemainderRat x (n + 1)
      = if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
          greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
        else greedyMersenneRemainderRat x n := rfl

/-- Greedy subtraction preserves nonnegativity. -/
theorem greedyMersenneRemainder_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ greedyMersenneRemainder x n := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [greedyMersenneRemainder_succ]
      split_ifs with h
      · linarith
      · exact ih

/-- Rational and real greedy execution agree exactly under casting. -/
@[simp] theorem cast_greedyMersenneRemainderRat (x : ℚ) (n : ℕ) :
    ((greedyMersenneRemainderRat x n : ℚ) : ℝ)
      = greedyMersenneRemainder (x : ℝ) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [greedyMersenneRemainderRat_succ, greedyMersenneRemainder_succ]
      by_cases h : mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n
      · have h' : mersenneWeight (n + 1)
            ≤ greedyMersenneRemainder (x : ℝ) n := by
          have hc : ((mersenneWeightRat (n + 1) : ℚ) : ℝ)
              ≤ ((greedyMersenneRemainderRat x n : ℚ) : ℝ) := by
            exact_mod_cast h
          rw [← ih]
          simpa using hc
        rw [if_pos h, if_pos h']
        push_cast
        rw [cast_mersenneWeightRat, ih]
      · have h' : ¬ mersenneWeight (n + 1)
            ≤ greedyMersenneRemainder (x : ℝ) n := by
          intro hreal
          apply h
          rw [← ih] at hreal
          have hc : ((mersenneWeightRat (n + 1) : ℚ) : ℝ)
              ≤ ((greedyMersenneRemainderRat x n : ℚ) : ℝ) := by
            simpa using hreal
          exact_mod_cast hc
        rw [if_neg h, if_neg h', ih]

/-- The set of positive exponents selected by the real greedy recursion. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

@[simp] theorem zero_not_mem_greedyMersenneSupport (x : ℝ) :
    0 ∉ greedyMersenneSupport x := by
  simp [greedyMersenneSupport]

@[simp] theorem succ_mem_greedyMersenneSupport_iff (x : ℝ) (n : ℕ) :
    n + 1 ∈ greedyMersenneSupport x
      ↔ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n := by
  simp [greedyMersenneSupport]

/-- Exact finite-prefix identity for the real greedy recursion. -/
theorem greedyMersenne_prefix_add_remainder (x : ℝ) (n : ℕ) :
    x = (∑ k ∈ Finset.range n,
          Set.indicator (greedyMersenneSupport x) mersenneWeight (k + 1))
        + greedyMersenneRemainder x n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n
      · rw [Set.indicator_of_mem ((succ_mem_greedyMersenneSupport_iff x n).2 h),
          greedyMersenneRemainder_succ, if_pos h]
        linarith
      · rw [Set.indicator_of_notMem (by
            simpa only [succ_mem_greedyMersenneSupport_iff] using h),
          greedyMersenneRemainder_succ, if_neg h, add_zero]
        exact ih

/-! ## Recovery, survival, and uniqueness -/

/-- On a genuine support value, the greedy residual is exactly the unprocessed
support suffix. -/
theorem greedyMersenneRemainder_supportValue (A : Set ℕ) (n : ℕ) :
    greedyMersenneRemainder (positiveMersenneSupportValue A) n
      = positiveMersenneSupportSuffix A n := by
  induction n with
  | zero => simp [positiveMersenneSupportValue, positiveMersenneSupportSuffix]
  | succ n ih =>
      rw [greedyMersenneRemainder_succ, ih,
        positiveMersenneSupportSuffix_eq_indicator_add]
      by_cases hA : n + 1 ∈ A
      · rw [Set.indicator_of_mem hA]
        have hnonneg := positiveMersenneSupportSuffix_nonneg A (n + 1)
        have htake : mersenneWeight (n + 1)
            ≤ mersenneWeight (n + 1) + positiveMersenneSupportSuffix A (n + 1) := by
          linarith
        rw [if_pos htake]
        ring
      · rw [Set.indicator_of_notMem hA, zero_add]
        have hsuffix := positiveMersenneSupportSuffix_le_tail A (n + 1)
        have htail := mersenneTail_lt_weight (n := n + 1) (by omega)
        have hskip : ¬ mersenneWeight (n + 1)
            ≤ positiveMersenneSupportSuffix A (n + 1) := by
          linarith
        rw [if_neg hskip]

/-- Greedy selection recovers every positive bit of a representing support. -/
theorem succ_mem_greedySupport_supportValue_iff (A : Set ℕ) (n : ℕ) :
    n + 1 ∈ greedyMersenneSupport (positiveMersenneSupportValue A)
      ↔ n + 1 ∈ A := by
  rw [succ_mem_greedyMersenneSupport_iff,
    greedyMersenneRemainder_supportValue]
  constructor
  · intro htake
    by_contra hA
    have hsuffix := positiveMersenneSupportSuffix_le_tail A (n + 1)
    have htail := mersenneTail_lt_weight (n := n + 1) (by omega)
    rw [positiveMersenneSupportSuffix_eq_indicator_add,
      Set.indicator_of_notMem hA, zero_add] at htake
    linarith
  · intro hA
    rw [positiveMersenneSupportSuffix_eq_indicator_add,
      Set.indicator_of_mem hA]
    have hnonneg := positiveMersenneSupportSuffix_nonneg A (n + 1)
    linarith

/-- A normalized support is recovered exactly, including the forced-zero bit
at exponent zero. -/
theorem greedySupport_supportValue_eq (A : Set ℕ) (hA0 : 0 ∉ A) :
    greedyMersenneSupport (positiveMersenneSupportValue A) = A := by
  ext m
  rcases m with _ | n
  · simp [hA0]
  · simpa [Nat.succ_eq_add_one] using succ_mem_greedySupport_supportValue_iff A n

/-- Every support value is nonnegative. -/
theorem positiveMersenneSupportValue_nonneg (A : Set ℕ) :
    0 ≤ positiveMersenneSupportValue A := by
  rw [positiveMersenneSupportValue_eq_prefix_add_suffix A 0]
  simpa using positiveMersenneSupportSuffix_nonneg A 0

/-- Membership implies the exact all-level upper-tail survival inequalities. -/
theorem greedy_survives_of_mem_mersenneAchievementSet {x : ℝ}
    (hx : x ∈ mersenneAchievementSet) :
    0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  rcases hx with ⟨A, hA0, rfl⟩
  refine ⟨positiveMersenneSupportValue_nonneg A, fun n => ?_⟩
  rw [greedyMersenneRemainder_supportValue]
  exact positiveMersenneSupportSuffix_le_tail A n

/-- If every greedy residual stays at or below the remaining mass, the
residuals converge to zero.  The nonnegativity guard excludes the false
negative-target variant. -/
theorem tendsto_greedyMersenneRemainder_zero {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    Tendsto (greedyMersenneRemainder x) atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_mersenneTail_zero
    (Filter.Eventually.of_forall fun n => greedyMersenneRemainder_nonneg hx n)
    (Filter.Eventually.of_forall hsurvive)

/-- All-level survival constructs a genuine normalized support code. -/
theorem mem_mersenneAchievementSet_of_greedy_survival {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    x ∈ mersenneAchievementSet := by
  let A := greedyMersenneSupport x
  have hsum := summable_positiveMersenneSupportIndicator A
  have htoSum : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        Set.indicator A mersenneWeight (k + 1)) atTop
      (nhds (positiveMersenneSupportValue A)) := by
    simpa [positiveMersenneSupportValue] using hsum.tendsto_sum_tsum_nat
  have hrem := tendsto_greedyMersenneRemainder_zero hx hsurvive
  have htoX : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        Set.indicator A mersenneWeight (k + 1)) atTop (nhds x) := by
    have hsub : Tendsto (fun n : ℕ => x - greedyMersenneRemainder x n)
        atTop (nhds (x - 0)) := tendsto_const_nhds.sub hrem
    convert hsub using 1
    · funext n
      have hprefix := greedyMersenne_prefix_add_remainder x n
      change (∑ k ∈ Finset.range n,
        Set.indicator (greedyMersenneSupport x) mersenneWeight (k + 1))
          = x - greedyMersenneRemainder x n
      linarith
    · simp
  have hvalue : positiveMersenneSupportValue A = x :=
    tendsto_nhds_unique htoSum htoX
  exact ⟨A, zero_not_mem_greedyMersenneSupport x, hvalue.symm⟩

/-- **Greedy membership criterion.**  A real target belongs to the Mersenne
achievement set exactly when it is nonnegative and every residual is at most
the full remaining tail. -/
theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  constructor
  · exact greedy_survives_of_mem_mersenneAchievementSet
  · rintro ⟨hx, hsurvive⟩
    exact mem_mersenneAchievementSet_of_greedy_survival hx hsurvive

/-- Strict superincreasingness makes normalized support coding injective. -/
theorem positiveMersenneSupportValue_injective_normalized
    {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    (hvalue : positiveMersenneSupportValue A = positiveMersenneSupportValue B) :
    A = B := by
  rw [← greedySupport_supportValue_eq A hA0,
    ← greedySupport_supportValue_eq B hB0, hvalue]

/-- The support coding through the existing #257 series is likewise unique
after the zero-bit normalization. -/
theorem erdosSupportSeries_two_injective_normalized
    {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    (hvalue : erdosSupportSeries 2 A = erdosSupportSeries 2 B) :
    A = B := by
  apply positiveMersenneSupportValue_injective_normalized hA0 hB0
  simpa only [positiveMersenneSupportValue_eq_erdosSupportSeries] using hvalue

/-! ## Finite exact-rational death certificates -/

/-- Split a tail after any finite lookahead. -/
theorem mersenneTail_eq_prefix_add_tail (n lookahead : ℕ) :
    mersenneTail n
      = (∑ k ∈ Finset.range lookahead, mersenneWeight (n + k + 1))
        + mersenneTail (n + lookahead) := by
  have h := (summable_mersenneTail n).sum_add_tsum_nat_add lookahead
  simpa [mersenneTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

/-- A finite rational upper enclosure for `mersenneTail n`.  The lookahead
parameter exposes a family of exact rational bounds without comparing an
infinite real tail numerically. -/
def mersenneTailUpperRat (n lookahead : ℕ) : ℚ :=
  (∑ k ∈ Finset.range lookahead, mersenneWeightRat (n + k + 1))
    + 2 * mersenneWeightRat (n + lookahead + 1)

/-- Every finite rational enclosure lies strictly above the actual tail. -/
theorem mersenneTail_lt_cast_tailUpperRat (n lookahead : ℕ) :
    mersenneTail n < ((mersenneTailUpperRat n lookahead : ℚ) : ℝ) := by
  rw [mersenneTail_eq_prefix_add_tail]
  have htail := mersenneTail_lt_two_mul_weight (n + lookahead)
  have hcast : ((mersenneTailUpperRat n lookahead : ℚ) : ℝ)
      = (∑ k ∈ Finset.range lookahead, mersenneWeight (n + k + 1))
        + 2 * mersenneWeight (n + lookahead + 1) := by
    unfold mersenneTailUpperRat
    push_cast
    simp
  rw [hcast]
  linarith

/-- Semantic greedy death: the residual at the given level is already larger
than all remaining available mass. -/
def GreedyMersenneDeath (x : ℝ) (level : ℕ) : Prop :=
  mersenneTail level < greedyMersenneRemainder x level

/-- Any semantic death level proves nonmembership. -/
theorem greedyMersenneDeath_not_mem {x : ℝ} {level : ℕ}
    (hdeath : GreedyMersenneDeath x level) :
    x ∉ mersenneAchievementSet := by
  intro hx
  have hsurvive := (mem_mersenneAchievementSet_iff_greedy_survival x).mp hx
  exact (not_lt_of_ge (hsurvive.2 level)) hdeath

/-- A decidable finite certificate: an exact rational upper enclosure is no
larger than the exact rational greedy residual. -/
def CertifiedGreedyMersenneDeath
    (x : ℚ) (level lookahead : ℕ) : Prop :=
  mersenneTailUpperRat level lookahead
    ≤ greedyMersenneRemainderRat x level

/-- Every finite exact-rational death certificate is sound. -/
theorem certifiedGreedyMersenneDeath_not_mem
    {x : ℚ} {level lookahead : ℕ}
    (hcert : CertifiedGreedyMersenneDeath x level lookahead) :
    ((x : ℚ) : ℝ) ∉ mersenneAchievementSet := by
  apply greedyMersenneDeath_not_mem
  unfold GreedyMersenneDeath
  have htail := mersenneTail_lt_cast_tailUpperRat level lookahead
  have hcertReal : ((mersenneTailUpperRat level lookahead : ℚ) : ℝ)
      ≤ ((greedyMersenneRemainderRat x level : ℚ) : ℝ) := by
    exact_mod_cast hcert
  rw [cast_greedyMersenneRemainderRat] at hcertReal
  exact lt_of_lt_of_le htail hcertReal

/-- **Exact level-one certificate.**  Greedy skips weight `w₁=1` at `3/4`,
leaving residual `3/4`; the zero-lookahead enclosure of the remaining tail is
`2*w₂ = 2/3`. -/
theorem three_fourths_certifiedGreedyMersenneDeath :
    CertifiedGreedyMersenneDeath (3 / 4 : ℚ) 1 0 := by
  norm_num [CertifiedGreedyMersenneDeath, mersenneTailUpperRat,
    greedyMersenneRemainderRat, mersenneWeightRat]

/-- Consequently `3/4` is not in the Mersenne achievement set. -/
theorem three_fourths_not_mem_mersenneAchievementSet :
    (3 / 4 : ℝ) ∉ mersenneAchievementSet := by
  simpa using certifiedGreedyMersenneDeath_not_mem
    (x := (3 / 4 : ℚ)) (level := 1) (lookahead := 0)
      three_fourths_certifiedGreedyMersenneDeath

/-! ## Rational greedy prefixes and computable digits -/

/-- Positive exponents selected through a finite exact-rational greedy run. -/
def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)

@[simp] theorem zero_not_mem_greedyMersennePrefixRat (x : ℚ) (n : ℕ) :
    0 ∉ greedyMersennePrefixRat x n := by
  classical
  simp [greedyMersennePrefixRat]

/-- Exact telescoping identity for a finite rational greedy run. -/
theorem greedyMersenneRat_prefix_add_remainder (x : ℚ) (n : ℕ) :
    x = (∑ k ∈ Finset.range n,
          if mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k then
            mersenneWeightRat (k + 1)
          else 0)
        + greedyMersenneRemainderRat x n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, greedyMersenneRemainderRat_succ]
      by_cases h : mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n
      · rw [if_pos h, if_pos h]
        linarith
      · rw [if_neg h, if_neg h, add_zero]
        exact ih

/-- The finite prefix selected by the rational greedy run is exactly an
instance of the certificate kernel's `finiteErdosSum`. -/
theorem finiteErdosSum_greedyMersennePrefixRat (x : ℚ) (n : ℕ) :
    finiteErdosSum (greedyMersennePrefixRat x n) 2
      = ∑ k ∈ Finset.range n,
          if mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k then
            mersenneWeightRat (k + 1)
          else 0 := by
  classical
  unfold finiteErdosSum greedyMersennePrefixRat
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    rfl
  · exact Set.injOn_of_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)

/-- Exact interface to the certificate kernel: the rational greedy residual
is the target minus a `finiteErdosSum`. -/
theorem greedyMersenneRemainderRat_eq_sub_finiteErdosSum
    (x : ℚ) (n : ℕ) :
    greedyMersenneRemainderRat x n
      = x - finiteErdosSum (greedyMersennePrefixRat x n) 2 := by
  have hprefix := greedyMersenneRat_prefix_add_remainder x n
  rw [finiteErdosSum_greedyMersennePrefixRat]
  linarith

/-- A rational comparison decides exactly the same greedy bit as the real
comparison after casting. -/
theorem rational_greedy_take_iff_real (x : ℚ) (n : ℕ) :
    mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n
      ↔ mersenneWeight (n + 1) ≤ greedyMersenneRemainder (x : ℝ) n := by
  constructor
  · intro h
    have hc : ((mersenneWeightRat (n + 1) : ℚ) : ℝ)
        ≤ ((greedyMersenneRemainderRat x n : ℚ) : ℝ) := by
      exact_mod_cast h
    simpa using hc
  · intro h
    rw [← cast_greedyMersenneRemainderRat x n] at h
    have hc : ((mersenneWeightRat (n + 1) : ℚ) : ℝ)
        ≤ ((greedyMersenneRemainderRat x n : ℚ) : ℝ) := by
      simpa using h
    exact_mod_cast hc

/-- A rational value already known to have normalized support has computable
support bits, recovered by the exact rational greedy recurrence.  This does
not assert decidability of achievement-set membership. -/
theorem rational_member_support_bit_iff
    (x : ℚ) (A : Set ℕ) (hA0 : 0 ∉ A)
    (hvalue : ((x : ℚ) : ℝ) = positiveMersenneSupportValue A) (n : ℕ) :
    n + 1 ∈ A ↔
      mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n := by
  rw [rational_greedy_take_iff_real]
  rw [hvalue]
  have hset := greedySupport_supportValue_eq A hA0
  have hmem : n + 1 ∈ A ↔
      n + 1 ∈ greedyMersenneSupport (positiveMersenneSupportValue A) := by
    rw [hset]
  exact hmem.trans (succ_mem_greedyMersenneSupport_iff _ n)

/-! ## Exact regression fixtures -/

/-- An exact worked prefix identity.  Selecting exponents
`{2,3,6,7,14}` from the target `1/2` leaves the rational residual
`1/688086`. -/
theorem half_sub_five_term_prefix_eq :
    (1 / 2 : ℚ)
      - finiteErdosSum ({2, 3, 6, 7, 14} : Finset ℕ) 2
      = 1 / 688086 := by
  norm_num [finiteErdosSum]

end Erdos249257
