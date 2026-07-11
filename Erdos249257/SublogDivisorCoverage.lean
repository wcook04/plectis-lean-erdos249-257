import Erdos249257.RationalSupportCarrySkeleton
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Zero-window growth for rational Erdős support series

This file proves a sublogarithmic divisor-coverage theorem for a hypothetical
rational Erdős support-series value. If the support coefficient vanishes
for `h` consecutive indices after `N`, the shifted odd-denominator tail state
from `RationalSupportCarrySkeleton` doubles exactly `h` times.  Positivity of
that state therefore forces

`2^h ≤ v * binaryCoeffTail (supportCoeff A) (c + N + h)`.

The unconditional half is now closed in the same module.  A fixed-natural-
power factorisation argument proves

`τ(n)^k ≤ (k^(2^k))^k * n`.

Taking one real `k`-th root and summing an exact weighted geometric majorant
gives a `1/k` support-tail envelope.  Raising the carry inequality to the
`k`-th power consumes one binary factor from the self-reference through `h`,
which yields the final coefficient `1/(k-1)`.  The theorem
`supportCoeffZeroWindow_length_le_eps_logb` proves an
`ε * log₂ N + O(1)` zero-window bound for every positive `N`.

This theorem does not prove or refute universal Erdős #257, and Erdős #249
also remains open.
-/

namespace Erdos249257

open Set

/-! ## An explicit fixed-power divisor bound -/

/-- The elementary exponential bound used for every prime exponent. -/
theorem nat_add_one_le_two_pow (a : ℕ) :
    a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      calc
        a + 2 ≤ 2 * (a + 1) := by omega
        _ ≤ 2 * 2 ^ a := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (a + 1) := by simp [pow_succ, Nat.mul_comm]

/-- A single explicit penalty `k^k` controls every exponent at every prime
at least two. -/
theorem nat_add_one_pow_le_self_pow_mul_two_pow
    (k a : ℕ) (hk : 1 ≤ k) :
    (a + 1) ^ k ≤ k ^ k * 2 ^ a := by
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  let q := a / k
  have hmod : a % k < k := Nat.mod_lt a hk0
  have hdecomp : a = q * k + a % k := by
    simpa [q] using (Nat.div_add_mod' a k).symm
  have haq : a + 1 ≤ k * (q + 1) := by
    calc
      a + 1 = q * k + (a % k + 1) := by omega
      _ ≤ q * k + k :=
        Nat.add_le_add_left (Nat.succ_le_iff.mpr hmod) (q * k)
      _ = k * (q + 1) := by ring
  have hq : q + 1 ≤ 2 ^ q := nat_add_one_le_two_pow q
  have hbase : a + 1 ≤ k * 2 ^ q :=
    haq.trans (Nat.mul_le_mul_left k hq)
  calc
    (a + 1) ^ k ≤ (k * 2 ^ q) ^ k := Nat.pow_le_pow_left hbase k
    _ = k ^ k * 2 ^ (q * k) := by rw [mul_pow, ← pow_mul]
    _ ≤ k ^ k * 2 ^ a := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right (by omega) (Nat.div_mul_le_self a k)

/-- Pointwise prime-factor estimate: only primes below `2^k` pay the
explicit `k^k` penalty. -/
theorem factorization_add_one_pow_le_penalty_mul
    (n p k : ℕ) (hk : 1 ≤ k)
    (hp : p ∈ n.primeFactors) :
    (n.factorization p + 1) ^ k ≤
      (if p < 2 ^ k then k ^ k else 1) *
        p ^ n.factorization p := by
  let a := n.factorization p
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : 2 ≤ p := hpprime.two_le
  by_cases hsmall : p < 2 ^ k
  · simp only [if_pos hsmall]
    calc
      (a + 1) ^ k ≤ k ^ k * 2 ^ a :=
        nat_add_one_pow_le_self_pow_mul_two_pow k a hk
      _ ≤ k ^ k * p ^ a :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp2 a)
  · have hlarge : 2 ^ k ≤ p := Nat.le_of_not_gt hsmall
    simp only [if_neg hsmall, one_mul]
    calc
      (a + 1) ^ k ≤ (2 ^ a) ^ k :=
        Nat.pow_le_pow_left (nat_add_one_le_two_pow a) k
      _ = (2 ^ k) ^ a := by simp only [← pow_mul, Nat.mul_comm k a]
      _ ≤ p ^ a := Nat.pow_le_pow_left hlarge a

/-- There are at most `2^k` prime factors below the cutoff `2^k`. -/
theorem card_small_primeFactors_le_two_pow (n k : ℕ) :
    (n.primeFactors.filter fun p => p < 2 ^ k).card ≤ 2 ^ k := by
  calc
    (n.primeFactors.filter fun p => p < 2 ^ k).card
        ≤ (Finset.range (2 ^ k)).card := by
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_range.mpr hp.2
    _ = 2 ^ k := Finset.card_range _

/-- Completely explicit constant for the fixed-`k` divisor bound. -/
def divisorSubpowerConst (k : ℕ) : ℕ := k ^ (2 ^ k)

/-- Fixed-natural-power divisor theorem.  All prime-factor bookkeeping is in
`ℕ`; the only loss is the explicit penalty from primes below `2^k`. -/
theorem card_divisors_pow_le_divisorSubpowerConst_pow_mul
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    n.divisors.card ^ k ≤ divisorSubpowerConst k ^ k * n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [Nat.card_divisors hn0, ← Finset.prod_pow]
  calc
    n.primeFactors.prod (fun p => (n.factorization p + 1) ^ k)
        ≤ n.primeFactors.prod (fun p =>
          (if p < 2 ^ k then k ^ k else 1) *
            p ^ n.factorization p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        exact factorization_add_one_pow_le_penalty_mul n p k hk hp
    _ =
        n.primeFactors.prod (fun p => if p < 2 ^ k then k ^ k else 1) *
          n.primeFactors.prod (fun p => p ^ n.factorization p) := by
      rw [Finset.prod_mul_distrib]
    _ =
        (k ^ k) ^ (n.primeFactors.filter fun p => p < 2 ^ k).card * n := by
      congr 1
      · rw [← Finset.prod_filter]
        simp
      · simpa [← Nat.support_factorization] using
          (Nat.prod_factorization_pow_eq_self hn0)
    _ ≤ (k ^ k) ^ (2 ^ k) * n := by
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (by positivity)
        (card_small_primeFactors_le_two_pow n k)
    _ = divisorSubpowerConst k ^ k * n := by
      simp only [divisorSubpowerConst, ← pow_mul, Nat.mul_comm k (2 ^ k)]

/-- Take the real `k`-th root once, after the finite prime-factor product has
been closed in `ℕ`.  This version includes `n = 0`. -/
theorem card_divisors_le_divisorSubpowerConst_mul_rpow
    (n k : ℕ) (hk : 1 ≤ k) :
    (n.divisors.card : ℝ) ≤
      (divisorSubpowerConst k : ℝ) *
        (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  by_cases hn0 : n = 0
  · subst n
    simp [Nat.divisors]
    positivity
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnat :=
      card_divisors_pow_le_divisorSubpowerConst_pow_mul n k hn hk
    have hreal :
        (n.divisors.card : ℝ) ^ k ≤
          (divisorSubpowerConst k : ℝ) ^ k * (n : ℝ) := by
      exact_mod_cast hnat
    have hk0 : k ≠ 0 := by omega
    have hroot := Real.rpow_le_rpow (by positivity) hreal (by positivity :
      0 ≤ ((k : ℝ)⁻¹))
    calc
      (n.divisors.card : ℝ) =
          ((n.divisors.card : ℝ) ^ k) ^ ((k : ℝ)⁻¹) := by
        symm
        exact Real.pow_rpow_inv_natCast (by positivity) hk0
      _ ≤
          (((divisorSubpowerConst k : ℝ) ^ k) * (n : ℝ)) ^
            ((k : ℝ)⁻¹) := hroot
      _ =
          (divisorSubpowerConst k : ℝ) *
            (n : ℝ) ^ ((k : ℝ)⁻¹) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        rw [Real.pow_rpow_inv_natCast (by positivity) hk0]

/-- The support coefficient inherits the fixed-power divisor theorem. -/
theorem supportCoeff_pow_le_divisorSubpowerConst_pow_mul
    (A : Set ℕ) (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    supportCoeff A n ^ k ≤ divisorSubpowerConst k ^ k * n := by
  calc
    supportCoeff A n ^ k ≤ n.divisors.card ^ k :=
      Nat.pow_le_pow_left (supportCoeff_le_card_divisors A n) k
    _ ≤ divisorSubpowerConst k ^ k * n :=
      card_divisors_pow_le_divisorSubpowerConst_pow_mul n k hn hk

/-- Real subpower form inherited by `supportCoeff`. -/
theorem supportCoeff_le_divisorSubpowerConst_mul_rpow
    (A : Set ℕ) (n k : ℕ) (hk : 1 ≤ k) :
    (supportCoeff A n : ℝ) ≤
      (divisorSubpowerConst k : ℝ) *
        (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  calc
    (supportCoeff A n : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast supportCoeff_le_card_divisors A n
    _ ≤
        (divisorSubpowerConst k : ℝ) *
          (n : ℝ) ^ ((k : ℝ)⁻¹) :=
      card_divisors_le_divisorSubpowerConst_mul_rpow n k hk

/-- `supportCoeff A` vanishes on the `h` positive indices immediately after
`N`, namely `N + 1, ..., N + h`. -/
def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  ∀ j : ℕ, j < h → supportCoeff A (N + j + 1) = 0

/-- A shifted natural tail state doubles exactly across a support-coefficient
zero window. This is the recurrence-only core; it uses no analytic
growth estimate. -/
theorem shiftedTailState_eq_pow_mul_of_supportCoeffZeroWindow
    (A : Set ℕ) (c v N h : ℕ) (u : ℕ → ℕ)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    u (N + h) = 2 ^ h * u N := by
  have hiter : ∀ m : ℕ, m ≤ h → u (N + m) = 2 ^ m * u N := by
    intro m
    induction m with
    | zero =>
        intro _
        simp
    | succ m ih =>
        intro hm
        have hm_lt : m < h := Nat.lt_of_succ_le hm
        have hz0 : supportCoeff A ((c + N) + m + 1) = 0 :=
          hzero m hm_lt
        have hz : supportCoeff A (c + (N + m) + 1) = 0 := by
          simpa [Nat.add_assoc] using hz0
        have hstep : u ((N + m) + 1) = 2 * u (N + m) := by
          have := hrec (N + m)
          simpa [hz] using this
        calc
          u (N + (m + 1)) = u ((N + m) + 1) := by
            simp [Nat.add_assoc]
          _ = 2 * u (N + m) := hstep
          _ = 2 * (2 ^ m * u N) := by rw [ih (Nat.le_of_lt hm_lt)]
          _ = 2 ^ (m + 1) * u N := by rw [pow_succ]; ring
  exact hiter h le_rfl

/-- Positivity upgrades exact doubling to the natural-number lower bound
`2^h ≤ u(N+h)`. -/
theorem pow_le_shiftedTailState_of_supportCoeffZeroWindow
    (A : Set ℕ) (c v N h : ℕ) (u : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    2 ^ h ≤ u (N + h) := by
  rw [shiftedTailState_eq_pow_mul_of_supportCoeffZeroWindow
    A c v N h u hrec hzero]
  exact Nat.le_mul_of_pos_right (2 ^ h) (hpos N)

/-- Fraction-facing algebraic boundary. For a displayed denominator
`2^c * v`, every zero window forces the odd tail state, hence the scaled true
tail, to be at least `2^h`. -/
theorem pow_le_mul_binaryCoeffTail_of_support_fraction_zeroWindow
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    (2 : ℝ) ^ h ≤
      (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + N + h) := by
  obtain ⟨u, htail, hpos, hrec, _⟩ :=
    exists_shifted_odd_tail_nat_states_of_support_fraction
      A hA p c v hv hvalue
  have hpowNat : 2 ^ h ≤ u (N + h) :=
    pow_le_shiftedTailState_of_supportCoeffZeroWindow
      A c v N h u hpos hrec hzero
  have hpowReal : (2 : ℝ) ^ h ≤ (u (N + h) : ℝ) := by
    exact_mod_cast hpowNat
  calc
    (2 : ℝ) ^ h ≤ (u (N + h) : ℝ) := hpowReal
    _ = (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + (N + h)) :=
      htail (N + h)
    _ = (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + N + h) := by
      simp [Nat.add_assoc]

/-- An explicit upper envelope for the scaled support-coefficient tail. -/
def SupportCoeffTailEnvelope (A : Set ℕ) (envelope : ℕ → ℝ) : Prop :=
  ∀ M : ℕ, binaryCoeffTail (supportCoeff A) M ≤ envelope M

/-! ## A generic subpower-to-binary-tail transport -/

/-- The weighted geometric majorant used by every subpower tail envelope is
summable. -/
theorem summable_succ_div_two_pow :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  have h :=
    (summable_const_add_mul_geometric 1
      (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)).mul_left (1 / 2 : ℝ)
  refine h.congr fun j => ?_
  push_cast
  rw [pow_succ, div_pow, one_pow]
  ring

/-- Exact value of the weighted geometric majorant. -/
theorem tsum_succ_div_two_pow :
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) = 2 := by
  have hgeom : Summable (fun j : ℕ => ((1 : ℝ) / 2) ^ j) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hlin : Summable (fun j : ℕ => (j : ℝ) * ((1 : ℝ) / 2) ^ j) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one 1
        (by norm_num : ‖(1 : ℝ) / 2‖ < 1))
  calc
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1))
        = (1 / 2 : ℝ) *
            ((∑' j : ℕ, (j : ℝ) * ((1 : ℝ) / 2) ^ j) +
              ∑' j : ℕ, ((1 : ℝ) / 2) ^ j) := by
          rw [← hlin.tsum_add hgeom, ← tsum_mul_left]
          apply tsum_congr
          intro j
          push_cast
          rw [pow_succ, div_pow, one_pow]
          ring
    _ = 2 := by
      rw [tsum_coe_mul_geometric_of_norm_lt_one
          (by norm_num : ‖(1 : ℝ) / 2‖ < 1),
        tsum_geometric_of_norm_lt_one
          (by norm_num : ‖(1 : ℝ) / 2‖ < 1)]
      norm_num

/-- A coefficient bound `f(n) ≤ C n^δ`, with `0 ≤ δ ≤ 1`, gives the
explicit binary-tail bound `2 C (M+1)^δ`.  The proof also derives `C ≥ 0`
from the bound at `n = 1`, so callers do not need a redundant sign hypothesis. -/
theorem binaryCoeffTail_le_two_mul_rpow
    (f : ℕ → ℕ) (C δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hf : ∀ n : ℕ, (f n : ℝ) ≤ C * (n : ℝ) ^ δ)
    (M : ℕ) :
    binaryCoeffTail f M ≤
      2 * C * (((M + 1 : ℕ) : ℝ) ^ δ) := by
  have hC : 0 ≤ C := by
    have h := hf 1
    have h0 : (0 : ℝ) ≤ (f 1 : ℝ) := Nat.cast_nonneg _
    have := h0.trans h
    simpa using this
  let K : ℝ := C * (((M + 1 : ℕ) : ℝ) ^ δ)
  have hK : 0 ≤ K := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have hmaj : Summable
      (fun j : ℕ => K * (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1))) :=
    summable_succ_div_two_pow.mul_left K
  have hterm : ∀ j : ℕ,
      (f (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) ≤
        K * (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
    intro j
    have hindexNat : M + j + 1 ≤ (M + 1) * (j + 1) := by
      nlinarith
    have hindex : ((M + j + 1 : ℕ) : ℝ) ≤
        ((M + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast hindexNat
    have hbase : ((M + j + 1 : ℕ) : ℝ) ^ δ ≤
        ((((M + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ δ) :=
      Real.rpow_le_rpow (by positivity) hindex hδ0
    have hjpow : (((j + 1 : ℕ) : ℝ) ^ δ) ≤ ((j + 1 : ℕ) : ℝ) :=
      Real.rpow_le_self_of_one_le (by norm_num) hδ1
    have hcoeff : (f (M + j + 1) : ℝ) ≤
        K * ((j + 1 : ℕ) : ℝ) := by
      calc
        (f (M + j + 1) : ℝ)
            ≤ C * (((M + j + 1 : ℕ) : ℝ) ^ δ) := hf _
        _ ≤ C *
            ((((M + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ δ) := by
              gcongr
        _ = K * (((j + 1 : ℕ) : ℝ) ^ δ) := by
              dsimp [K]
              rw [Real.mul_rpow (by positivity) (by positivity)]
              ring
        _ ≤ K * ((j + 1 : ℕ) : ℝ) := by gcongr
    calc
      (f (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
          ≤ (K * ((j + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ (j + 1) := by
            gcongr
      _ = K * (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) := by ring
  have hsource : Summable
      (fun j : ℕ => (f (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm hmaj
  unfold binaryCoeffTail
  calc
    (∑' j : ℕ, (f (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1))
        ≤ ∑' j : ℕ, K *
            (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) :=
          Summable.tsum_le_tsum hterm hsource hmaj
    _ = K * 2 := by rw [tsum_mul_left, tsum_succ_div_two_pow]
    _ = 2 * C * (((M + 1 : ℕ) : ℝ) ^ δ) := by
      dsimp [K]
      ring

/-- Package a pointwise divisor-card bound into the exact tail-envelope
interface consumed by the rational carry theorem below. -/
theorem supportCoeffTailEnvelope_two_mul_rpow_of_card_divisors_bound
    (A : Set ℕ) (C δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdiv : ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ) :
    SupportCoeffTailEnvelope A
      (fun M : ℕ => 2 * C * (((M + 1 : ℕ) : ℝ) ^ δ)) := by
  intro M
  apply binaryCoeffTail_le_two_mul_rpow (supportCoeff A) C δ hδ0 hδ1
  intro n
  have hcoeff : (supportCoeff A n : ℝ) ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast supportCoeff_le_card_divisors A n
  exact hcoeff.trans (hdiv n)

/-- Unconditional support-tail envelope with exponent exactly `1/k`. -/
theorem supportCoeffTailEnvelope_divisorSubpower
    (A : Set ℕ) (k : ℕ) (hk : 1 ≤ k) :
    SupportCoeffTailEnvelope A
      (fun M : ℕ =>
        2 * (divisorSubpowerConst k : ℝ) *
          (((M + 1 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) := by
  apply supportCoeffTailEnvelope_two_mul_rpow_of_card_divisors_bound
  · positivity
  · apply (inv_le_one₀ (by positivity : (0 : ℝ) < k)).2
    exact_mod_cast hk
  · intro n
    exact card_divisors_le_divisorSubpowerConst_mul_rpow n k hk

/-- Once a subpower tail envelope
is supplied, a zero window is bounded by that envelope at its right endpoint.
No divisor-growth implementation detail leaks into the rational-support
argument. -/
theorem pow_le_mul_tailEnvelope_of_support_fraction_zeroWindow
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h)
    (envelope : ℕ → ℝ) (henvelope : SupportCoeffTailEnvelope A envelope) :
    (2 : ℝ) ^ h ≤ (v : ℝ) * envelope (c + N + h) := by
  calc
    (2 : ℝ) ^ h ≤
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + N + h) :=
      pow_le_mul_binaryCoeffTail_of_support_fraction_zeroWindow
        A hA p c v N h hv hvalue hzero
    _ ≤ (v : ℝ) * envelope (c + N + h) :=
      mul_le_mul_of_nonneg_left (henvelope (c + N + h)) (Nat.cast_nonneg v)

/-- Direct consumer bridge from any pointwise divisor subpower bound to a
zero-window power inequality. -/
theorem pow_le_mul_two_mul_rpow_of_card_divisors_bound_zeroWindow
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h)
    (C δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdiv : ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ) :
    (2 : ℝ) ^ h ≤
      (v : ℝ) * (2 * C * ((((c + N + h) + 1 : ℕ) : ℝ) ^ δ)) := by
  exact pow_le_mul_tailEnvelope_of_support_fraction_zeroWindow
    A hA p c v N h hv hvalue hzero
    (fun M : ℕ => 2 * C * (((M + 1 : ℕ) : ℝ) ^ δ))
    (supportCoeffTailEnvelope_two_mul_rpow_of_card_divisors_bound
      A C δ hδ0 hδ1 hdiv)

/-- The unconditional divisor-subpower envelope composed with the verified
rational carry mechanism. -/
theorem pow_le_divisorSubpower_of_support_fraction_zeroWindow
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h k : ℕ) (hv : 0 < v) (hk : 1 ≤ k)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    (2 : ℝ) ^ h ≤
      (2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)) *
        (((c + N + 1 + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) := by
  have hraw := pow_le_mul_tailEnvelope_of_support_fraction_zeroWindow
    A hA p c v N h hv hvalue hzero
    (fun M : ℕ =>
      2 * (divisorSubpowerConst k : ℝ) *
        (((M + 1 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)))
    (supportCoeffTailEnvelope_divisorSubpower A k hk)
  calc
    (2 : ℝ) ^ h ≤
        (v : ℝ) *
          (2 * (divisorSubpowerConst k : ℝ) *
            (((c + N + h + 1 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) := hraw
    _ = (2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)) *
        (((c + N + 1 + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) := by
      rw [show c + N + h + 1 = c + N + 1 + h by omega]
      ring

/-! ## Absorbing the zero-window length -/

/-- Raising the self-referential inequality to the `k`-th power and using
`Y+h ≤ Y*2^h` consumes exactly one of the `k` binary factors. -/
theorem pow_sub_one_mul_le_of_pow_le_mul_add_invNat_rpow
    (k Y h : ℕ) (hk : 2 ≤ k) (hY : 1 ≤ Y)
    (L : ℝ) (hL : 1 ≤ L)
    (hpow :
      (2 : ℝ) ^ h ≤
        L * (((Y + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) :
    (2 : ℝ) ^ ((k - 1) * h) ≤ L ^ k * (Y : ℝ) := by
  have hk0 : k ≠ 0 := by omega
  have hraised :
      (2 : ℝ) ^ (h * k) ≤ L ^ k * ((Y + h : ℕ) : ℝ) := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ h) hpow k
    calc
      (2 : ℝ) ^ (h * k) = ((2 : ℝ) ^ h) ^ k := by rw [pow_mul]
      _ ≤ (L * (((Y + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) ^ k := hp
      _ = L ^ k * ((Y + h : ℕ) : ℝ) := by
        rw [mul_pow, Real.rpow_inv_natCast_pow (by positivity) hk0]
  have hYh : Y + h ≤ Y * (h + 1) := by
    have hh : h ≤ Y * h := by
      have ht := Nat.mul_le_mul_right h hY
      simpa [Nat.mul_comm] using ht
    calc
      Y + h ≤ Y + Y * h := Nat.add_le_add_left hh Y
      _ = Y * (h + 1) := by simp [Nat.mul_add, Nat.add_comm]
  have hhpow : h + 1 ≤ 2 ^ h := nat_add_one_le_two_pow h
  have hX : Y + h ≤ Y * 2 ^ h :=
    hYh.trans (Nat.mul_le_mul_left Y hhpow)
  have hXreal : ((Y + h : ℕ) : ℝ) ≤ (Y : ℝ) * (2 : ℝ) ^ h := by
    exact_mod_cast hX
  have hwith :
      (2 : ℝ) ^ (h * k) ≤
        L ^ k * (Y : ℝ) * (2 : ℝ) ^ h := by
    calc
      (2 : ℝ) ^ (h * k) ≤ L ^ k * ((Y + h : ℕ) : ℝ) := hraised
      _ ≤ L ^ k * ((Y : ℝ) * (2 : ℝ) ^ h) := by
        gcongr
      _ = L ^ k * (Y : ℝ) * (2 : ℝ) ^ h := by ring
  have hexp : h * k = (k - 1) * h + h := by
    have hsplit : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    calc
      h * k = h * ((k - 1) + 1) := by rw [hsplit]
      _ = (k - 1) * h + h := by ring
  have hmul :
      (2 : ℝ) ^ ((k - 1) * h) * (2 : ℝ) ^ h ≤
        (L ^ k * (Y : ℝ)) * (2 : ℝ) ^ h := by
    simpa [hexp, pow_add, mul_assoc] using hwith
  exact le_of_mul_le_mul_right hmul (by positivity)

/-- Logarithmic form of the absorption theorem.  The final coefficient is
`1/(k-1)`, although the divisor and tail exponent is `1/k`. -/
theorem length_le_logb_of_pow_le_mul_add_invNat_rpow
    (k Y h : ℕ) (hk : 2 ≤ k) (hY : 1 ≤ Y)
    (L : ℝ) (hL : 1 ≤ L)
    (hpow :
      (2 : ℝ) ^ h ≤
        L * (((Y + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) :
    (h : ℝ) ≤
      (Real.logb 2 (Y : ℝ) + Real.logb 2 (L ^ k)) /
        ((k - 1 : ℕ) : ℝ) := by
  have hcancel :
      (2 : ℝ) ^ ((k - 1) * h) ≤ L ^ k * (Y : ℝ) :=
    pow_sub_one_mul_le_of_pow_le_mul_add_invNat_rpow
      k Y h hk hY L hL hpow
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hprodpos : 0 < L ^ k * (Y : ℝ) :=
    mul_pos (pow_pos hLpos k) hYpos
  have hlog :
      (((k - 1) * h : ℕ) : ℝ) ≤
        Real.logb 2 (L ^ k * (Y : ℝ)) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hprodpos]
    rw [Real.rpow_natCast]
    exact hcancel
  rw [Real.logb_mul (pow_ne_zero k hLpos.ne') hYpos.ne'] at hlog
  have hkden : 0 < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  rw [le_div_iff₀ hkden]
  norm_num [Nat.cast_mul] at hlog ⊢
  linarith

/-- Archimedean selector in exactly the exponent produced by absorption. -/
theorem exists_nat_two_le_inv_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 2 ≤ k ∧ (((k - 1 : ℕ) : ℝ))⁻¹ ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hε
  refine ⟨n + 2, by omega, ?_⟩
  simpa [one_div] using hn.le

/-- Separate the fixed affine shift from the growing index inside `log₂`. -/
theorem logb_nat_affine_le_add (c N : ℕ) :
    Real.logb 2 (c + N + 1 : ℝ) ≤
      Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ) := by
  have hle : (c + N + 1 : ℝ) ≤ (c + 1 : ℝ) * (N + 1 : ℝ) := by
    nlinarith [Nat.zero_le c, Nat.zero_le N]
  calc
    Real.logb 2 (c + N + 1 : ℝ) ≤
        Real.logb 2 ((c + 1 : ℝ) * (N + 1 : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hle
    _ = Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ) := by
      rw [Real.logb_mul (by positivity) (by positivity)]

/-- Convert a parameterized `1/(k-1)` affine-log estimate to an
`ε * log₂(N+1)` estimate while keeping the remaining term explicit. -/
theorem le_epsilon_mul_logb_add_constant_div_of_affine_log_bound
    {ε D x : ℝ} {c N k : ℕ}
    (hbound : x ≤
      (Real.logb 2 (c + N + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ))
    (hinv : (((k - 1 : ℕ) : ℝ))⁻¹ ≤ ε) :
    x ≤ ε * Real.logb 2 (N + 1 : ℝ) +
      (Real.logb 2 (c + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ) := by
  have hnum :
      Real.logb 2 (c + N + 1 : ℝ) + D ≤
        (Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ)) + D :=
    add_le_add (logb_nat_affine_le_add c N) le_rfl
  have hdiv :
      (Real.logb 2 (c + N + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ) ≤
        ((Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ)) + D) /
          ((k - 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have hlog : 0 ≤ Real.logb 2 (N + 1 : ℝ) :=
    Real.logb_nonneg (by norm_num) (by norm_num)
  have hscale :
      Real.logb 2 (N + 1 : ℝ) / ((k - 1 : ℕ) : ℝ) ≤
        ε * Real.logb 2 (N + 1 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hinv hlog
  calc
    x ≤ (Real.logb 2 (c + N + 1 : ℝ) + D) /
        ((k - 1 : ℕ) : ℝ) := hbound
    _ ≤ ((Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ)) + D) /
        ((k - 1 : ℕ) : ℝ) := hdiv
    _ = Real.logb 2 (N + 1 : ℝ) / ((k - 1 : ℕ) : ℝ) +
        (Real.logb 2 (c + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ) := by ring
    _ ≤ ε * Real.logb 2 (N + 1 : ℝ) +
        (Real.logb 2 (c + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ) :=
      add_le_add hscale le_rfl

/-! ## Sublogarithmic zero-window bounds -/

/-- Parameterized fixed-`k` theorem. This is the load-bearing form from
which the every-`ε` statement follows. -/
theorem supportCoeffZeroWindow_length_le_logb_divisorSubpower
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v N h k : ℕ) (hv : 0 < v) (hk : 2 ≤ k)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hzero : SupportCoeffZeroWindow A (c + N) h) :
    (h : ℝ) ≤
      (Real.logb 2 (c + N + 1 : ℝ) +
        Real.logb 2
          ((2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)) ^ k)) /
        ((k - 1 : ℕ) : ℝ) := by
  let L : ℝ := 2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)
  have hk1 : 1 ≤ k := le_trans (by omega) hk
  have hpow :
      (2 : ℝ) ^ h ≤
        L * (((c + N + 1 + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) := by
    exact pow_le_divisorSubpower_of_support_fraction_zeroWindow
      A hA p c v N h k hv hk1 hvalue hzero
  have hL : 1 ≤ L := by
    dsimp [L]
    have hkpos : 0 < k := by omega
    have hpos : 0 < 2 * v * divisorSubpowerConst k := by
      dsimp [divisorSubpowerConst]
      positivity
    have hnat : 1 ≤ 2 * v * divisorSubpowerConst k := by omega
    exact_mod_cast hnat
  simpa [L] using
    length_le_logb_of_pow_le_mul_add_invNat_rpow
      k (c + N + 1) h hk (by omega) L hL hpow

/-- For every positive `ε`, a rational support-series
value forces every support-coefficient zero window to have length at most
`ε * log₂(N+1)` plus a constant depending only on `ε`, `v`, and `c`.

The bound is uniform in the support `A`, numerator `p`, starting index `N`,
and window length `h`. -/
theorem supportCoeffZeroWindow_length_le_eps_logb_add
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ,
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N + 1 : ℝ) + B := by
  obtain ⟨k, hk, hinv⟩ := exists_nat_two_le_inv_sub_one_le hε
  let L : ℝ := 2 * (v : ℝ) * (divisorSubpowerConst k : ℝ)
  let D : ℝ := Real.logb 2 (L ^ k)
  let B : ℝ :=
    (Real.logb 2 (c + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ)
  have hL : 1 ≤ L := by
    dsimp [L]
    have hkpos : 0 < k := by omega
    have hpos : 0 < 2 * v * divisorSubpowerConst k := by
      dsimp [divisorSubpowerConst]
      positivity
    have hnat : 1 ≤ 2 * v * divisorSubpowerConst k := by omega
    exact_mod_cast hnat
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Real.logb_nonneg (by norm_num) (one_le_pow₀ hL)
  have hB : 0 ≤ B := by
    dsimp [B]
    apply div_nonneg
    · exact add_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) hD
    · positivity
  refine ⟨B, hB, ?_⟩
  intro N h hzero
  have hkbound := supportCoeffZeroWindow_length_le_logb_divisorSubpower
    A hA p c v N h k hv hk hvalue hzero
  have hfinal :=
    le_epsilon_mul_logb_add_constant_div_of_affine_log_bound
      (ε := ε) (D := D) (x := (h : ℝ))
      (c := c) (N := N) (k := k) hkbound hinv
  simpa [B, D, L] using hfinal

/-- For positive `N`, replace the total `log₂(N+1)` form by the customary
paper-facing `log₂ N` form at the cost of one additive `ε`. -/
theorem logb_nat_succ_le_one_add (N : ℕ) (hN : 1 ≤ N) :
    Real.logb 2 (N + 1 : ℝ) ≤ 1 + Real.logb 2 (N : ℝ) := by
  have hle : (N + 1 : ℝ) ≤ (2 : ℝ) * (N : ℝ) := by
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  calc
    Real.logb 2 (N + 1 : ℝ) ≤ Real.logb 2 ((2 : ℝ) * (N : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hle
    _ = Real.logb 2 (2 : ℝ) + Real.logb 2 (N : ℝ) := by
      rw [Real.logb_mul (by norm_num) (by positivity)]
    _ = 1 + Real.logb 2 (N : ℝ) := by
      rw [Real.logb_self_eq_one (by norm_num)]

/-- Exact `ε * log₂ N + O(1)` form for every positive
starting index. -/
theorem supportCoeffZeroWindow_length_le_eps_logb
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ, 1 ≤ N →
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N : ℝ) + B := by
  obtain ⟨B, hB, hbound⟩ :=
    supportCoeffZeroWindow_length_le_eps_logb_add
      A hA p c v hv hvalue ε hε
  refine ⟨B + ε, add_nonneg hB hε.le, ?_⟩
  intro N h hN hzero
  calc
    (h : ℝ) ≤ ε * Real.logb 2 (N + 1 : ℝ) + B := hbound N h hzero
    _ ≤ ε * (1 + Real.logb 2 (N : ℝ)) + B := by
      gcongr
      exact logb_nat_succ_le_one_add N hN
    _ = ε * Real.logb 2 (N : ℝ) + (B + ε) := by ring

#print axioms shiftedTailState_eq_pow_mul_of_supportCoeffZeroWindow
#print axioms pow_le_shiftedTailState_of_supportCoeffZeroWindow
#print axioms pow_le_mul_binaryCoeffTail_of_support_fraction_zeroWindow
#print axioms pow_le_mul_tailEnvelope_of_support_fraction_zeroWindow
#print axioms card_divisors_pow_le_divisorSubpowerConst_pow_mul
#print axioms card_divisors_le_divisorSubpowerConst_mul_rpow
#print axioms binaryCoeffTail_le_two_mul_rpow
#print axioms supportCoeffTailEnvelope_divisorSubpower
#print axioms length_le_logb_of_pow_le_mul_add_invNat_rpow
#print axioms supportCoeffZeroWindow_length_le_logb_divisorSubpower
#print axioms supportCoeffZeroWindow_length_le_eps_logb_add
#print axioms supportCoeffZeroWindow_length_le_eps_logb

end Erdos249257
