import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The two-thirds band for singleton skips of a greedy Mersenne expansion

Write a residual as `rem = 1/R`.  A skip at rank `k` of the greedy Mersenne
expansion is *dyadically safe* when `rem ≤ 2^{-k}`, equivalently `R ≥ 2^k`.
Across a run of consecutive skips `R` does not move, so only the last skip
before a take can fail to be safe, and a take immediately followed by a take
has no skip to check.  The remaining configuration is the *singleton*: a take
at `b`, one skip at `b+1`, then a take at `b+2`.

This module gives that configuration an exact normal form.  Writing
`q = 2^b - 1`, the singleton skip is unsafe precisely when the pre-take
reciprocal `R` lies in the open interval

  `( q(2q+1)/(3q+1) , 2q(q+1)/(3q+2) )`,

whose width is exactly `q²/((3q+1)(3q+2))`, hence below `1/9`, and which is
contained in `(2q/3, 2q/3 + 2/9)`.  The obstruction is therefore confined to a
window of bounded width pinned at two thirds of the Mersenne modulus, and an
unsafe skip forces `2q < 3R < 2q + 2/3`.

Two unconditional consequences follow:

* `not_twoThirdsBand_of_int` — an integral reciprocal is never unsafe, since
  the pinning leaves no room for an integer multiple of three.
* `seven_le_of_intBand_odd` — for a residual `rem = p/(2D)` in lowest terms
  with `p`, `D` and `q` odd, an unsafe singleton forces `p ≥ 7`.  The argument
  is `2`-adic: oddness makes the band defect `Δ = 6D - 2pq` divisible by four,
  and that congruence alone removes the classes `p ∈ {1, 3, 5}`.

Both are statements about a single take-skip-take step in isolation.  This
module does not assert that the greedy expansion of any particular target
avoids the band, and it does not prove the half-membership statement of
Erdős #257; the reachability of band states by an actual greedy orbit is not
addressed here.  The `p ≥ 7` bound is sharp for the arithmetic hypotheses
stated: odd triples realising `p = 7` inside the band exist.
-/

namespace Erdos249257
namespace HalfGreedyTwoThirdsBand

/-! ## Rational geometry of the band -/

/-- Reciprocal of the residual after subtracting the rank-`b` Mersenne weight,
where `q = 2^b - 1`: from `rem' = 1/R - 1/q` one gets `R' = Rq/(q - R)`. -/
noncomputable def postTakeReciprocal (R q : ℚ) : ℚ := R * q / (q - R)

/-- The singleton skip at `b+1` is unsafe exactly when the post-take reciprocal
lands strictly inside `(2^{b+1} - 1, 2^{b+1}) = (2q+1, 2q+2)`. -/
def SingletonUnsafe (R q : ℚ) : Prop :=
  2 * q + 1 < postTakeReciprocal R q ∧ postTakeReciprocal R q < 2 * q + 2

/-- The two-thirds band, in the pre-take reciprocal. -/
def TwoThirdsBand (R q : ℚ) : Prop :=
  q * (2 * q + 1) / (3 * q + 1) < R ∧ R < 2 * q * (q + 1) / (3 * q + 2)

/-- **Band localisation.**  Under a take at `b` (`0 < R < q`), the singleton skip
is unsafe if and only if the pre-take reciprocal lies in the two-thirds band. -/
theorem singletonUnsafe_iff_twoThirdsBand {R q : ℚ} (hR : 0 < R) (hRq : R < q) :
    SingletonUnsafe R q ↔ TwoThirdsBand R q := by
  have hq : 0 < q := lt_trans hR hRq
  have hqR : 0 < q - R := by linarith
  have h1 : (0 : ℚ) < 3 * q + 1 := by linarith
  have h2 : (0 : ℚ) < 3 * q + 2 := by linarith
  unfold SingletonUnsafe TwoThirdsBand postTakeReciprocal
  rw [lt_div_iff₀ hqR, div_lt_iff₀ hqR, div_lt_iff₀ h1, lt_div_iff₀ h2]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨ha, hb⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-- The band begins strictly above `2q/3`. -/
theorem twoThirds_lt_bandLower {q : ℚ} (hq : 0 < q) :
    2 * q / 3 < q * (2 * q + 1) / (3 * q + 1) := by
  rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

/-- The band ends strictly below `2q/3 + 2/9`. -/
theorem bandUpper_lt_twoThirds_add {q : ℚ} (hq : 0 < q) :
    2 * q * (q + 1) / (3 * q + 2) < 2 * q / 3 + 2 / 9 := by
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **The band has width exactly `q²/((3q+1)(3q+2))`.** -/
theorem band_width {q : ℚ} (hq : 0 < q) :
    2 * q * (q + 1) / (3 * q + 2) - q * (2 * q + 1) / (3 * q + 1) =
      q ^ 2 / ((3 * q + 1) * (3 * q + 2)) := by
  have h1 : (3 * q + 1) ≠ 0 := by positivity
  have h2 : (3 * q + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The band width stays below `1/9`, uniformly in `q`. -/
theorem band_width_lt_ninth {q : ℚ} (hq : 0 < q) :
    q ^ 2 / ((3 * q + 1) * (3 * q + 2)) < 1 / 9 := by
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **Two-thirds pinning.**  An unsafe singleton forces `2q < 3R < 2q + 2/3`. -/
theorem three_mul_mem_of_twoThirdsBand {R q : ℚ} (hq : 0 < q)
    (h : TwoThirdsBand R q) :
    2 * q < 3 * R ∧ 3 * R < 2 * q + 2 / 3 := by
  obtain ⟨hlo, hhi⟩ := h
  have h1 : 2 * q / 3 < R := lt_trans (twoThirds_lt_bandLower hq) hlo
  have h2 : R < 2 * q / 3 + 2 / 9 := lt_trans hhi (bandUpper_lt_twoThirds_add hq)
  constructor <;> linarith

/-! ## An integral reciprocal is never unsafe

The pinning makes `2q` and `3R` integers separated by less than `2/3`, and no
integer lies in a gap of that length above another integer. -/

/-- **Integral reciprocals are safe.**  If `R` and `q` are integers, the singleton
skip cannot be unsafe.  This covers a unit residual `rem = 1/(2D)`, for which
`R = 2D`. -/
theorem not_twoThirdsBand_of_int {R q : ℚ} (hq : 0 < q)
    (m n : ℤ) (hRm : R = (m : ℚ)) (hqn : q = (n : ℚ)) :
    ¬ TwoThirdsBand R q := by
  intro h
  obtain ⟨hlo, hhi⟩ := three_mul_mem_of_twoThirdsBand hq h
  have e1 : ((2 * n : ℤ) : ℚ) < ((3 * m : ℤ) : ℚ) := by
    push_cast
    rw [hRm, hqn] at hlo
    linarith
  have i1 : (2 * n : ℤ) < 3 * m := by exact_mod_cast e1
  have i2 : (2 * n + 1 : ℤ) ≤ 3 * m := by omega
  have e2 : ((2 * n + 1 : ℤ) : ℚ) ≤ ((3 * m : ℤ) : ℚ) := by exact_mod_cast i2
  push_cast at e2
  rw [hRm, hqn] at hhi
  linarith

/-! ## The 2-adic bound `p ≥ 7`

A residual `rem = p/(2D)` in lowest terms whose denominator carries exactly one
factor of two has `p` and `D` both odd, and `q = 2^b - 1` is odd.  The band
defect

  `Δ = 6D - 2pq = 2(3D - pq)`

then has `3D - pq` even, so `4 ∣ Δ`.  An unsafe singleton needs `Δ > 0`, hence
`Δ ≥ 4`, and that one step forces `p ≥ 7`. -/

/-- Integer form of the band for `R = 2D/p`, cleared of denominators. -/
def IntBand (p D q : ℤ) : Prop :=
  q * (2 * q + 1) * p < 2 * D * (3 * q + 1) ∧ 2 * D * (3 * q + 2) < 2 * p * q * (q + 1)

/-- The band defect `Δ = 6D - 2pq` is divisible by four when `p`, `D`, `q` are odd. -/
theorem four_dvd_bandDefect {p D q : ℤ}
    (hp : Odd p) (hD : Odd D) (hq : Odd q) :
    (4 : ℤ) ∣ (6 * D - 2 * p * q) := by
  obtain ⟨a, ha⟩ := hD
  obtain ⟨b, hb⟩ := hp
  obtain ⟨c, hc⟩ := hq
  exact ⟨3 * a - 2 * b * c - b - c + 1, by rw [ha, hb, hc]; ring⟩

/-- **The 2-adic bound.**  For odd positive `p`, `D`, `q`, an unsafe singleton skip
forces `p ≥ 7`; equivalently, `p ∈ {1, 3, 5}` is always safe.

The bound is sharp for these hypotheses: odd triples with `p = 7` do lie in the
band.  Reachability by an actual greedy orbit is a separate question and is not
addressed here. -/
theorem seven_le_of_intBand_odd {p D q : ℤ}
    (hp : 0 < p) (hD : 0 < D) (hq : 0 < q)
    (hpodd : Odd p) (hDodd : Odd D) (hqodd : Odd q)
    (hband : IntBand p D q) :
    7 ≤ p := by
  obtain ⟨hlo, hhi⟩ := hband
  -- `ε = pq - 2D` is positive: otherwise `pq ≤ 2D` collapses the upper bound.
  have hε : 0 < p * q - 2 * D := by nlinarith
  -- Band defect bounds: `ε < Δq < 2ε`.
  have hΔq_lt : (6 * D - 2 * p * q) * q < 2 * (p * q - 2 * D) := by nlinarith
  have hΔq_gt : p * q - 2 * D < (6 * D - 2 * p * q) * q := by nlinarith
  -- Hence `Δ > 0`.
  have hΔpos : 0 < 6 * D - 2 * p * q := by nlinarith
  -- Parity: `4 ∣ Δ`, so `Δ ≥ 4`.
  have hΔ4 : 4 ≤ 6 * D - 2 * p * q := by
    obtain ⟨k, hk⟩ := four_dvd_bandDefect hpodd hDodd hqodd
    rw [hk] at hΔpos ⊢
    have : 0 < k := by nlinarith
    nlinarith
  -- `4q ≤ Δq < 2ε` gives `ε > 2q`, i.e. `2D < (p-2)q`.
  have hεbig : 2 * q < p * q - 2 * D := by nlinarith
  -- With `Δ > 0`, i.e. `6D > 2pq`, this forces `p > 6`.
  nlinarith

/-! ## Trust receipt

Every theorem above is kernel-reduced: no `native_decide`, hence no
`Lean.trustCompiler`, and no `sorryAx`.  The expected profile is the standard
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms singletonUnsafe_iff_twoThirdsBand
#print axioms band_width
#print axioms band_width_lt_ninth
#print axioms three_mul_mem_of_twoThirdsBand
#print axioms not_twoThirdsBand_of_int
#print axioms four_dvd_bandDefect
#print axioms seven_le_of_intBand_odd

end HalfGreedyTwoThirdsBand
end Erdos249257
