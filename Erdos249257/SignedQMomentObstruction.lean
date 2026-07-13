import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Signed finite q-moment determinants

This file isolates two algebraic cores of the signed-Hankel route for Erdős
#249: a positivity-free rectangular determinant expansion derived from the
Leibniz formula, and the unique-largest-dyadic-exponent parity argument that
forces a cleared common numerator to be odd and hence non-zero.
-/

namespace Erdos249257.SignedQMomentObstruction

open scoped BigOperators
open Matrix

/-! ## A rectangular Cauchy–Binet expansion

The pinned Mathlib determinant API does not currently expose rectangular
Cauchy–Binet directly.  The following compact expansion is derived from the
Leibniz formula.  Non-injective maps remain in the sum here; in Vandermonde
applications their determinant is zero.
-/

theorem det_mul_rectangular
    {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix ι κ R) (N : Matrix κ ι R) :
    Matrix.det (M * N) =
      ∑ p : ι → κ, Matrix.det (fun i j ↦ M i (p j)) * ∏ i, N (p i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  congr 1
  funext p
  rw [Finset.sum_mul]
  congr 1
  funext σ
  rw [Finset.prod_mul_distrib]
  ring

/-- A finite signed moment matrix on an arbitrary finite atom type.  Here `w`
is the full atom mass (for the target application, `w N = a N * x N`). -/
def finiteSignedMomentMatrix
    {R κ : Type*} [CommRing R] [Fintype κ]
    (n : ℕ) (w x : κ → R) : Matrix (Fin n) (Fin n) R :=
  fun i j ↦ ∑ a : κ, w a * x a ^ (i.1 + j.1)

/-! ## Unique-terminal dyadic parity -/

private theorem even_finset_sum {α : Type*} (s : Finset α) (f : α → ℤ)
    (h : ∀ i ∈ s, Even (f i)) : Even (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih (fun i hi ↦ h i (by simp [hi])))

private theorem not_even_finset_sum_of_unique_not_even
    {α : Type*} (s : Finset α) (f : α → ℤ) (m : α)
    (hm : m ∈ s) (hodd : ¬ Even (f m))
    (heven : ∀ i ∈ s, i ≠ m → Even (f i)) :
    ¬ Even (∑ i ∈ s, f i) := by
  classical
  rw [← Finset.sum_erase_add _ _ hm]
  intro htotal
  have hrest : Even (∑ i ∈ s.erase m, f i) :=
    even_finset_sum (s.erase m) f (fun i hi ↦
      heven i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  exact hodd ((Int.even_add.mp htotal).mp hrest)

/-- If one dyadic denominator exponent is uniquely largest and its numerator
is odd, the common numerator obtained by clearing that denominator is odd. -/
theorem scaled_dyadic_sum_odd {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) % 2 = 1 := by
  rw [← Int.not_even_iff]
  apply not_even_finset_sum_of_unique_not_even s
      (fun i ↦ u i * (2 : ℤ) ^ (e m - e i)) m hm
  · simpa using hu
  · intro i hi him
    have hne : e m - e i ≠ 0 :=
      Nat.ne_of_gt (Nat.sub_pos_of_lt (hmax i hi him))
    have hp : Even ((2 : ℤ) ^ (e m - e i)) :=
      Int.even_pow.mpr ⟨⟨1, rfl⟩, hne⟩
    exact hp.mul_left (u i)

/-- The same unique-terminal hypothesis gives non-vanishing after common
dyadic denominator clearing. -/
theorem scaled_dyadic_sum_ne_zero {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) ≠ 0 := by
  intro hzero
  have hodd := scaled_dyadic_sum_odd s u e m hm hu hmax
  simp [hzero] at hodd

/-! ## Concrete truncated moments -/

/-- The finite signed `q = 1/2` moment used by the Möbius Hankel lane. -/
def truncatedMoment (a : ℕ → ℤ) (Y k : ℕ) : ℚ :=
  ∑ N ∈ Finset.Icc 1 Y,
    (a N : ℚ) * ((1 / (2 : ℚ)) ^ N) ^ (k + 1)

/-- Hankel matrix associated to a moment sequence. -/
def hankelMatrix (m : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ m (i.1 + j.1)

/-- Order-`n` Hankel determinant associated to a moment sequence. -/
def hankelDet (m : ℕ → ℚ) (n : ℕ) : ℚ :=
  Matrix.det (hankelMatrix m n)

end Erdos249257.SignedQMomentObstruction
