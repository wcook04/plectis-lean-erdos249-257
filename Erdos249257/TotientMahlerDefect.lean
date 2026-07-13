import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Exact dyadic totient-kernel interfaces

This module records the proof-bearing part of the quantitative dyadic-kernel
route for Erdős #249.  It deliberately separates three layers:

* elementary reduction of every even residue channel to an odd channel;
* a finite determinant certificate which is sufficient for linear
  independence of any chosen family of kernel channels;
* the exact contradiction consumer needed by a future compressed-adjoint
  construction.

The all-level producer of the determinant certificates is an analytic-number-
theory problem (CRT plus Dirichlet's theorem on primes in arithmetic
progressions).  Mathlib's Dirichlet theorem is imported here, but no axiom or
placeholder is used to pretend that the producer has already been formalised.

This is coefficient-side infrastructure, not a proof that the totient series
is irrational.
-/

namespace Erdos249257

open Module Matrix

/-- The `(j,r)` dyadic-kernel channel of Euler's totient, viewed over `ℚ`. -/
def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

/-- The canonical channels through level `e`: the two zero-residue base
channels, followed by every odd residue at levels `1,...,e`. -/
abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)

/-- The canonical family indexed without duplicate even-residue channels. -/
def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)

/-- The canonical family has exactly `2^e+1` channels. -/
theorem card_totientCanonicalIndex (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 := by
  have hgeom : (∑ i ∈ Finset.range e, 2 ^ i) + 1 = 2 ^ e := by
    induction e with
    | zero => simp
    | succ e ih =>
        rw [Finset.sum_range_succ, pow_succ]
        omega
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  omega

/-- Pull a finite family of sequences back along a finite family of evaluation
points. -/
def evaluationLinearMap {ι : Type*} [Fintype ι] (rowIndex : ι → ℕ) :
    (ℕ → ℚ) →ₗ[ℚ] (ι → ℚ) where
  toFun f i := f (rowIndex i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A square nonzero evaluation minor.  This is the exact finite object needed
to turn number-theoretic row construction into linear independence. -/
structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) where
  rowIndex : ι → ℕ
  det_ne_zero :
    Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0

/-- A nonzero square evaluation minor proves that the underlying functions are
linearly independent. -/
theorem linearIndependent_of_separatedMinorCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (family : ι → ℕ → ℚ)
    (cert : SeparatedMinorCertificate family) :
    LinearIndependent ℚ family := by
  apply LinearIndependent.of_comp (evaluationLinearMap cert.rowIndex)
  change LinearIndependent ℚ (fun j i => family j (cert.rowIndex i))
  exact Matrix.linearIndependent_cols_of_det_ne_zero cert.det_ne_zero

/-- Linear independence of the canonical family gives its exact finite-level
dimension.  This is the producer-neutral endpoint consumed both by explicit
minors and by a future adaptive CRT--Dirichlet proof. -/
theorem finrank_canonicalTotientKernel_eq_of_linearIndependent (e : ℕ)
    (hcanon : LinearIndependent ℚ (canonicalTotientKernelFamily e)) :
    finrank ℚ (Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e))) =
      2 ^ e + 1 := by
  rw [finrank_span_eq_card hcanon]
  exact card_totientCanonicalIndex e

/-- A separated minor for the canonical family gives the exact finite-level
dimension promised by the dyadic rank route.  The remaining all-level task is
to construct this certificate by CRT and Dirichlet for each `e`. -/
theorem finrank_canonicalTotientKernel_eq_of_certificate (e : ℕ)
    (cert : SeparatedMinorCertificate (canonicalTotientKernelFamily e)) :
    finrank ℚ (Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e))) =
      2 ^ e + 1 := by
  exact finrank_canonicalTotientKernel_eq_of_linearIndependent e
    (linearIndependent_of_separatedMinorCertificate
      (canonicalTotientKernelFamily e) cert)

/-- Totient of an odd number multiplied by a positive power of two. -/
theorem totient_two_pow_succ_mul_of_odd (t m : ℕ) (hm : Odd m) :
    Nat.totient (2 ^ (t + 1) * m) = 2 ^ t * Nat.totient m := by
  induction t with
  | zero =>
      simpa using Nat.totient_two_mul_of_odd hm
  | succ t ih =>
      have heven : Even (2 ^ (t + 1) * m) := by
        refine Even.mul_right ?_ m
        exact ⟨2 ^ t, by ring⟩
      calc
        Nat.totient (2 ^ (t + 1 + 1) * m) =
            Nat.totient (2 * (2 ^ (t + 1) * m)) := by
              congr 1
              ring
        _ = 2 * Nat.totient (2 ^ (t + 1) * m) :=
          Nat.totient_two_mul_of_even heven
        _ = 2 * (2 ^ t * Nat.totient m) := by rw [ih]
        _ = 2 ^ (t + 1) * Nat.totient m := by ring

/-- Repeated doubling scales the totient once the argument is already even. -/
theorem totient_two_pow_mul_two (j n : ℕ) :
    Nat.totient (2 ^ j * (2 * n)) =
      2 ^ j * Nat.totient (2 * n) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have heven : Even (2 ^ j * (2 * n)) := by
        exact Even.mul_left (by simp) _
      calc
        Nat.totient (2 ^ (j + 1) * (2 * n)) =
            Nat.totient (2 * (2 ^ j * (2 * n))) := by
              congr 1
              ring
        _ = 2 * Nat.totient (2 ^ j * (2 * n)) :=
          Nat.totient_two_mul_of_even heven
        _ = 2 * (2 ^ j * Nat.totient (2 * n)) := by rw [ih]
        _ = 2 ^ (j + 1) * Nat.totient (2 * n) := by ring

/-- Every positive zero-residue channel is a scalar multiple of the first
zero-residue channel. -/
theorem totientKernel_zero_residue (j n : ℕ) :
    totientKernelSeq (j + 1) 0 n =
      (2 ^ j : ℚ) * totientKernelSeq 1 0 n := by
  simp only [totientKernelSeq, add_zero]
  norm_cast
  rw [show 2 ^ (j + 1) * n = 2 ^ j * (2 * n) by ring]
  exact totient_two_pow_mul_two j n

/-- Exact reduction of an even residue to its odd-core channel. -/
theorem totientKernel_even_residue_reduce
    (j t s n : ℕ) (ht : t + 1 < j) (hs : Odd s) :
    totientKernelSeq j (2 ^ (t + 1) * s) n =
      (2 ^ t : ℚ) * totientKernelSeq (j - (t + 1)) s n := by
  simp only [totientKernelSeq]
  norm_cast
  have hpow : 2 ^ j = 2 ^ (t + 1) * 2 ^ (j - (t + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [show 2 ^ j * n + 2 ^ (t + 1) * s =
      2 ^ (t + 1) * (2 ^ (j - (t + 1)) * n + s) by
        rw [hpow]
        ring]
  apply totient_two_pow_succ_mul_of_odd
  have hevenPow : Even (2 ^ (j - (t + 1))) := by
    refine ⟨2 ^ (j - (t + 1) - 1), ?_⟩
    have hjt : 0 < j - (t + 1) := by omega
    calc
      2 ^ (j - (t + 1)) = 2 ^ ((j - (t + 1) - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (j - (t + 1) - 1) + 2 ^ (j - (t + 1) - 1) := by
        rw [pow_succ]
        ring
  exact (hevenPow.mul_right n).add_odd hs

/-- The exact proof object required from a future totient-specific compressed
adjoint construction. -/
structure CompressedAdjointCertificate (v : ℕ) where
  Q : ℕ
  A : ℤ
  boundary : ℤ
  v_pos : 0 < v
  Q_pos : 0 < Q
  A_ne_zero : A ≠ 0
  identity : (Q : ℤ) * (v : ℤ) * A = boundary
  boundary_small : |boundary| < (Q : ℤ) * (v : ℤ)

/-- A compressed-adjoint certificate is impossible: its boundary is both a
nonzero multiple of `Q*v` and strictly smaller than `Q*v`. -/
theorem false_of_compressedAdjointCertificate {v : ℕ}
    (cert : CompressedAdjointCertificate v) : False := by
  have hQv_pos : (0 : ℤ) < (cert.Q : ℤ) * (v : ℤ) := by
    exact mul_pos (by exact_mod_cast cert.Q_pos) (by exact_mod_cast cert.v_pos)
  have hA_abs : (1 : ℤ) ≤ |cert.A| := by
    exact Int.one_le_abs cert.A_ne_zero
  have hlower : (cert.Q : ℤ) * (v : ℤ) ≤ |cert.boundary| := by
    rw [← cert.identity, abs_mul, abs_mul]
    simpa [abs_of_pos hQv_pos] using
      mul_le_mul_of_nonneg_left hA_abs hQv_pos.le
  exact (not_lt_of_ge hlower) cert.boundary_small

end Erdos249257
