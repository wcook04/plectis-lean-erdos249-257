import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=19 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000

theorem prime_lucas_46558517 : Nat.Prime 46558517 := by
  apply lucas_primality 46558517 (2 : ZMod 46558517)
  ·
      have fermat_0 : (2 : ZMod 46558517) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 46558517) ^ 2 = 4 := by
        calc
          (2 : ZMod 46558517) ^ 2 = (2 : ZMod 46558517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 1 * (2 : ZMod 46558517) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 46558517) ^ 5 = 32 := by
        calc
          (2 : ZMod 46558517) ^ 5 = (2 : ZMod 46558517) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 2 * (2 : ZMod 46558517) ^ 2) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 46558517) ^ 11 = 2048 := by
        calc
          (2 : ZMod 46558517) ^ 11 = (2 : ZMod 46558517) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 5 * (2 : ZMod 46558517) ^ 5) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 46558517) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 46558517) ^ 22 = (2 : ZMod 46558517) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 11 * (2 : ZMod 46558517) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 46558517) ^ 44 = 3837449 := by
        calc
          (2 : ZMod 46558517) ^ 44 = (2 : ZMod 46558517) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 22 * (2 : ZMod 46558517) ^ 22 := by rw [pow_add]
          _ = 3837449 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 46558517) ^ 88 = 21485671 := by
        calc
          (2 : ZMod 46558517) ^ 88 = (2 : ZMod 46558517) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 44 * (2 : ZMod 46558517) ^ 44 := by rw [pow_add]
          _ = 21485671 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 46558517) ^ 177 = 14055341 := by
        calc
          (2 : ZMod 46558517) ^ 177 = (2 : ZMod 46558517) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 88 * (2 : ZMod 46558517) ^ 88) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 14055341 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 46558517) ^ 355 = 8377543 := by
        calc
          (2 : ZMod 46558517) ^ 355 = (2 : ZMod 46558517) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 177 * (2 : ZMod 46558517) ^ 177) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 8377543 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 46558517) ^ 710 = 33579226 := by
        calc
          (2 : ZMod 46558517) ^ 710 = (2 : ZMod 46558517) ^ (355 + 355) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 355 * (2 : ZMod 46558517) ^ 355 := by rw [pow_add]
          _ = 33579226 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 46558517) ^ 1420 = 11179336 := by
        calc
          (2 : ZMod 46558517) ^ 1420 = (2 : ZMod 46558517) ^ (710 + 710) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 710 * (2 : ZMod 46558517) ^ 710 := by rw [pow_add]
          _ = 11179336 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 46558517) ^ 2841 = 28148218 := by
        calc
          (2 : ZMod 46558517) ^ 2841 = (2 : ZMod 46558517) ^ (1420 + 1420 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 1420 * (2 : ZMod 46558517) ^ 1420) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 28148218 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 46558517) ^ 5683 = 38898351 := by
        calc
          (2 : ZMod 46558517) ^ 5683 = (2 : ZMod 46558517) ^ (2841 + 2841 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 2841 * (2 : ZMod 46558517) ^ 2841) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 38898351 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 46558517) ^ 11366 = 25145803 := by
        calc
          (2 : ZMod 46558517) ^ 11366 = (2 : ZMod 46558517) ^ (5683 + 5683) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 5683 * (2 : ZMod 46558517) ^ 5683 := by rw [pow_add]
          _ = 25145803 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 46558517) ^ 22733 = 5807482 := by
        calc
          (2 : ZMod 46558517) ^ 22733 = (2 : ZMod 46558517) ^ (11366 + 11366 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 11366 * (2 : ZMod 46558517) ^ 11366) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 5807482 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 46558517) ^ 45467 = 40840667 := by
        calc
          (2 : ZMod 46558517) ^ 45467 = (2 : ZMod 46558517) ^ (22733 + 22733 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 22733 * (2 : ZMod 46558517) ^ 22733) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 40840667 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 46558517) ^ 90934 = 45516964 := by
        calc
          (2 : ZMod 46558517) ^ 90934 = (2 : ZMod 46558517) ^ (45467 + 45467) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 45467 * (2 : ZMod 46558517) ^ 45467 := by rw [pow_add]
          _ = 45516964 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 46558517) ^ 181869 = 38411418 := by
        calc
          (2 : ZMod 46558517) ^ 181869 = (2 : ZMod 46558517) ^ (90934 + 90934 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 90934 * (2 : ZMod 46558517) ^ 90934) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 38411418 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 46558517) ^ 363738 = 3525091 := by
        calc
          (2 : ZMod 46558517) ^ 363738 = (2 : ZMod 46558517) ^ (181869 + 181869) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 181869 * (2 : ZMod 46558517) ^ 181869 := by rw [pow_add]
          _ = 3525091 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 46558517) ^ 727476 = 31163566 := by
        calc
          (2 : ZMod 46558517) ^ 727476 = (2 : ZMod 46558517) ^ (363738 + 363738) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 363738 * (2 : ZMod 46558517) ^ 363738 := by rw [pow_add]
          _ = 31163566 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 46558517) ^ 1454953 = 30103992 := by
        calc
          (2 : ZMod 46558517) ^ 1454953 = (2 : ZMod 46558517) ^ (727476 + 727476 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 727476 * (2 : ZMod 46558517) ^ 727476) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 30103992 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 46558517) ^ 2909907 = 43067322 := by
        calc
          (2 : ZMod 46558517) ^ 2909907 = (2 : ZMod 46558517) ^ (1454953 + 1454953 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 1454953 * (2 : ZMod 46558517) ^ 1454953) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 43067322 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 46558517) ^ 5819814 = 28038146 := by
        calc
          (2 : ZMod 46558517) ^ 5819814 = (2 : ZMod 46558517) ^ (2909907 + 2909907) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 2909907 * (2 : ZMod 46558517) ^ 2909907 := by rw [pow_add]
          _ = 28038146 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 46558517) ^ 11639629 = 9517774 := by
        calc
          (2 : ZMod 46558517) ^ 11639629 = (2 : ZMod 46558517) ^ (5819814 + 5819814 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 5819814 * (2 : ZMod 46558517) ^ 5819814) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 9517774 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 46558517) ^ 23279258 = 46558516 := by
        calc
          (2 : ZMod 46558517) ^ 23279258 = (2 : ZMod 46558517) ^ (11639629 + 11639629) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 11639629 * (2 : ZMod 46558517) ^ 11639629 := by rw [pow_add]
          _ = 46558516 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 46558517) ^ 46558516 = 1 := by
        calc
          (2 : ZMod 46558517) ^ 46558516 = (2 : ZMod 46558517) ^ (23279258 + 23279258) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 23279258 * (2 : ZMod 46558517) ^ 23279258 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (557, 1), (20897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (557, 1), (20897, 1)] : List FactorBlock).map factorBlockValue).prod = 46558517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 46558517) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 46558517) ^ 2 = 4 := by
        calc
          (2 : ZMod 46558517) ^ 2 = (2 : ZMod 46558517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 1 * (2 : ZMod 46558517) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 46558517) ^ 5 = 32 := by
        calc
          (2 : ZMod 46558517) ^ 5 = (2 : ZMod 46558517) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 2 * (2 : ZMod 46558517) ^ 2) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 46558517) ^ 11 = 2048 := by
        calc
          (2 : ZMod 46558517) ^ 11 = (2 : ZMod 46558517) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 5 * (2 : ZMod 46558517) ^ 5) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 46558517) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 46558517) ^ 22 = (2 : ZMod 46558517) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 11 * (2 : ZMod 46558517) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 46558517) ^ 44 = 3837449 := by
        calc
          (2 : ZMod 46558517) ^ 44 = (2 : ZMod 46558517) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 22 * (2 : ZMod 46558517) ^ 22 := by rw [pow_add]
          _ = 3837449 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 46558517) ^ 88 = 21485671 := by
        calc
          (2 : ZMod 46558517) ^ 88 = (2 : ZMod 46558517) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 44 * (2 : ZMod 46558517) ^ 44 := by rw [pow_add]
          _ = 21485671 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 46558517) ^ 177 = 14055341 := by
        calc
          (2 : ZMod 46558517) ^ 177 = (2 : ZMod 46558517) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 88 * (2 : ZMod 46558517) ^ 88) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 14055341 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 46558517) ^ 355 = 8377543 := by
        calc
          (2 : ZMod 46558517) ^ 355 = (2 : ZMod 46558517) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 177 * (2 : ZMod 46558517) ^ 177) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 8377543 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 46558517) ^ 710 = 33579226 := by
        calc
          (2 : ZMod 46558517) ^ 710 = (2 : ZMod 46558517) ^ (355 + 355) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 355 * (2 : ZMod 46558517) ^ 355 := by rw [pow_add]
          _ = 33579226 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 46558517) ^ 1420 = 11179336 := by
        calc
          (2 : ZMod 46558517) ^ 1420 = (2 : ZMod 46558517) ^ (710 + 710) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 710 * (2 : ZMod 46558517) ^ 710 := by rw [pow_add]
          _ = 11179336 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 46558517) ^ 2841 = 28148218 := by
        calc
          (2 : ZMod 46558517) ^ 2841 = (2 : ZMod 46558517) ^ (1420 + 1420 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 1420 * (2 : ZMod 46558517) ^ 1420) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 28148218 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 46558517) ^ 5683 = 38898351 := by
        calc
          (2 : ZMod 46558517) ^ 5683 = (2 : ZMod 46558517) ^ (2841 + 2841 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 2841 * (2 : ZMod 46558517) ^ 2841) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 38898351 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 46558517) ^ 11366 = 25145803 := by
        calc
          (2 : ZMod 46558517) ^ 11366 = (2 : ZMod 46558517) ^ (5683 + 5683) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 5683 * (2 : ZMod 46558517) ^ 5683 := by rw [pow_add]
          _ = 25145803 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 46558517) ^ 22733 = 5807482 := by
        calc
          (2 : ZMod 46558517) ^ 22733 = (2 : ZMod 46558517) ^ (11366 + 11366 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 11366 * (2 : ZMod 46558517) ^ 11366) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 5807482 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 46558517) ^ 45467 = 40840667 := by
        calc
          (2 : ZMod 46558517) ^ 45467 = (2 : ZMod 46558517) ^ (22733 + 22733 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 22733 * (2 : ZMod 46558517) ^ 22733) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 40840667 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 46558517) ^ 90934 = 45516964 := by
        calc
          (2 : ZMod 46558517) ^ 90934 = (2 : ZMod 46558517) ^ (45467 + 45467) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 45467 * (2 : ZMod 46558517) ^ 45467 := by rw [pow_add]
          _ = 45516964 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 46558517) ^ 181869 = 38411418 := by
        calc
          (2 : ZMod 46558517) ^ 181869 = (2 : ZMod 46558517) ^ (90934 + 90934 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 90934 * (2 : ZMod 46558517) ^ 90934) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 38411418 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 46558517) ^ 363738 = 3525091 := by
        calc
          (2 : ZMod 46558517) ^ 363738 = (2 : ZMod 46558517) ^ (181869 + 181869) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 181869 * (2 : ZMod 46558517) ^ 181869 := by rw [pow_add]
          _ = 3525091 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 46558517) ^ 727476 = 31163566 := by
        calc
          (2 : ZMod 46558517) ^ 727476 = (2 : ZMod 46558517) ^ (363738 + 363738) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 363738 * (2 : ZMod 46558517) ^ 363738 := by rw [pow_add]
          _ = 31163566 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 46558517) ^ 1454953 = 30103992 := by
        calc
          (2 : ZMod 46558517) ^ 1454953 = (2 : ZMod 46558517) ^ (727476 + 727476 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 727476 * (2 : ZMod 46558517) ^ 727476) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 30103992 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 46558517) ^ 2909907 = 43067322 := by
        calc
          (2 : ZMod 46558517) ^ 2909907 = (2 : ZMod 46558517) ^ (1454953 + 1454953 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 1454953 * (2 : ZMod 46558517) ^ 1454953) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 43067322 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 46558517) ^ 5819814 = 28038146 := by
        calc
          (2 : ZMod 46558517) ^ 5819814 = (2 : ZMod 46558517) ^ (2909907 + 2909907) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 2909907 * (2 : ZMod 46558517) ^ 2909907 := by rw [pow_add]
          _ = 28038146 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 46558517) ^ 11639629 = 9517774 := by
        calc
          (2 : ZMod 46558517) ^ 11639629 = (2 : ZMod 46558517) ^ (5819814 + 5819814 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 5819814 * (2 : ZMod 46558517) ^ 5819814) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 9517774 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 46558517) ^ 23279258 = 46558516 := by
        calc
          (2 : ZMod 46558517) ^ 23279258 = (2 : ZMod 46558517) ^ (11639629 + 11639629) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 11639629 * (2 : ZMod 46558517) ^ 11639629 := by rw [pow_add]
          _ = 46558516 := by rw [factor_0_23]; decide
      change (2 : ZMod 46558517) ^ 23279258 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 46558517) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 46558517) ^ 2 = 4 := by
        calc
          (2 : ZMod 46558517) ^ 2 = (2 : ZMod 46558517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 1 * (2 : ZMod 46558517) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 46558517) ^ 5 = 32 := by
        calc
          (2 : ZMod 46558517) ^ 5 = (2 : ZMod 46558517) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 2 * (2 : ZMod 46558517) ^ 2) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 46558517) ^ 10 = 1024 := by
        calc
          (2 : ZMod 46558517) ^ 10 = (2 : ZMod 46558517) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 5 * (2 : ZMod 46558517) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 46558517) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 46558517) ^ 20 = (2 : ZMod 46558517) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 10 * (2 : ZMod 46558517) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 46558517) ^ 40 = 32248821 := by
        calc
          (2 : ZMod 46558517) ^ 40 = (2 : ZMod 46558517) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 20 * (2 : ZMod 46558517) ^ 20 := by rw [pow_add]
          _ = 32248821 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 46558517) ^ 81 = 31085622 := by
        calc
          (2 : ZMod 46558517) ^ 81 = (2 : ZMod 46558517) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 40 * (2 : ZMod 46558517) ^ 40) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 31085622 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 46558517) ^ 163 = 41032256 := by
        calc
          (2 : ZMod 46558517) ^ 163 = (2 : ZMod 46558517) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 81 * (2 : ZMod 46558517) ^ 81) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 41032256 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 46558517) ^ 326 = 13557658 := by
        calc
          (2 : ZMod 46558517) ^ 326 = (2 : ZMod 46558517) ^ (163 + 163) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 163 * (2 : ZMod 46558517) ^ 163 := by rw [pow_add]
          _ = 13557658 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 46558517) ^ 653 = 43589587 := by
        calc
          (2 : ZMod 46558517) ^ 653 = (2 : ZMod 46558517) ^ (326 + 326 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 326 * (2 : ZMod 46558517) ^ 326) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 43589587 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 46558517) ^ 1306 = 40347943 := by
        calc
          (2 : ZMod 46558517) ^ 1306 = (2 : ZMod 46558517) ^ (653 + 653) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 653 * (2 : ZMod 46558517) ^ 653 := by rw [pow_add]
          _ = 40347943 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 46558517) ^ 2612 = 12234894 := by
        calc
          (2 : ZMod 46558517) ^ 2612 = (2 : ZMod 46558517) ^ (1306 + 1306) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 1306 * (2 : ZMod 46558517) ^ 1306 := by rw [pow_add]
          _ = 12234894 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 46558517) ^ 5224 = 15258686 := by
        calc
          (2 : ZMod 46558517) ^ 5224 = (2 : ZMod 46558517) ^ (2612 + 2612) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 2612 * (2 : ZMod 46558517) ^ 2612 := by rw [pow_add]
          _ = 15258686 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 46558517) ^ 10448 = 41117363 := by
        calc
          (2 : ZMod 46558517) ^ 10448 = (2 : ZMod 46558517) ^ (5224 + 5224) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 5224 * (2 : ZMod 46558517) ^ 5224 := by rw [pow_add]
          _ = 41117363 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 46558517) ^ 20897 = 29836138 := by
        calc
          (2 : ZMod 46558517) ^ 20897 = (2 : ZMod 46558517) ^ (10448 + 10448 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 10448 * (2 : ZMod 46558517) ^ 10448) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 29836138 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 46558517) ^ 41794 = 10396404 := by
        calc
          (2 : ZMod 46558517) ^ 41794 = (2 : ZMod 46558517) ^ (20897 + 20897) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 20897 * (2 : ZMod 46558517) ^ 20897 := by rw [pow_add]
          _ = 10396404 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 46558517) ^ 83588 = 37942369 := by
        calc
          (2 : ZMod 46558517) ^ 83588 = (2 : ZMod 46558517) ^ (41794 + 41794) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 41794 * (2 : ZMod 46558517) ^ 41794 := by rw [pow_add]
          _ = 37942369 := by rw [factor_1_15]; decide
      change (2 : ZMod 46558517) ^ 83588 ≠ 1
      rw [factor_1_16]
      decide
    ·
      have factor_2_0 : (2 : ZMod 46558517) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 46558517) ^ 2 = 4 := by
        calc
          (2 : ZMod 46558517) ^ 2 = (2 : ZMod 46558517) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 1 * (2 : ZMod 46558517) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 46558517) ^ 4 = 16 := by
        calc
          (2 : ZMod 46558517) ^ 4 = (2 : ZMod 46558517) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 2 * (2 : ZMod 46558517) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 46558517) ^ 8 = 256 := by
        calc
          (2 : ZMod 46558517) ^ 8 = (2 : ZMod 46558517) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 4 * (2 : ZMod 46558517) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 46558517) ^ 17 = 131072 := by
        calc
          (2 : ZMod 46558517) ^ 17 = (2 : ZMod 46558517) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 8 * (2 : ZMod 46558517) ^ 8) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 46558517) ^ 34 = 46334928 := by
        calc
          (2 : ZMod 46558517) ^ 34 = (2 : ZMod 46558517) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 17 * (2 : ZMod 46558517) ^ 17 := by rw [pow_add]
          _ = 46334928 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 46558517) ^ 69 = 22945843 := by
        calc
          (2 : ZMod 46558517) ^ 69 = (2 : ZMod 46558517) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 34 * (2 : ZMod 46558517) ^ 34) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 22945843 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 46558517) ^ 139 = 38151864 := by
        calc
          (2 : ZMod 46558517) ^ 139 = (2 : ZMod 46558517) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 69 * (2 : ZMod 46558517) ^ 69) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 38151864 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 46558517) ^ 278 = 36447388 := by
        calc
          (2 : ZMod 46558517) ^ 278 = (2 : ZMod 46558517) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 139 * (2 : ZMod 46558517) ^ 139 := by rw [pow_add]
          _ = 36447388 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 46558517) ^ 557 = 30721824 := by
        calc
          (2 : ZMod 46558517) ^ 557 = (2 : ZMod 46558517) ^ (278 + 278 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = ((2 : ZMod 46558517) ^ 278 * (2 : ZMod 46558517) ^ 278) * (2 : ZMod 46558517) := by rw [pow_succ, pow_add]
          _ = 30721824 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 46558517) ^ 1114 = 31061370 := by
        calc
          (2 : ZMod 46558517) ^ 1114 = (2 : ZMod 46558517) ^ (557 + 557) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 557 * (2 : ZMod 46558517) ^ 557 := by rw [pow_add]
          _ = 31061370 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 46558517) ^ 2228 = 23978468 := by
        calc
          (2 : ZMod 46558517) ^ 2228 = (2 : ZMod 46558517) ^ (1114 + 1114) :=
            congrArg (fun n : ℕ => (2 : ZMod 46558517) ^ n) (by norm_num)
          _ = (2 : ZMod 46558517) ^ 1114 * (2 : ZMod 46558517) ^ 1114 := by rw [pow_add]
          _ = 23978468 := by rw [factor_2_10]; decide
      change (2 : ZMod 46558517) ^ 2228 ≠ 1
      rw [factor_2_11]
      decide

#print axioms prime_lucas_46558517

end TotientTailPeriodKiller
end Erdos249257
