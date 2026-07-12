import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_77013413 : Nat.Prime 77013413 := by
  apply lucas_primality 77013413 (2 : ZMod 77013413)
  ·
      have fermat_0 : (2 : ZMod 77013413) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 77013413) ^ 2 = 4 := by
        calc
          (2 : ZMod 77013413) ^ 2 = (2 : ZMod 77013413) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 1 * (2 : ZMod 77013413) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 77013413) ^ 4 = 16 := by
        calc
          (2 : ZMod 77013413) ^ 4 = (2 : ZMod 77013413) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 2 * (2 : ZMod 77013413) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 77013413) ^ 9 = 512 := by
        calc
          (2 : ZMod 77013413) ^ 9 = (2 : ZMod 77013413) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 4 * (2 : ZMod 77013413) ^ 4) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 77013413) ^ 18 = 262144 := by
        calc
          (2 : ZMod 77013413) ^ 18 = (2 : ZMod 77013413) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 9 * (2 : ZMod 77013413) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 77013413) ^ 36 = 23512340 := by
        calc
          (2 : ZMod 77013413) ^ 36 = (2 : ZMod 77013413) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 18 * (2 : ZMod 77013413) ^ 18 := by rw [pow_add]
          _ = 23512340 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 77013413) ^ 73 = 26825601 := by
        calc
          (2 : ZMod 77013413) ^ 73 = (2 : ZMod 77013413) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 36 * (2 : ZMod 77013413) ^ 36) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 26825601 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 77013413) ^ 146 = 19679 := by
        calc
          (2 : ZMod 77013413) ^ 146 = (2 : ZMod 77013413) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 73 * (2 : ZMod 77013413) ^ 73 := by rw [pow_add]
          _ = 19679 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 77013413) ^ 293 = 4391952 := by
        calc
          (2 : ZMod 77013413) ^ 293 = (2 : ZMod 77013413) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 146 * (2 : ZMod 77013413) ^ 146) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 4391952 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 77013413) ^ 587 = 1739692 := by
        calc
          (2 : ZMod 77013413) ^ 587 = (2 : ZMod 77013413) ^ (293 + 293 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 293 * (2 : ZMod 77013413) ^ 293) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 1739692 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 77013413) ^ 1175 = 33288167 := by
        calc
          (2 : ZMod 77013413) ^ 1175 = (2 : ZMod 77013413) ^ (587 + 587 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 587 * (2 : ZMod 77013413) ^ 587) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 33288167 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 77013413) ^ 2350 = 37221712 := by
        calc
          (2 : ZMod 77013413) ^ 2350 = (2 : ZMod 77013413) ^ (1175 + 1175) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 1175 * (2 : ZMod 77013413) ^ 1175 := by rw [pow_add]
          _ = 37221712 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 77013413) ^ 4700 = 24036957 := by
        calc
          (2 : ZMod 77013413) ^ 4700 = (2 : ZMod 77013413) ^ (2350 + 2350) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 2350 * (2 : ZMod 77013413) ^ 2350 := by rw [pow_add]
          _ = 24036957 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 77013413) ^ 9401 = 75798330 := by
        calc
          (2 : ZMod 77013413) ^ 9401 = (2 : ZMod 77013413) ^ (4700 + 4700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 4700 * (2 : ZMod 77013413) ^ 4700) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 75798330 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 77013413) ^ 18802 = 2556266 := by
        calc
          (2 : ZMod 77013413) ^ 18802 = (2 : ZMod 77013413) ^ (9401 + 9401) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 9401 * (2 : ZMod 77013413) ^ 9401 := by rw [pow_add]
          _ = 2556266 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 77013413) ^ 37604 = 61796532 := by
        calc
          (2 : ZMod 77013413) ^ 37604 = (2 : ZMod 77013413) ^ (18802 + 18802) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 18802 * (2 : ZMod 77013413) ^ 18802 := by rw [pow_add]
          _ = 61796532 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 77013413) ^ 75208 = 10983929 := by
        calc
          (2 : ZMod 77013413) ^ 75208 = (2 : ZMod 77013413) ^ (37604 + 37604) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 37604 * (2 : ZMod 77013413) ^ 37604 := by rw [pow_add]
          _ = 10983929 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 77013413) ^ 150416 = 24913870 := by
        calc
          (2 : ZMod 77013413) ^ 150416 = (2 : ZMod 77013413) ^ (75208 + 75208) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 75208 * (2 : ZMod 77013413) ^ 75208 := by rw [pow_add]
          _ = 24913870 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 77013413) ^ 300833 = 67676791 := by
        calc
          (2 : ZMod 77013413) ^ 300833 = (2 : ZMod 77013413) ^ (150416 + 150416 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 150416 * (2 : ZMod 77013413) ^ 150416) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 67676791 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 77013413) ^ 601667 = 54043630 := by
        calc
          (2 : ZMod 77013413) ^ 601667 = (2 : ZMod 77013413) ^ (300833 + 300833 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 300833 * (2 : ZMod 77013413) ^ 300833) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 54043630 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 77013413) ^ 1203334 = 47999041 := by
        calc
          (2 : ZMod 77013413) ^ 1203334 = (2 : ZMod 77013413) ^ (601667 + 601667) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 601667 * (2 : ZMod 77013413) ^ 601667 := by rw [pow_add]
          _ = 47999041 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 77013413) ^ 2406669 = 22049116 := by
        calc
          (2 : ZMod 77013413) ^ 2406669 = (2 : ZMod 77013413) ^ (1203334 + 1203334 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 1203334 * (2 : ZMod 77013413) ^ 1203334) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 22049116 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 77013413) ^ 4813338 = 19975400 := by
        calc
          (2 : ZMod 77013413) ^ 4813338 = (2 : ZMod 77013413) ^ (2406669 + 2406669) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 2406669 * (2 : ZMod 77013413) ^ 2406669 := by rw [pow_add]
          _ = 19975400 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 77013413) ^ 9626676 = 23649897 := by
        calc
          (2 : ZMod 77013413) ^ 9626676 = (2 : ZMod 77013413) ^ (4813338 + 4813338) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 4813338 * (2 : ZMod 77013413) ^ 4813338 := by rw [pow_add]
          _ = 23649897 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 77013413) ^ 19253353 = 29713618 := by
        calc
          (2 : ZMod 77013413) ^ 19253353 = (2 : ZMod 77013413) ^ (9626676 + 9626676 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 9626676 * (2 : ZMod 77013413) ^ 9626676) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 29713618 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 77013413) ^ 38506706 = 77013412 := by
        calc
          (2 : ZMod 77013413) ^ 38506706 = (2 : ZMod 77013413) ^ (19253353 + 19253353) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 19253353 * (2 : ZMod 77013413) ^ 19253353 := by rw [pow_add]
          _ = 77013412 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 77013413) ^ 77013412 = 1 := by
        calc
          (2 : ZMod 77013413) ^ 77013412 = (2 : ZMod 77013413) ^ (38506706 + 38506706) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 38506706 * (2 : ZMod 77013413) ^ 38506706 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (2750479, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (2750479, 1)] : List FactorBlock).map factorBlockValue).prod = 77013413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 77013413) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 77013413) ^ 2 = 4 := by
        calc
          (2 : ZMod 77013413) ^ 2 = (2 : ZMod 77013413) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 1 * (2 : ZMod 77013413) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 77013413) ^ 4 = 16 := by
        calc
          (2 : ZMod 77013413) ^ 4 = (2 : ZMod 77013413) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 2 * (2 : ZMod 77013413) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 77013413) ^ 9 = 512 := by
        calc
          (2 : ZMod 77013413) ^ 9 = (2 : ZMod 77013413) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 4 * (2 : ZMod 77013413) ^ 4) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 77013413) ^ 18 = 262144 := by
        calc
          (2 : ZMod 77013413) ^ 18 = (2 : ZMod 77013413) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 9 * (2 : ZMod 77013413) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 77013413) ^ 36 = 23512340 := by
        calc
          (2 : ZMod 77013413) ^ 36 = (2 : ZMod 77013413) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 18 * (2 : ZMod 77013413) ^ 18 := by rw [pow_add]
          _ = 23512340 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 77013413) ^ 73 = 26825601 := by
        calc
          (2 : ZMod 77013413) ^ 73 = (2 : ZMod 77013413) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 36 * (2 : ZMod 77013413) ^ 36) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 26825601 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 77013413) ^ 146 = 19679 := by
        calc
          (2 : ZMod 77013413) ^ 146 = (2 : ZMod 77013413) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 73 * (2 : ZMod 77013413) ^ 73 := by rw [pow_add]
          _ = 19679 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 77013413) ^ 293 = 4391952 := by
        calc
          (2 : ZMod 77013413) ^ 293 = (2 : ZMod 77013413) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 146 * (2 : ZMod 77013413) ^ 146) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 4391952 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 77013413) ^ 587 = 1739692 := by
        calc
          (2 : ZMod 77013413) ^ 587 = (2 : ZMod 77013413) ^ (293 + 293 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 293 * (2 : ZMod 77013413) ^ 293) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 1739692 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 77013413) ^ 1175 = 33288167 := by
        calc
          (2 : ZMod 77013413) ^ 1175 = (2 : ZMod 77013413) ^ (587 + 587 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 587 * (2 : ZMod 77013413) ^ 587) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 33288167 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 77013413) ^ 2350 = 37221712 := by
        calc
          (2 : ZMod 77013413) ^ 2350 = (2 : ZMod 77013413) ^ (1175 + 1175) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 1175 * (2 : ZMod 77013413) ^ 1175 := by rw [pow_add]
          _ = 37221712 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 77013413) ^ 4700 = 24036957 := by
        calc
          (2 : ZMod 77013413) ^ 4700 = (2 : ZMod 77013413) ^ (2350 + 2350) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 2350 * (2 : ZMod 77013413) ^ 2350 := by rw [pow_add]
          _ = 24036957 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 77013413) ^ 9401 = 75798330 := by
        calc
          (2 : ZMod 77013413) ^ 9401 = (2 : ZMod 77013413) ^ (4700 + 4700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 4700 * (2 : ZMod 77013413) ^ 4700) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 75798330 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 77013413) ^ 18802 = 2556266 := by
        calc
          (2 : ZMod 77013413) ^ 18802 = (2 : ZMod 77013413) ^ (9401 + 9401) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 9401 * (2 : ZMod 77013413) ^ 9401 := by rw [pow_add]
          _ = 2556266 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 77013413) ^ 37604 = 61796532 := by
        calc
          (2 : ZMod 77013413) ^ 37604 = (2 : ZMod 77013413) ^ (18802 + 18802) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 18802 * (2 : ZMod 77013413) ^ 18802 := by rw [pow_add]
          _ = 61796532 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 77013413) ^ 75208 = 10983929 := by
        calc
          (2 : ZMod 77013413) ^ 75208 = (2 : ZMod 77013413) ^ (37604 + 37604) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 37604 * (2 : ZMod 77013413) ^ 37604 := by rw [pow_add]
          _ = 10983929 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 77013413) ^ 150416 = 24913870 := by
        calc
          (2 : ZMod 77013413) ^ 150416 = (2 : ZMod 77013413) ^ (75208 + 75208) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 75208 * (2 : ZMod 77013413) ^ 75208 := by rw [pow_add]
          _ = 24913870 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 77013413) ^ 300833 = 67676791 := by
        calc
          (2 : ZMod 77013413) ^ 300833 = (2 : ZMod 77013413) ^ (150416 + 150416 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 150416 * (2 : ZMod 77013413) ^ 150416) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 67676791 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 77013413) ^ 601667 = 54043630 := by
        calc
          (2 : ZMod 77013413) ^ 601667 = (2 : ZMod 77013413) ^ (300833 + 300833 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 300833 * (2 : ZMod 77013413) ^ 300833) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 54043630 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 77013413) ^ 1203334 = 47999041 := by
        calc
          (2 : ZMod 77013413) ^ 1203334 = (2 : ZMod 77013413) ^ (601667 + 601667) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 601667 * (2 : ZMod 77013413) ^ 601667 := by rw [pow_add]
          _ = 47999041 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 77013413) ^ 2406669 = 22049116 := by
        calc
          (2 : ZMod 77013413) ^ 2406669 = (2 : ZMod 77013413) ^ (1203334 + 1203334 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 1203334 * (2 : ZMod 77013413) ^ 1203334) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 22049116 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 77013413) ^ 4813338 = 19975400 := by
        calc
          (2 : ZMod 77013413) ^ 4813338 = (2 : ZMod 77013413) ^ (2406669 + 2406669) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 2406669 * (2 : ZMod 77013413) ^ 2406669 := by rw [pow_add]
          _ = 19975400 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 77013413) ^ 9626676 = 23649897 := by
        calc
          (2 : ZMod 77013413) ^ 9626676 = (2 : ZMod 77013413) ^ (4813338 + 4813338) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 4813338 * (2 : ZMod 77013413) ^ 4813338 := by rw [pow_add]
          _ = 23649897 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 77013413) ^ 19253353 = 29713618 := by
        calc
          (2 : ZMod 77013413) ^ 19253353 = (2 : ZMod 77013413) ^ (9626676 + 9626676 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 9626676 * (2 : ZMod 77013413) ^ 9626676) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 29713618 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 77013413) ^ 38506706 = 77013412 := by
        calc
          (2 : ZMod 77013413) ^ 38506706 = (2 : ZMod 77013413) ^ (19253353 + 19253353) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 19253353 * (2 : ZMod 77013413) ^ 19253353 := by rw [pow_add]
          _ = 77013412 := by rw [factor_0_24]; decide
      change (2 : ZMod 77013413) ^ 38506706 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 77013413) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 77013413) ^ 2 = 4 := by
        calc
          (2 : ZMod 77013413) ^ 2 = (2 : ZMod 77013413) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 1 * (2 : ZMod 77013413) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 77013413) ^ 5 = 32 := by
        calc
          (2 : ZMod 77013413) ^ 5 = (2 : ZMod 77013413) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 2 * (2 : ZMod 77013413) ^ 2) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 77013413) ^ 10 = 1024 := by
        calc
          (2 : ZMod 77013413) ^ 10 = (2 : ZMod 77013413) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 5 * (2 : ZMod 77013413) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 77013413) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 77013413) ^ 20 = (2 : ZMod 77013413) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 10 * (2 : ZMod 77013413) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 77013413) ^ 41 = 59274163 := by
        calc
          (2 : ZMod 77013413) ^ 41 = (2 : ZMod 77013413) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 20 * (2 : ZMod 77013413) ^ 20) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 59274163 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 77013413) ^ 83 = 52640396 := by
        calc
          (2 : ZMod 77013413) ^ 83 = (2 : ZMod 77013413) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 41 * (2 : ZMod 77013413) ^ 41) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 52640396 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 77013413) ^ 167 = 67678253 := by
        calc
          (2 : ZMod 77013413) ^ 167 = (2 : ZMod 77013413) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 83 * (2 : ZMod 77013413) ^ 83) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 67678253 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 77013413) ^ 335 = 60262879 := by
        calc
          (2 : ZMod 77013413) ^ 335 = (2 : ZMod 77013413) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 167 * (2 : ZMod 77013413) ^ 167) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 60262879 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 77013413) ^ 671 = 3303183 := by
        calc
          (2 : ZMod 77013413) ^ 671 = (2 : ZMod 77013413) ^ (335 + 335 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 335 * (2 : ZMod 77013413) ^ 335) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 3303183 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 77013413) ^ 1343 = 54249189 := by
        calc
          (2 : ZMod 77013413) ^ 1343 = (2 : ZMod 77013413) ^ (671 + 671 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 671 * (2 : ZMod 77013413) ^ 671) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 54249189 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 77013413) ^ 2686 = 38579038 := by
        calc
          (2 : ZMod 77013413) ^ 2686 = (2 : ZMod 77013413) ^ (1343 + 1343) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 1343 * (2 : ZMod 77013413) ^ 1343 := by rw [pow_add]
          _ = 38579038 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 77013413) ^ 5372 = 52693868 := by
        calc
          (2 : ZMod 77013413) ^ 5372 = (2 : ZMod 77013413) ^ (2686 + 2686) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 2686 * (2 : ZMod 77013413) ^ 2686 := by rw [pow_add]
          _ = 52693868 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 77013413) ^ 10744 = 53137273 := by
        calc
          (2 : ZMod 77013413) ^ 10744 = (2 : ZMod 77013413) ^ (5372 + 5372) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 5372 * (2 : ZMod 77013413) ^ 5372 := by rw [pow_add]
          _ = 53137273 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 77013413) ^ 21488 = 66362979 := by
        calc
          (2 : ZMod 77013413) ^ 21488 = (2 : ZMod 77013413) ^ (10744 + 10744) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 10744 * (2 : ZMod 77013413) ^ 10744 := by rw [pow_add]
          _ = 66362979 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 77013413) ^ 42976 = 74622090 := by
        calc
          (2 : ZMod 77013413) ^ 42976 = (2 : ZMod 77013413) ^ (21488 + 21488) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 21488 * (2 : ZMod 77013413) ^ 21488 := by rw [pow_add]
          _ = 74622090 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 77013413) ^ 85952 = 25748253 := by
        calc
          (2 : ZMod 77013413) ^ 85952 = (2 : ZMod 77013413) ^ (42976 + 42976) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 42976 * (2 : ZMod 77013413) ^ 42976 := by rw [pow_add]
          _ = 25748253 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 77013413) ^ 171904 = 25298880 := by
        calc
          (2 : ZMod 77013413) ^ 171904 = (2 : ZMod 77013413) ^ (85952 + 85952) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 85952 * (2 : ZMod 77013413) ^ 85952 := by rw [pow_add]
          _ = 25298880 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 77013413) ^ 343809 = 74394902 := by
        calc
          (2 : ZMod 77013413) ^ 343809 = (2 : ZMod 77013413) ^ (171904 + 171904 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 171904 * (2 : ZMod 77013413) ^ 171904) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 74394902 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 77013413) ^ 687619 = 37368636 := by
        calc
          (2 : ZMod 77013413) ^ 687619 = (2 : ZMod 77013413) ^ (343809 + 343809 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 343809 * (2 : ZMod 77013413) ^ 343809) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 37368636 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 77013413) ^ 1375239 = 24272979 := by
        calc
          (2 : ZMod 77013413) ^ 1375239 = (2 : ZMod 77013413) ^ (687619 + 687619 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 687619 * (2 : ZMod 77013413) ^ 687619) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 24272979 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 77013413) ^ 2750479 = 49504084 := by
        calc
          (2 : ZMod 77013413) ^ 2750479 = (2 : ZMod 77013413) ^ (1375239 + 1375239 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 1375239 * (2 : ZMod 77013413) ^ 1375239) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 49504084 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 77013413) ^ 5500958 = 43781888 := by
        calc
          (2 : ZMod 77013413) ^ 5500958 = (2 : ZMod 77013413) ^ (2750479 + 2750479) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 2750479 * (2 : ZMod 77013413) ^ 2750479 := by rw [pow_add]
          _ = 43781888 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 77013413) ^ 11001916 = 33045060 := by
        calc
          (2 : ZMod 77013413) ^ 11001916 = (2 : ZMod 77013413) ^ (5500958 + 5500958) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 5500958 * (2 : ZMod 77013413) ^ 5500958 := by rw [pow_add]
          _ = 33045060 := by rw [factor_1_22]; decide
      change (2 : ZMod 77013413) ^ 11001916 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (2 : ZMod 77013413) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 77013413) ^ 3 = 8 := by
        calc
          (2 : ZMod 77013413) ^ 3 = (2 : ZMod 77013413) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 1 * (2 : ZMod 77013413) ^ 1) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 77013413) ^ 7 = 128 := by
        calc
          (2 : ZMod 77013413) ^ 7 = (2 : ZMod 77013413) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = ((2 : ZMod 77013413) ^ 3 * (2 : ZMod 77013413) ^ 3) * (2 : ZMod 77013413) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 77013413) ^ 14 = 16384 := by
        calc
          (2 : ZMod 77013413) ^ 14 = (2 : ZMod 77013413) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 7 * (2 : ZMod 77013413) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 77013413) ^ 28 = 37395217 := by
        calc
          (2 : ZMod 77013413) ^ 28 = (2 : ZMod 77013413) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 77013413) ^ n) (by norm_num)
          _ = (2 : ZMod 77013413) ^ 14 * (2 : ZMod 77013413) ^ 14 := by rw [pow_add]
          _ = 37395217 := by rw [factor_2_3]; decide
      change (2 : ZMod 77013413) ^ 28 ≠ 1
      rw [factor_2_4]
      decide

#print axioms prime_lucas_77013413

end TotientTailPeriodKiller
end Erdos249257
