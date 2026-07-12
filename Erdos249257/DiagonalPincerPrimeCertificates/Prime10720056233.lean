import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_10720056233 : Nat.Prime 10720056233 := by
  apply lucas_primality 10720056233 (3 : ZMod 10720056233)
  ·
      have fermat_0 : (3 : ZMod 10720056233) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 10720056233) ^ 2 = 9 := by
        calc
          (3 : ZMod 10720056233) ^ 2 = (3 : ZMod 10720056233) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 1 * (3 : ZMod 10720056233) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 10720056233) ^ 4 = 81 := by
        calc
          (3 : ZMod 10720056233) ^ 4 = (3 : ZMod 10720056233) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 2 * (3 : ZMod 10720056233) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 10720056233) ^ 9 = 19683 := by
        calc
          (3 : ZMod 10720056233) ^ 9 = (3 : ZMod 10720056233) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 4 * (3 : ZMod 10720056233) ^ 4) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 10720056233) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 10720056233) ^ 19 = (3 : ZMod 10720056233) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 9 * (3 : ZMod 10720056233) ^ 9) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 10720056233) ^ 39 = 2823681693 := by
        calc
          (3 : ZMod 10720056233) ^ 39 = (3 : ZMod 10720056233) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 19 * (3 : ZMod 10720056233) ^ 19) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2823681693 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 10720056233) ^ 79 = 9161081778 := by
        calc
          (3 : ZMod 10720056233) ^ 79 = (3 : ZMod 10720056233) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 39 * (3 : ZMod 10720056233) ^ 39) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 9161081778 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 10720056233) ^ 159 = 1294024163 := by
        calc
          (3 : ZMod 10720056233) ^ 159 = (3 : ZMod 10720056233) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 79 * (3 : ZMod 10720056233) ^ 79) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 1294024163 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 10720056233) ^ 319 = 3774536709 := by
        calc
          (3 : ZMod 10720056233) ^ 319 = (3 : ZMod 10720056233) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 159 * (3 : ZMod 10720056233) ^ 159) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3774536709 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 10720056233) ^ 638 = 8866030682 := by
        calc
          (3 : ZMod 10720056233) ^ 638 = (3 : ZMod 10720056233) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 319 * (3 : ZMod 10720056233) ^ 319 := by rw [pow_add]
          _ = 8866030682 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 10720056233) ^ 1277 = 8759359608 := by
        calc
          (3 : ZMod 10720056233) ^ 1277 = (3 : ZMod 10720056233) ^ (638 + 638 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 638 * (3 : ZMod 10720056233) ^ 638) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 8759359608 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 10720056233) ^ 2555 = 3083694684 := by
        calc
          (3 : ZMod 10720056233) ^ 2555 = (3 : ZMod 10720056233) ^ (1277 + 1277 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1277 * (3 : ZMod 10720056233) ^ 1277) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3083694684 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 10720056233) ^ 5111 = 3495340026 := by
        calc
          (3 : ZMod 10720056233) ^ 5111 = (3 : ZMod 10720056233) ^ (2555 + 2555 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 2555 * (3 : ZMod 10720056233) ^ 2555) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3495340026 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 10720056233) ^ 10223 = 5537027029 := by
        calc
          (3 : ZMod 10720056233) ^ 10223 = (3 : ZMod 10720056233) ^ (5111 + 5111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 5111 * (3 : ZMod 10720056233) ^ 5111) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 5537027029 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 10720056233) ^ 20446 = 9129218641 := by
        calc
          (3 : ZMod 10720056233) ^ 20446 = (3 : ZMod 10720056233) ^ (10223 + 10223) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 10223 * (3 : ZMod 10720056233) ^ 10223 := by rw [pow_add]
          _ = 9129218641 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 10720056233) ^ 40893 = 2480259941 := by
        calc
          (3 : ZMod 10720056233) ^ 40893 = (3 : ZMod 10720056233) ^ (20446 + 20446 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 20446 * (3 : ZMod 10720056233) ^ 20446) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2480259941 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 10720056233) ^ 81787 = 8781255820 := by
        calc
          (3 : ZMod 10720056233) ^ 81787 = (3 : ZMod 10720056233) ^ (40893 + 40893 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 40893 * (3 : ZMod 10720056233) ^ 40893) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 8781255820 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 10720056233) ^ 163575 = 7162718179 := by
        calc
          (3 : ZMod 10720056233) ^ 163575 = (3 : ZMod 10720056233) ^ (81787 + 81787 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 81787 * (3 : ZMod 10720056233) ^ 81787) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 7162718179 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 10720056233) ^ 327150 = 8533260171 := by
        calc
          (3 : ZMod 10720056233) ^ 327150 = (3 : ZMod 10720056233) ^ (163575 + 163575) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 163575 * (3 : ZMod 10720056233) ^ 163575 := by rw [pow_add]
          _ = 8533260171 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 10720056233) ^ 654300 = 10212204455 := by
        calc
          (3 : ZMod 10720056233) ^ 654300 = (3 : ZMod 10720056233) ^ (327150 + 327150) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 327150 * (3 : ZMod 10720056233) ^ 327150 := by rw [pow_add]
          _ = 10212204455 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 10720056233) ^ 1308600 = 2870151138 := by
        calc
          (3 : ZMod 10720056233) ^ 1308600 = (3 : ZMod 10720056233) ^ (654300 + 654300) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 654300 * (3 : ZMod 10720056233) ^ 654300 := by rw [pow_add]
          _ = 2870151138 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 10720056233) ^ 2617201 = 10200401300 := by
        calc
          (3 : ZMod 10720056233) ^ 2617201 = (3 : ZMod 10720056233) ^ (1308600 + 1308600 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1308600 * (3 : ZMod 10720056233) ^ 1308600) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 10200401300 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 10720056233) ^ 5234402 = 9826106783 := by
        calc
          (3 : ZMod 10720056233) ^ 5234402 = (3 : ZMod 10720056233) ^ (2617201 + 2617201) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 2617201 * (3 : ZMod 10720056233) ^ 2617201 := by rw [pow_add]
          _ = 9826106783 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 10720056233) ^ 10468804 = 9886560158 := by
        calc
          (3 : ZMod 10720056233) ^ 10468804 = (3 : ZMod 10720056233) ^ (5234402 + 5234402) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 5234402 * (3 : ZMod 10720056233) ^ 5234402 := by rw [pow_add]
          _ = 9886560158 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 10720056233) ^ 20937609 = 2463777338 := by
        calc
          (3 : ZMod 10720056233) ^ 20937609 = (3 : ZMod 10720056233) ^ (10468804 + 10468804 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 10468804 * (3 : ZMod 10720056233) ^ 10468804) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2463777338 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 10720056233) ^ 41875219 = 2038785147 := by
        calc
          (3 : ZMod 10720056233) ^ 41875219 = (3 : ZMod 10720056233) ^ (20937609 + 20937609 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 20937609 * (3 : ZMod 10720056233) ^ 20937609) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2038785147 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 10720056233) ^ 83750439 = 5782088983 := by
        calc
          (3 : ZMod 10720056233) ^ 83750439 = (3 : ZMod 10720056233) ^ (41875219 + 41875219 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 41875219 * (3 : ZMod 10720056233) ^ 41875219) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 5782088983 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 10720056233) ^ 167500878 = 4965943570 := by
        calc
          (3 : ZMod 10720056233) ^ 167500878 = (3 : ZMod 10720056233) ^ (83750439 + 83750439) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 83750439 * (3 : ZMod 10720056233) ^ 83750439 := by rw [pow_add]
          _ = 4965943570 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 10720056233) ^ 335001757 = 1209432388 := by
        calc
          (3 : ZMod 10720056233) ^ 335001757 = (3 : ZMod 10720056233) ^ (167500878 + 167500878 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 167500878 * (3 : ZMod 10720056233) ^ 167500878) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 1209432388 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 10720056233) ^ 670003514 = 5881555434 := by
        calc
          (3 : ZMod 10720056233) ^ 670003514 = (3 : ZMod 10720056233) ^ (335001757 + 335001757) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 335001757 * (3 : ZMod 10720056233) ^ 335001757 := by rw [pow_add]
          _ = 5881555434 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 10720056233) ^ 1340007029 = 3761999248 := by
        calc
          (3 : ZMod 10720056233) ^ 1340007029 = (3 : ZMod 10720056233) ^ (670003514 + 670003514 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 670003514 * (3 : ZMod 10720056233) ^ 670003514) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3761999248 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 10720056233) ^ 2680014058 = 3040528629 := by
        calc
          (3 : ZMod 10720056233) ^ 2680014058 = (3 : ZMod 10720056233) ^ (1340007029 + 1340007029) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 1340007029 * (3 : ZMod 10720056233) ^ 1340007029 := by rw [pow_add]
          _ = 3040528629 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 10720056233) ^ 5360028116 = 10720056232 := by
        calc
          (3 : ZMod 10720056233) ^ 5360028116 = (3 : ZMod 10720056233) ^ (2680014058 + 2680014058) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 2680014058 * (3 : ZMod 10720056233) ^ 2680014058 := by rw [pow_add]
          _ = 10720056232 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 10720056233) ^ 10720056232 = 1 := by
        calc
          (3 : ZMod 10720056233) ^ 10720056232 = (3 : ZMod 10720056233) ^ (5360028116 + 5360028116) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 5360028116 * (3 : ZMod 10720056233) ^ 5360028116 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (83, 1), (601, 1), (26863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (83, 1), (601, 1), (26863, 1)] : List FactorBlock).map factorBlockValue).prod = 10720056233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 10720056233) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 10720056233) ^ 2 = 9 := by
        calc
          (3 : ZMod 10720056233) ^ 2 = (3 : ZMod 10720056233) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 1 * (3 : ZMod 10720056233) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 10720056233) ^ 4 = 81 := by
        calc
          (3 : ZMod 10720056233) ^ 4 = (3 : ZMod 10720056233) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 2 * (3 : ZMod 10720056233) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 10720056233) ^ 9 = 19683 := by
        calc
          (3 : ZMod 10720056233) ^ 9 = (3 : ZMod 10720056233) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 4 * (3 : ZMod 10720056233) ^ 4) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 10720056233) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 10720056233) ^ 19 = (3 : ZMod 10720056233) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 9 * (3 : ZMod 10720056233) ^ 9) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 10720056233) ^ 39 = 2823681693 := by
        calc
          (3 : ZMod 10720056233) ^ 39 = (3 : ZMod 10720056233) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 19 * (3 : ZMod 10720056233) ^ 19) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2823681693 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 10720056233) ^ 79 = 9161081778 := by
        calc
          (3 : ZMod 10720056233) ^ 79 = (3 : ZMod 10720056233) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 39 * (3 : ZMod 10720056233) ^ 39) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 9161081778 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 10720056233) ^ 159 = 1294024163 := by
        calc
          (3 : ZMod 10720056233) ^ 159 = (3 : ZMod 10720056233) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 79 * (3 : ZMod 10720056233) ^ 79) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 1294024163 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 10720056233) ^ 319 = 3774536709 := by
        calc
          (3 : ZMod 10720056233) ^ 319 = (3 : ZMod 10720056233) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 159 * (3 : ZMod 10720056233) ^ 159) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3774536709 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 10720056233) ^ 638 = 8866030682 := by
        calc
          (3 : ZMod 10720056233) ^ 638 = (3 : ZMod 10720056233) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 319 * (3 : ZMod 10720056233) ^ 319 := by rw [pow_add]
          _ = 8866030682 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 10720056233) ^ 1277 = 8759359608 := by
        calc
          (3 : ZMod 10720056233) ^ 1277 = (3 : ZMod 10720056233) ^ (638 + 638 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 638 * (3 : ZMod 10720056233) ^ 638) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 8759359608 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 10720056233) ^ 2555 = 3083694684 := by
        calc
          (3 : ZMod 10720056233) ^ 2555 = (3 : ZMod 10720056233) ^ (1277 + 1277 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1277 * (3 : ZMod 10720056233) ^ 1277) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3083694684 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 10720056233) ^ 5111 = 3495340026 := by
        calc
          (3 : ZMod 10720056233) ^ 5111 = (3 : ZMod 10720056233) ^ (2555 + 2555 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 2555 * (3 : ZMod 10720056233) ^ 2555) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3495340026 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 10720056233) ^ 10223 = 5537027029 := by
        calc
          (3 : ZMod 10720056233) ^ 10223 = (3 : ZMod 10720056233) ^ (5111 + 5111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 5111 * (3 : ZMod 10720056233) ^ 5111) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 5537027029 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 10720056233) ^ 20446 = 9129218641 := by
        calc
          (3 : ZMod 10720056233) ^ 20446 = (3 : ZMod 10720056233) ^ (10223 + 10223) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 10223 * (3 : ZMod 10720056233) ^ 10223 := by rw [pow_add]
          _ = 9129218641 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 10720056233) ^ 40893 = 2480259941 := by
        calc
          (3 : ZMod 10720056233) ^ 40893 = (3 : ZMod 10720056233) ^ (20446 + 20446 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 20446 * (3 : ZMod 10720056233) ^ 20446) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2480259941 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 10720056233) ^ 81787 = 8781255820 := by
        calc
          (3 : ZMod 10720056233) ^ 81787 = (3 : ZMod 10720056233) ^ (40893 + 40893 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 40893 * (3 : ZMod 10720056233) ^ 40893) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 8781255820 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 10720056233) ^ 163575 = 7162718179 := by
        calc
          (3 : ZMod 10720056233) ^ 163575 = (3 : ZMod 10720056233) ^ (81787 + 81787 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 81787 * (3 : ZMod 10720056233) ^ 81787) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 7162718179 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 10720056233) ^ 327150 = 8533260171 := by
        calc
          (3 : ZMod 10720056233) ^ 327150 = (3 : ZMod 10720056233) ^ (163575 + 163575) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 163575 * (3 : ZMod 10720056233) ^ 163575 := by rw [pow_add]
          _ = 8533260171 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 10720056233) ^ 654300 = 10212204455 := by
        calc
          (3 : ZMod 10720056233) ^ 654300 = (3 : ZMod 10720056233) ^ (327150 + 327150) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 327150 * (3 : ZMod 10720056233) ^ 327150 := by rw [pow_add]
          _ = 10212204455 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 10720056233) ^ 1308600 = 2870151138 := by
        calc
          (3 : ZMod 10720056233) ^ 1308600 = (3 : ZMod 10720056233) ^ (654300 + 654300) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 654300 * (3 : ZMod 10720056233) ^ 654300 := by rw [pow_add]
          _ = 2870151138 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 10720056233) ^ 2617201 = 10200401300 := by
        calc
          (3 : ZMod 10720056233) ^ 2617201 = (3 : ZMod 10720056233) ^ (1308600 + 1308600 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1308600 * (3 : ZMod 10720056233) ^ 1308600) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 10200401300 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 10720056233) ^ 5234402 = 9826106783 := by
        calc
          (3 : ZMod 10720056233) ^ 5234402 = (3 : ZMod 10720056233) ^ (2617201 + 2617201) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 2617201 * (3 : ZMod 10720056233) ^ 2617201 := by rw [pow_add]
          _ = 9826106783 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 10720056233) ^ 10468804 = 9886560158 := by
        calc
          (3 : ZMod 10720056233) ^ 10468804 = (3 : ZMod 10720056233) ^ (5234402 + 5234402) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 5234402 * (3 : ZMod 10720056233) ^ 5234402 := by rw [pow_add]
          _ = 9886560158 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 10720056233) ^ 20937609 = 2463777338 := by
        calc
          (3 : ZMod 10720056233) ^ 20937609 = (3 : ZMod 10720056233) ^ (10468804 + 10468804 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 10468804 * (3 : ZMod 10720056233) ^ 10468804) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2463777338 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 10720056233) ^ 41875219 = 2038785147 := by
        calc
          (3 : ZMod 10720056233) ^ 41875219 = (3 : ZMod 10720056233) ^ (20937609 + 20937609 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 20937609 * (3 : ZMod 10720056233) ^ 20937609) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2038785147 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 10720056233) ^ 83750439 = 5782088983 := by
        calc
          (3 : ZMod 10720056233) ^ 83750439 = (3 : ZMod 10720056233) ^ (41875219 + 41875219 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 41875219 * (3 : ZMod 10720056233) ^ 41875219) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 5782088983 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 10720056233) ^ 167500878 = 4965943570 := by
        calc
          (3 : ZMod 10720056233) ^ 167500878 = (3 : ZMod 10720056233) ^ (83750439 + 83750439) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 83750439 * (3 : ZMod 10720056233) ^ 83750439 := by rw [pow_add]
          _ = 4965943570 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 10720056233) ^ 335001757 = 1209432388 := by
        calc
          (3 : ZMod 10720056233) ^ 335001757 = (3 : ZMod 10720056233) ^ (167500878 + 167500878 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 167500878 * (3 : ZMod 10720056233) ^ 167500878) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 1209432388 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 10720056233) ^ 670003514 = 5881555434 := by
        calc
          (3 : ZMod 10720056233) ^ 670003514 = (3 : ZMod 10720056233) ^ (335001757 + 335001757) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 335001757 * (3 : ZMod 10720056233) ^ 335001757 := by rw [pow_add]
          _ = 5881555434 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 10720056233) ^ 1340007029 = 3761999248 := by
        calc
          (3 : ZMod 10720056233) ^ 1340007029 = (3 : ZMod 10720056233) ^ (670003514 + 670003514 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 670003514 * (3 : ZMod 10720056233) ^ 670003514) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3761999248 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 10720056233) ^ 2680014058 = 3040528629 := by
        calc
          (3 : ZMod 10720056233) ^ 2680014058 = (3 : ZMod 10720056233) ^ (1340007029 + 1340007029) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 1340007029 * (3 : ZMod 10720056233) ^ 1340007029 := by rw [pow_add]
          _ = 3040528629 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 10720056233) ^ 5360028116 = 10720056232 := by
        calc
          (3 : ZMod 10720056233) ^ 5360028116 = (3 : ZMod 10720056233) ^ (2680014058 + 2680014058) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 2680014058 * (3 : ZMod 10720056233) ^ 2680014058 := by rw [pow_add]
          _ = 10720056232 := by rw [factor_0_31]; decide
      change (3 : ZMod 10720056233) ^ 5360028116 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (3 : ZMod 10720056233) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 10720056233) ^ 3 = 27 := by
        calc
          (3 : ZMod 10720056233) ^ 3 = (3 : ZMod 10720056233) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1 * (3 : ZMod 10720056233) ^ 1) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 10720056233) ^ 7 = 2187 := by
        calc
          (3 : ZMod 10720056233) ^ 7 = (3 : ZMod 10720056233) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 3 * (3 : ZMod 10720056233) ^ 3) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 10720056233) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 10720056233) ^ 15 = (3 : ZMod 10720056233) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 7 * (3 : ZMod 10720056233) ^ 7) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 10720056233) ^ 30 = 1732083651 := by
        calc
          (3 : ZMod 10720056233) ^ 30 = (3 : ZMod 10720056233) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 15 * (3 : ZMod 10720056233) ^ 15 := by rw [pow_add]
          _ = 1732083651 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 10720056233) ^ 61 = 4820661361 := by
        calc
          (3 : ZMod 10720056233) ^ 61 = (3 : ZMod 10720056233) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 30 * (3 : ZMod 10720056233) ^ 30) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 4820661361 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 10720056233) ^ 123 = 10291452756 := by
        calc
          (3 : ZMod 10720056233) ^ 123 = (3 : ZMod 10720056233) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 61 * (3 : ZMod 10720056233) ^ 61) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 10291452756 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 10720056233) ^ 246 = 9357061026 := by
        calc
          (3 : ZMod 10720056233) ^ 246 = (3 : ZMod 10720056233) ^ (123 + 123) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 123 * (3 : ZMod 10720056233) ^ 123 := by rw [pow_add]
          _ = 9357061026 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 10720056233) ^ 492 = 1602456822 := by
        calc
          (3 : ZMod 10720056233) ^ 492 = (3 : ZMod 10720056233) ^ (246 + 246) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 246 * (3 : ZMod 10720056233) ^ 246 := by rw [pow_add]
          _ = 1602456822 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 10720056233) ^ 985 = 1511234275 := by
        calc
          (3 : ZMod 10720056233) ^ 985 = (3 : ZMod 10720056233) ^ (492 + 492 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 492 * (3 : ZMod 10720056233) ^ 492) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 1511234275 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 10720056233) ^ 1970 = 6708281670 := by
        calc
          (3 : ZMod 10720056233) ^ 1970 = (3 : ZMod 10720056233) ^ (985 + 985) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 985 * (3 : ZMod 10720056233) ^ 985 := by rw [pow_add]
          _ = 6708281670 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 10720056233) ^ 3941 = 6960157665 := by
        calc
          (3 : ZMod 10720056233) ^ 3941 = (3 : ZMod 10720056233) ^ (1970 + 1970 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1970 * (3 : ZMod 10720056233) ^ 1970) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 6960157665 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 10720056233) ^ 7883 = 3587406005 := by
        calc
          (3 : ZMod 10720056233) ^ 7883 = (3 : ZMod 10720056233) ^ (3941 + 3941 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 3941 * (3 : ZMod 10720056233) ^ 3941) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3587406005 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 10720056233) ^ 15766 = 7748571181 := by
        calc
          (3 : ZMod 10720056233) ^ 15766 = (3 : ZMod 10720056233) ^ (7883 + 7883) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 7883 * (3 : ZMod 10720056233) ^ 7883 := by rw [pow_add]
          _ = 7748571181 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 10720056233) ^ 31532 = 3406904140 := by
        calc
          (3 : ZMod 10720056233) ^ 31532 = (3 : ZMod 10720056233) ^ (15766 + 15766) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 15766 * (3 : ZMod 10720056233) ^ 15766 := by rw [pow_add]
          _ = 3406904140 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 10720056233) ^ 63065 = 728059901 := by
        calc
          (3 : ZMod 10720056233) ^ 63065 = (3 : ZMod 10720056233) ^ (31532 + 31532 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 31532 * (3 : ZMod 10720056233) ^ 31532) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 728059901 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 10720056233) ^ 126130 = 7868860895 := by
        calc
          (3 : ZMod 10720056233) ^ 126130 = (3 : ZMod 10720056233) ^ (63065 + 63065) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 63065 * (3 : ZMod 10720056233) ^ 63065 := by rw [pow_add]
          _ = 7868860895 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 10720056233) ^ 252260 = 8075260221 := by
        calc
          (3 : ZMod 10720056233) ^ 252260 = (3 : ZMod 10720056233) ^ (126130 + 126130) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 126130 * (3 : ZMod 10720056233) ^ 126130 := by rw [pow_add]
          _ = 8075260221 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 10720056233) ^ 504520 = 4965533641 := by
        calc
          (3 : ZMod 10720056233) ^ 504520 = (3 : ZMod 10720056233) ^ (252260 + 252260) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 252260 * (3 : ZMod 10720056233) ^ 252260 := by rw [pow_add]
          _ = 4965533641 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 10720056233) ^ 1009041 = 6272098590 := by
        calc
          (3 : ZMod 10720056233) ^ 1009041 = (3 : ZMod 10720056233) ^ (504520 + 504520 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 504520 * (3 : ZMod 10720056233) ^ 504520) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 6272098590 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 10720056233) ^ 2018082 = 9329775325 := by
        calc
          (3 : ZMod 10720056233) ^ 2018082 = (3 : ZMod 10720056233) ^ (1009041 + 1009041) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 1009041 * (3 : ZMod 10720056233) ^ 1009041 := by rw [pow_add]
          _ = 9329775325 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 10720056233) ^ 4036165 = 7994868143 := by
        calc
          (3 : ZMod 10720056233) ^ 4036165 = (3 : ZMod 10720056233) ^ (2018082 + 2018082 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 2018082 * (3 : ZMod 10720056233) ^ 2018082) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 7994868143 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 10720056233) ^ 8072331 = 8749788559 := by
        calc
          (3 : ZMod 10720056233) ^ 8072331 = (3 : ZMod 10720056233) ^ (4036165 + 4036165 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 4036165 * (3 : ZMod 10720056233) ^ 4036165) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 8749788559 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 10720056233) ^ 16144663 = 1661224869 := by
        calc
          (3 : ZMod 10720056233) ^ 16144663 = (3 : ZMod 10720056233) ^ (8072331 + 8072331 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 8072331 * (3 : ZMod 10720056233) ^ 8072331) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 1661224869 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 10720056233) ^ 32289326 = 1461958485 := by
        calc
          (3 : ZMod 10720056233) ^ 32289326 = (3 : ZMod 10720056233) ^ (16144663 + 16144663) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 16144663 * (3 : ZMod 10720056233) ^ 16144663 := by rw [pow_add]
          _ = 1461958485 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 10720056233) ^ 64578652 = 4989344546 := by
        calc
          (3 : ZMod 10720056233) ^ 64578652 = (3 : ZMod 10720056233) ^ (32289326 + 32289326) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 32289326 * (3 : ZMod 10720056233) ^ 32289326 := by rw [pow_add]
          _ = 4989344546 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 10720056233) ^ 129157304 = 2781733807 := by
        calc
          (3 : ZMod 10720056233) ^ 129157304 = (3 : ZMod 10720056233) ^ (64578652 + 64578652) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 64578652 * (3 : ZMod 10720056233) ^ 64578652 := by rw [pow_add]
          _ = 2781733807 := by rw [factor_1_25]; decide
      change (3 : ZMod 10720056233) ^ 129157304 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (3 : ZMod 10720056233) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 10720056233) ^ 2 = 9 := by
        calc
          (3 : ZMod 10720056233) ^ 2 = (3 : ZMod 10720056233) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 1 * (3 : ZMod 10720056233) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 10720056233) ^ 4 = 81 := by
        calc
          (3 : ZMod 10720056233) ^ 4 = (3 : ZMod 10720056233) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 2 * (3 : ZMod 10720056233) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 10720056233) ^ 8 = 6561 := by
        calc
          (3 : ZMod 10720056233) ^ 8 = (3 : ZMod 10720056233) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 4 * (3 : ZMod 10720056233) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 10720056233) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 10720056233) ^ 17 = (3 : ZMod 10720056233) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 8 * (3 : ZMod 10720056233) ^ 8) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 10720056233) ^ 34 = 938044702 := by
        calc
          (3 : ZMod 10720056233) ^ 34 = (3 : ZMod 10720056233) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 17 * (3 : ZMod 10720056233) ^ 17 := by rw [pow_add]
          _ = 938044702 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 10720056233) ^ 68 = 4971119468 := by
        calc
          (3 : ZMod 10720056233) ^ 68 = (3 : ZMod 10720056233) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 34 * (3 : ZMod 10720056233) ^ 34 := by rw [pow_add]
          _ = 4971119468 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 10720056233) ^ 136 = 6883255281 := by
        calc
          (3 : ZMod 10720056233) ^ 136 = (3 : ZMod 10720056233) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 68 * (3 : ZMod 10720056233) ^ 68 := by rw [pow_add]
          _ = 6883255281 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 10720056233) ^ 272 = 266944132 := by
        calc
          (3 : ZMod 10720056233) ^ 272 = (3 : ZMod 10720056233) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 136 * (3 : ZMod 10720056233) ^ 136 := by rw [pow_add]
          _ = 266944132 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 10720056233) ^ 544 = 7813018349 := by
        calc
          (3 : ZMod 10720056233) ^ 544 = (3 : ZMod 10720056233) ^ (272 + 272) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 272 * (3 : ZMod 10720056233) ^ 272 := by rw [pow_add]
          _ = 7813018349 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 10720056233) ^ 1088 = 111510963 := by
        calc
          (3 : ZMod 10720056233) ^ 1088 = (3 : ZMod 10720056233) ^ (544 + 544) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 544 * (3 : ZMod 10720056233) ^ 544 := by rw [pow_add]
          _ = 111510963 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 10720056233) ^ 2177 = 4125719387 := by
        calc
          (3 : ZMod 10720056233) ^ 2177 = (3 : ZMod 10720056233) ^ (1088 + 1088 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1088 * (3 : ZMod 10720056233) ^ 1088) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 4125719387 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 10720056233) ^ 4354 = 4011741670 := by
        calc
          (3 : ZMod 10720056233) ^ 4354 = (3 : ZMod 10720056233) ^ (2177 + 2177) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 2177 * (3 : ZMod 10720056233) ^ 2177 := by rw [pow_add]
          _ = 4011741670 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 10720056233) ^ 8709 = 5595002139 := by
        calc
          (3 : ZMod 10720056233) ^ 8709 = (3 : ZMod 10720056233) ^ (4354 + 4354 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 4354 * (3 : ZMod 10720056233) ^ 4354) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 5595002139 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 10720056233) ^ 17418 = 7266304821 := by
        calc
          (3 : ZMod 10720056233) ^ 17418 = (3 : ZMod 10720056233) ^ (8709 + 8709) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 8709 * (3 : ZMod 10720056233) ^ 8709 := by rw [pow_add]
          _ = 7266304821 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 10720056233) ^ 34837 = 7993402065 := by
        calc
          (3 : ZMod 10720056233) ^ 34837 = (3 : ZMod 10720056233) ^ (17418 + 17418 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 17418 * (3 : ZMod 10720056233) ^ 17418) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 7993402065 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 10720056233) ^ 69675 = 4310317560 := by
        calc
          (3 : ZMod 10720056233) ^ 69675 = (3 : ZMod 10720056233) ^ (34837 + 34837 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 34837 * (3 : ZMod 10720056233) ^ 34837) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 4310317560 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 10720056233) ^ 139351 = 9023823152 := by
        calc
          (3 : ZMod 10720056233) ^ 139351 = (3 : ZMod 10720056233) ^ (69675 + 69675 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 69675 * (3 : ZMod 10720056233) ^ 69675) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 9023823152 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 10720056233) ^ 278703 = 7552689219 := by
        calc
          (3 : ZMod 10720056233) ^ 278703 = (3 : ZMod 10720056233) ^ (139351 + 139351 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 139351 * (3 : ZMod 10720056233) ^ 139351) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 7552689219 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 10720056233) ^ 557407 = 10020217285 := by
        calc
          (3 : ZMod 10720056233) ^ 557407 = (3 : ZMod 10720056233) ^ (278703 + 278703 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 278703 * (3 : ZMod 10720056233) ^ 278703) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 10020217285 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 10720056233) ^ 1114814 = 782156099 := by
        calc
          (3 : ZMod 10720056233) ^ 1114814 = (3 : ZMod 10720056233) ^ (557407 + 557407) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 557407 * (3 : ZMod 10720056233) ^ 557407 := by rw [pow_add]
          _ = 782156099 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 10720056233) ^ 2229629 = 10197254829 := by
        calc
          (3 : ZMod 10720056233) ^ 2229629 = (3 : ZMod 10720056233) ^ (1114814 + 1114814 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1114814 * (3 : ZMod 10720056233) ^ 1114814) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 10197254829 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 10720056233) ^ 4459258 = 9973407568 := by
        calc
          (3 : ZMod 10720056233) ^ 4459258 = (3 : ZMod 10720056233) ^ (2229629 + 2229629) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 2229629 * (3 : ZMod 10720056233) ^ 2229629 := by rw [pow_add]
          _ = 9973407568 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 10720056233) ^ 8918516 = 453616476 := by
        calc
          (3 : ZMod 10720056233) ^ 8918516 = (3 : ZMod 10720056233) ^ (4459258 + 4459258) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 4459258 * (3 : ZMod 10720056233) ^ 4459258 := by rw [pow_add]
          _ = 453616476 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 10720056233) ^ 17837032 = 8405005398 := by
        calc
          (3 : ZMod 10720056233) ^ 17837032 = (3 : ZMod 10720056233) ^ (8918516 + 8918516) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 8918516 * (3 : ZMod 10720056233) ^ 8918516 := by rw [pow_add]
          _ = 8405005398 := by rw [factor_2_23]; decide
      change (3 : ZMod 10720056233) ^ 17837032 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (3 : ZMod 10720056233) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 10720056233) ^ 3 = 27 := by
        calc
          (3 : ZMod 10720056233) ^ 3 = (3 : ZMod 10720056233) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1 * (3 : ZMod 10720056233) ^ 1) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 10720056233) ^ 6 = 729 := by
        calc
          (3 : ZMod 10720056233) ^ 6 = (3 : ZMod 10720056233) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 3 * (3 : ZMod 10720056233) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 10720056233) ^ 12 = 531441 := by
        calc
          (3 : ZMod 10720056233) ^ 12 = (3 : ZMod 10720056233) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 6 * (3 : ZMod 10720056233) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 10720056233) ^ 24 = 3708074423 := by
        calc
          (3 : ZMod 10720056233) ^ 24 = (3 : ZMod 10720056233) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 12 * (3 : ZMod 10720056233) ^ 12 := by rw [pow_add]
          _ = 3708074423 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 10720056233) ^ 48 = 5755251447 := by
        calc
          (3 : ZMod 10720056233) ^ 48 = (3 : ZMod 10720056233) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 24 * (3 : ZMod 10720056233) ^ 24 := by rw [pow_add]
          _ = 5755251447 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 10720056233) ^ 97 = 10368675806 := by
        calc
          (3 : ZMod 10720056233) ^ 97 = (3 : ZMod 10720056233) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 48 * (3 : ZMod 10720056233) ^ 48) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 10368675806 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 10720056233) ^ 194 = 10415405994 := by
        calc
          (3 : ZMod 10720056233) ^ 194 = (3 : ZMod 10720056233) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 97 * (3 : ZMod 10720056233) ^ 97 := by rw [pow_add]
          _ = 10415405994 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 10720056233) ^ 389 = 3491355065 := by
        calc
          (3 : ZMod 10720056233) ^ 389 = (3 : ZMod 10720056233) ^ (194 + 194 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 194 * (3 : ZMod 10720056233) ^ 194) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3491355065 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 10720056233) ^ 779 = 8345854982 := by
        calc
          (3 : ZMod 10720056233) ^ 779 = (3 : ZMod 10720056233) ^ (389 + 389 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 389 * (3 : ZMod 10720056233) ^ 389) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 8345854982 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 10720056233) ^ 1558 = 1993004662 := by
        calc
          (3 : ZMod 10720056233) ^ 1558 = (3 : ZMod 10720056233) ^ (779 + 779) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 779 * (3 : ZMod 10720056233) ^ 779 := by rw [pow_add]
          _ = 1993004662 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 10720056233) ^ 3117 = 3649229414 := by
        calc
          (3 : ZMod 10720056233) ^ 3117 = (3 : ZMod 10720056233) ^ (1558 + 1558 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 1558 * (3 : ZMod 10720056233) ^ 1558) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 3649229414 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 10720056233) ^ 6235 = 2358092770 := by
        calc
          (3 : ZMod 10720056233) ^ 6235 = (3 : ZMod 10720056233) ^ (3117 + 3117 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 3117 * (3 : ZMod 10720056233) ^ 3117) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 2358092770 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 10720056233) ^ 12470 = 6980882202 := by
        calc
          (3 : ZMod 10720056233) ^ 12470 = (3 : ZMod 10720056233) ^ (6235 + 6235) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 6235 * (3 : ZMod 10720056233) ^ 6235 := by rw [pow_add]
          _ = 6980882202 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 10720056233) ^ 24941 = 6522657242 := by
        calc
          (3 : ZMod 10720056233) ^ 24941 = (3 : ZMod 10720056233) ^ (12470 + 12470 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 12470 * (3 : ZMod 10720056233) ^ 12470) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 6522657242 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 10720056233) ^ 49883 = 1096132737 := by
        calc
          (3 : ZMod 10720056233) ^ 49883 = (3 : ZMod 10720056233) ^ (24941 + 24941 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = ((3 : ZMod 10720056233) ^ 24941 * (3 : ZMod 10720056233) ^ 24941) * (3 : ZMod 10720056233) := by rw [pow_succ, pow_add]
          _ = 1096132737 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 10720056233) ^ 99766 = 8592388531 := by
        calc
          (3 : ZMod 10720056233) ^ 99766 = (3 : ZMod 10720056233) ^ (49883 + 49883) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 49883 * (3 : ZMod 10720056233) ^ 49883 := by rw [pow_add]
          _ = 8592388531 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 10720056233) ^ 199532 = 4954561520 := by
        calc
          (3 : ZMod 10720056233) ^ 199532 = (3 : ZMod 10720056233) ^ (99766 + 99766) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 99766 * (3 : ZMod 10720056233) ^ 99766 := by rw [pow_add]
          _ = 4954561520 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 10720056233) ^ 399064 = 606023599 := by
        calc
          (3 : ZMod 10720056233) ^ 399064 = (3 : ZMod 10720056233) ^ (199532 + 199532) :=
            congrArg (fun n : ℕ => (3 : ZMod 10720056233) ^ n) (by norm_num)
          _ = (3 : ZMod 10720056233) ^ 199532 * (3 : ZMod 10720056233) ^ 199532 := by rw [pow_add]
          _ = 606023599 := by rw [factor_3_17]; decide
      change (3 : ZMod 10720056233) ^ 399064 ≠ 1
      rw [factor_3_18]
      decide

#print axioms prime_lucas_10720056233

end TotientTailPeriodKiller
end Erdos249257
