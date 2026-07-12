import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_169653067 : Nat.Prime 169653067 := by
  apply lucas_primality 169653067 (3 : ZMod 169653067)
  ·
      have fermat_0 : (3 : ZMod 169653067) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 169653067) ^ 2 = 9 := by
        calc
          (3 : ZMod 169653067) ^ 2 = (3 : ZMod 169653067) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 1 * (3 : ZMod 169653067) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 169653067) ^ 5 = 243 := by
        calc
          (3 : ZMod 169653067) ^ 5 = (3 : ZMod 169653067) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 2 * (3 : ZMod 169653067) ^ 2) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 169653067) ^ 10 = 59049 := by
        calc
          (3 : ZMod 169653067) ^ 10 = (3 : ZMod 169653067) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 5 * (3 : ZMod 169653067) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 169653067) ^ 20 = 93723061 := by
        calc
          (3 : ZMod 169653067) ^ 20 = (3 : ZMod 169653067) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 10 * (3 : ZMod 169653067) ^ 10 := by rw [pow_add]
          _ = 93723061 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 169653067) ^ 40 = 168277080 := by
        calc
          (3 : ZMod 169653067) ^ 40 = (3 : ZMod 169653067) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 20 * (3 : ZMod 169653067) ^ 20 := by rw [pow_add]
          _ = 168277080 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 169653067) ^ 80 = 11996449 := by
        calc
          (3 : ZMod 169653067) ^ 80 = (3 : ZMod 169653067) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 40 * (3 : ZMod 169653067) ^ 40 := by rw [pow_add]
          _ = 11996449 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 169653067) ^ 161 = 43824781 := by
        calc
          (3 : ZMod 169653067) ^ 161 = (3 : ZMod 169653067) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 80 * (3 : ZMod 169653067) ^ 80) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 43824781 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 169653067) ^ 323 = 144453599 := by
        calc
          (3 : ZMod 169653067) ^ 323 = (3 : ZMod 169653067) ^ (161 + 161 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 161 * (3 : ZMod 169653067) ^ 161) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 144453599 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 169653067) ^ 647 = 13860995 := by
        calc
          (3 : ZMod 169653067) ^ 647 = (3 : ZMod 169653067) ^ (323 + 323 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 323 * (3 : ZMod 169653067) ^ 323) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 13860995 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 169653067) ^ 1294 = 3951468 := by
        calc
          (3 : ZMod 169653067) ^ 1294 = (3 : ZMod 169653067) ^ (647 + 647) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 647 * (3 : ZMod 169653067) ^ 647 := by rw [pow_add]
          _ = 3951468 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 169653067) ^ 2588 = 79333679 := by
        calc
          (3 : ZMod 169653067) ^ 2588 = (3 : ZMod 169653067) ^ (1294 + 1294) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 1294 * (3 : ZMod 169653067) ^ 1294 := by rw [pow_add]
          _ = 79333679 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 169653067) ^ 5177 = 156690069 := by
        calc
          (3 : ZMod 169653067) ^ 5177 = (3 : ZMod 169653067) ^ (2588 + 2588 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 2588 * (3 : ZMod 169653067) ^ 2588) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 156690069 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 169653067) ^ 10354 = 159774375 := by
        calc
          (3 : ZMod 169653067) ^ 10354 = (3 : ZMod 169653067) ^ (5177 + 5177) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 5177 * (3 : ZMod 169653067) ^ 5177 := by rw [pow_add]
          _ = 159774375 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 169653067) ^ 20709 = 119456568 := by
        calc
          (3 : ZMod 169653067) ^ 20709 = (3 : ZMod 169653067) ^ (10354 + 10354 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 10354 * (3 : ZMod 169653067) ^ 10354) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 119456568 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 169653067) ^ 41419 = 89257663 := by
        calc
          (3 : ZMod 169653067) ^ 41419 = (3 : ZMod 169653067) ^ (20709 + 20709 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 20709 * (3 : ZMod 169653067) ^ 20709) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 89257663 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 169653067) ^ 82838 = 153349792 := by
        calc
          (3 : ZMod 169653067) ^ 82838 = (3 : ZMod 169653067) ^ (41419 + 41419) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 41419 * (3 : ZMod 169653067) ^ 41419 := by rw [pow_add]
          _ = 153349792 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 169653067) ^ 165676 = 128085256 := by
        calc
          (3 : ZMod 169653067) ^ 165676 = (3 : ZMod 169653067) ^ (82838 + 82838) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 82838 * (3 : ZMod 169653067) ^ 82838 := by rw [pow_add]
          _ = 128085256 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 169653067) ^ 331353 = 45731961 := by
        calc
          (3 : ZMod 169653067) ^ 331353 = (3 : ZMod 169653067) ^ (165676 + 165676 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 165676 * (3 : ZMod 169653067) ^ 165676) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 45731961 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 169653067) ^ 662707 = 146428447 := by
        calc
          (3 : ZMod 169653067) ^ 662707 = (3 : ZMod 169653067) ^ (331353 + 331353 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 331353 * (3 : ZMod 169653067) ^ 331353) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 146428447 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 169653067) ^ 1325414 = 58292357 := by
        calc
          (3 : ZMod 169653067) ^ 1325414 = (3 : ZMod 169653067) ^ (662707 + 662707) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 662707 * (3 : ZMod 169653067) ^ 662707 := by rw [pow_add]
          _ = 58292357 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 169653067) ^ 2650829 = 54913510 := by
        calc
          (3 : ZMod 169653067) ^ 2650829 = (3 : ZMod 169653067) ^ (1325414 + 1325414 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 1325414 * (3 : ZMod 169653067) ^ 1325414) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 54913510 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 169653067) ^ 5301658 = 61067543 := by
        calc
          (3 : ZMod 169653067) ^ 5301658 = (3 : ZMod 169653067) ^ (2650829 + 2650829) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 2650829 * (3 : ZMod 169653067) ^ 2650829 := by rw [pow_add]
          _ = 61067543 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 169653067) ^ 10603316 = 138061118 := by
        calc
          (3 : ZMod 169653067) ^ 10603316 = (3 : ZMod 169653067) ^ (5301658 + 5301658) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 5301658 * (3 : ZMod 169653067) ^ 5301658 := by rw [pow_add]
          _ = 138061118 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 169653067) ^ 21206633 = 16435841 := by
        calc
          (3 : ZMod 169653067) ^ 21206633 = (3 : ZMod 169653067) ^ (10603316 + 10603316 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 10603316 * (3 : ZMod 169653067) ^ 10603316) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 16435841 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 169653067) ^ 42413266 = 156976918 := by
        calc
          (3 : ZMod 169653067) ^ 42413266 = (3 : ZMod 169653067) ^ (21206633 + 21206633) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 21206633 * (3 : ZMod 169653067) ^ 21206633 := by rw [pow_add]
          _ = 156976918 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 169653067) ^ 84826533 = 169653066 := by
        calc
          (3 : ZMod 169653067) ^ 84826533 = (3 : ZMod 169653067) ^ (42413266 + 42413266 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 42413266 * (3 : ZMod 169653067) ^ 42413266) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 169653066 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 169653067) ^ 169653066 = 1 := by
        calc
          (3 : ZMod 169653067) ^ 169653066 = (3 : ZMod 169653067) ^ (84826533 + 84826533) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 84826533 * (3 : ZMod 169653067) ^ 84826533 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (37, 1), (69473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (37, 1), (69473, 1)] : List FactorBlock).map factorBlockValue).prod = 169653067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 169653067) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 169653067) ^ 2 = 9 := by
        calc
          (3 : ZMod 169653067) ^ 2 = (3 : ZMod 169653067) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 1 * (3 : ZMod 169653067) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 169653067) ^ 5 = 243 := by
        calc
          (3 : ZMod 169653067) ^ 5 = (3 : ZMod 169653067) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 2 * (3 : ZMod 169653067) ^ 2) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 169653067) ^ 10 = 59049 := by
        calc
          (3 : ZMod 169653067) ^ 10 = (3 : ZMod 169653067) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 5 * (3 : ZMod 169653067) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 169653067) ^ 20 = 93723061 := by
        calc
          (3 : ZMod 169653067) ^ 20 = (3 : ZMod 169653067) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 10 * (3 : ZMod 169653067) ^ 10 := by rw [pow_add]
          _ = 93723061 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 169653067) ^ 40 = 168277080 := by
        calc
          (3 : ZMod 169653067) ^ 40 = (3 : ZMod 169653067) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 20 * (3 : ZMod 169653067) ^ 20 := by rw [pow_add]
          _ = 168277080 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 169653067) ^ 80 = 11996449 := by
        calc
          (3 : ZMod 169653067) ^ 80 = (3 : ZMod 169653067) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 40 * (3 : ZMod 169653067) ^ 40 := by rw [pow_add]
          _ = 11996449 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 169653067) ^ 161 = 43824781 := by
        calc
          (3 : ZMod 169653067) ^ 161 = (3 : ZMod 169653067) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 80 * (3 : ZMod 169653067) ^ 80) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 43824781 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 169653067) ^ 323 = 144453599 := by
        calc
          (3 : ZMod 169653067) ^ 323 = (3 : ZMod 169653067) ^ (161 + 161 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 161 * (3 : ZMod 169653067) ^ 161) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 144453599 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 169653067) ^ 647 = 13860995 := by
        calc
          (3 : ZMod 169653067) ^ 647 = (3 : ZMod 169653067) ^ (323 + 323 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 323 * (3 : ZMod 169653067) ^ 323) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 13860995 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 169653067) ^ 1294 = 3951468 := by
        calc
          (3 : ZMod 169653067) ^ 1294 = (3 : ZMod 169653067) ^ (647 + 647) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 647 * (3 : ZMod 169653067) ^ 647 := by rw [pow_add]
          _ = 3951468 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 169653067) ^ 2588 = 79333679 := by
        calc
          (3 : ZMod 169653067) ^ 2588 = (3 : ZMod 169653067) ^ (1294 + 1294) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 1294 * (3 : ZMod 169653067) ^ 1294 := by rw [pow_add]
          _ = 79333679 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 169653067) ^ 5177 = 156690069 := by
        calc
          (3 : ZMod 169653067) ^ 5177 = (3 : ZMod 169653067) ^ (2588 + 2588 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 2588 * (3 : ZMod 169653067) ^ 2588) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 156690069 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 169653067) ^ 10354 = 159774375 := by
        calc
          (3 : ZMod 169653067) ^ 10354 = (3 : ZMod 169653067) ^ (5177 + 5177) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 5177 * (3 : ZMod 169653067) ^ 5177 := by rw [pow_add]
          _ = 159774375 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 169653067) ^ 20709 = 119456568 := by
        calc
          (3 : ZMod 169653067) ^ 20709 = (3 : ZMod 169653067) ^ (10354 + 10354 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 10354 * (3 : ZMod 169653067) ^ 10354) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 119456568 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 169653067) ^ 41419 = 89257663 := by
        calc
          (3 : ZMod 169653067) ^ 41419 = (3 : ZMod 169653067) ^ (20709 + 20709 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 20709 * (3 : ZMod 169653067) ^ 20709) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 89257663 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 169653067) ^ 82838 = 153349792 := by
        calc
          (3 : ZMod 169653067) ^ 82838 = (3 : ZMod 169653067) ^ (41419 + 41419) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 41419 * (3 : ZMod 169653067) ^ 41419 := by rw [pow_add]
          _ = 153349792 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 169653067) ^ 165676 = 128085256 := by
        calc
          (3 : ZMod 169653067) ^ 165676 = (3 : ZMod 169653067) ^ (82838 + 82838) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 82838 * (3 : ZMod 169653067) ^ 82838 := by rw [pow_add]
          _ = 128085256 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 169653067) ^ 331353 = 45731961 := by
        calc
          (3 : ZMod 169653067) ^ 331353 = (3 : ZMod 169653067) ^ (165676 + 165676 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 165676 * (3 : ZMod 169653067) ^ 165676) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 45731961 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 169653067) ^ 662707 = 146428447 := by
        calc
          (3 : ZMod 169653067) ^ 662707 = (3 : ZMod 169653067) ^ (331353 + 331353 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 331353 * (3 : ZMod 169653067) ^ 331353) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 146428447 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 169653067) ^ 1325414 = 58292357 := by
        calc
          (3 : ZMod 169653067) ^ 1325414 = (3 : ZMod 169653067) ^ (662707 + 662707) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 662707 * (3 : ZMod 169653067) ^ 662707 := by rw [pow_add]
          _ = 58292357 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 169653067) ^ 2650829 = 54913510 := by
        calc
          (3 : ZMod 169653067) ^ 2650829 = (3 : ZMod 169653067) ^ (1325414 + 1325414 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 1325414 * (3 : ZMod 169653067) ^ 1325414) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 54913510 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 169653067) ^ 5301658 = 61067543 := by
        calc
          (3 : ZMod 169653067) ^ 5301658 = (3 : ZMod 169653067) ^ (2650829 + 2650829) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 2650829 * (3 : ZMod 169653067) ^ 2650829 := by rw [pow_add]
          _ = 61067543 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 169653067) ^ 10603316 = 138061118 := by
        calc
          (3 : ZMod 169653067) ^ 10603316 = (3 : ZMod 169653067) ^ (5301658 + 5301658) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 5301658 * (3 : ZMod 169653067) ^ 5301658 := by rw [pow_add]
          _ = 138061118 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 169653067) ^ 21206633 = 16435841 := by
        calc
          (3 : ZMod 169653067) ^ 21206633 = (3 : ZMod 169653067) ^ (10603316 + 10603316 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 10603316 * (3 : ZMod 169653067) ^ 10603316) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 16435841 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 169653067) ^ 42413266 = 156976918 := by
        calc
          (3 : ZMod 169653067) ^ 42413266 = (3 : ZMod 169653067) ^ (21206633 + 21206633) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 21206633 * (3 : ZMod 169653067) ^ 21206633 := by rw [pow_add]
          _ = 156976918 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 169653067) ^ 84826533 = 169653066 := by
        calc
          (3 : ZMod 169653067) ^ 84826533 = (3 : ZMod 169653067) ^ (42413266 + 42413266 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 42413266 * (3 : ZMod 169653067) ^ 42413266) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 169653066 := by rw [factor_0_25]; decide
      change (3 : ZMod 169653067) ^ 84826533 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (3 : ZMod 169653067) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 169653067) ^ 3 = 27 := by
        calc
          (3 : ZMod 169653067) ^ 3 = (3 : ZMod 169653067) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 1 * (3 : ZMod 169653067) ^ 1) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 169653067) ^ 6 = 729 := by
        calc
          (3 : ZMod 169653067) ^ 6 = (3 : ZMod 169653067) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 3 * (3 : ZMod 169653067) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 169653067) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 169653067) ^ 13 = (3 : ZMod 169653067) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 6 * (3 : ZMod 169653067) ^ 6) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 169653067) ^ 26 = 123578535 := by
        calc
          (3 : ZMod 169653067) ^ 26 = (3 : ZMod 169653067) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 13 * (3 : ZMod 169653067) ^ 13 := by rw [pow_add]
          _ = 123578535 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 169653067) ^ 53 = 16087576 := by
        calc
          (3 : ZMod 169653067) ^ 53 = (3 : ZMod 169653067) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 26 * (3 : ZMod 169653067) ^ 26) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 16087576 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 169653067) ^ 107 = 149908736 := by
        calc
          (3 : ZMod 169653067) ^ 107 = (3 : ZMod 169653067) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 53 * (3 : ZMod 169653067) ^ 53) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 149908736 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 169653067) ^ 215 = 17874292 := by
        calc
          (3 : ZMod 169653067) ^ 215 = (3 : ZMod 169653067) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 107 * (3 : ZMod 169653067) ^ 107) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 17874292 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 169653067) ^ 431 = 163752061 := by
        calc
          (3 : ZMod 169653067) ^ 431 = (3 : ZMod 169653067) ^ (215 + 215 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 215 * (3 : ZMod 169653067) ^ 215) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 163752061 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 169653067) ^ 862 = 70851085 := by
        calc
          (3 : ZMod 169653067) ^ 862 = (3 : ZMod 169653067) ^ (431 + 431) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 431 * (3 : ZMod 169653067) ^ 431 := by rw [pow_add]
          _ = 70851085 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 169653067) ^ 1725 = 159763940 := by
        calc
          (3 : ZMod 169653067) ^ 1725 = (3 : ZMod 169653067) ^ (862 + 862 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 862 * (3 : ZMod 169653067) ^ 862) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 159763940 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 169653067) ^ 3451 = 56641947 := by
        calc
          (3 : ZMod 169653067) ^ 3451 = (3 : ZMod 169653067) ^ (1725 + 1725 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 1725 * (3 : ZMod 169653067) ^ 1725) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 56641947 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 169653067) ^ 6903 = 145639288 := by
        calc
          (3 : ZMod 169653067) ^ 6903 = (3 : ZMod 169653067) ^ (3451 + 3451 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 3451 * (3 : ZMod 169653067) ^ 3451) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 145639288 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 169653067) ^ 13806 = 118984620 := by
        calc
          (3 : ZMod 169653067) ^ 13806 = (3 : ZMod 169653067) ^ (6903 + 6903) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 6903 * (3 : ZMod 169653067) ^ 6903 := by rw [pow_add]
          _ = 118984620 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 169653067) ^ 27612 = 28666810 := by
        calc
          (3 : ZMod 169653067) ^ 27612 = (3 : ZMod 169653067) ^ (13806 + 13806) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 13806 * (3 : ZMod 169653067) ^ 13806 := by rw [pow_add]
          _ = 28666810 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 169653067) ^ 55225 = 164167313 := by
        calc
          (3 : ZMod 169653067) ^ 55225 = (3 : ZMod 169653067) ^ (27612 + 27612 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 27612 * (3 : ZMod 169653067) ^ 27612) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 164167313 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 169653067) ^ 110451 = 120200699 := by
        calc
          (3 : ZMod 169653067) ^ 110451 = (3 : ZMod 169653067) ^ (55225 + 55225 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 55225 * (3 : ZMod 169653067) ^ 55225) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 120200699 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 169653067) ^ 220902 = 124676315 := by
        calc
          (3 : ZMod 169653067) ^ 220902 = (3 : ZMod 169653067) ^ (110451 + 110451) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 110451 * (3 : ZMod 169653067) ^ 110451 := by rw [pow_add]
          _ = 124676315 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 169653067) ^ 441804 = 167746373 := by
        calc
          (3 : ZMod 169653067) ^ 441804 = (3 : ZMod 169653067) ^ (220902 + 220902) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 220902 * (3 : ZMod 169653067) ^ 220902 := by rw [pow_add]
          _ = 167746373 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 169653067) ^ 883609 = 128963746 := by
        calc
          (3 : ZMod 169653067) ^ 883609 = (3 : ZMod 169653067) ^ (441804 + 441804 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 441804 * (3 : ZMod 169653067) ^ 441804) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 128963746 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 169653067) ^ 1767219 = 93786928 := by
        calc
          (3 : ZMod 169653067) ^ 1767219 = (3 : ZMod 169653067) ^ (883609 + 883609 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 883609 * (3 : ZMod 169653067) ^ 883609) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 93786928 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 169653067) ^ 3534438 = 58745013 := by
        calc
          (3 : ZMod 169653067) ^ 3534438 = (3 : ZMod 169653067) ^ (1767219 + 1767219) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 1767219 * (3 : ZMod 169653067) ^ 1767219 := by rw [pow_add]
          _ = 58745013 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 169653067) ^ 7068877 = 29175266 := by
        calc
          (3 : ZMod 169653067) ^ 7068877 = (3 : ZMod 169653067) ^ (3534438 + 3534438 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 3534438 * (3 : ZMod 169653067) ^ 3534438) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 29175266 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 169653067) ^ 14137755 = 163314993 := by
        calc
          (3 : ZMod 169653067) ^ 14137755 = (3 : ZMod 169653067) ^ (7068877 + 7068877 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 7068877 * (3 : ZMod 169653067) ^ 7068877) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 163314993 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 169653067) ^ 28275511 = 150638844 := by
        calc
          (3 : ZMod 169653067) ^ 28275511 = (3 : ZMod 169653067) ^ (14137755 + 14137755 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 14137755 * (3 : ZMod 169653067) ^ 14137755) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 150638844 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 169653067) ^ 56551022 = 150638843 := by
        calc
          (3 : ZMod 169653067) ^ 56551022 = (3 : ZMod 169653067) ^ (28275511 + 28275511) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 28275511 * (3 : ZMod 169653067) ^ 28275511 := by rw [pow_add]
          _ = 150638843 := by rw [factor_1_24]; decide
      change (3 : ZMod 169653067) ^ 56551022 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (3 : ZMod 169653067) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 169653067) ^ 3 = 27 := by
        calc
          (3 : ZMod 169653067) ^ 3 = (3 : ZMod 169653067) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 1 * (3 : ZMod 169653067) ^ 1) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 169653067) ^ 7 = 2187 := by
        calc
          (3 : ZMod 169653067) ^ 7 = (3 : ZMod 169653067) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 3 * (3 : ZMod 169653067) ^ 3) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 169653067) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 169653067) ^ 14 = (3 : ZMod 169653067) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 7 * (3 : ZMod 169653067) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 169653067) ^ 29 = 113212172 := by
        calc
          (3 : ZMod 169653067) ^ 29 = (3 : ZMod 169653067) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 14 * (3 : ZMod 169653067) ^ 14) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 113212172 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 169653067) ^ 58 = 7260427 := by
        calc
          (3 : ZMod 169653067) ^ 58 = (3 : ZMod 169653067) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 29 * (3 : ZMod 169653067) ^ 29 := by rw [pow_add]
          _ = 7260427 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 169653067) ^ 117 = 142528272 := by
        calc
          (3 : ZMod 169653067) ^ 117 = (3 : ZMod 169653067) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 58 * (3 : ZMod 169653067) ^ 58) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 142528272 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 169653067) ^ 235 = 87213657 := by
        calc
          (3 : ZMod 169653067) ^ 235 = (3 : ZMod 169653067) ^ (117 + 117 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 117 * (3 : ZMod 169653067) ^ 117) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 87213657 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 169653067) ^ 470 = 93803123 := by
        calc
          (3 : ZMod 169653067) ^ 470 = (3 : ZMod 169653067) ^ (235 + 235) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 235 * (3 : ZMod 169653067) ^ 235 := by rw [pow_add]
          _ = 93803123 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 169653067) ^ 941 = 136797500 := by
        calc
          (3 : ZMod 169653067) ^ 941 = (3 : ZMod 169653067) ^ (470 + 470 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 470 * (3 : ZMod 169653067) ^ 470) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 136797500 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 169653067) ^ 1882 = 68428117 := by
        calc
          (3 : ZMod 169653067) ^ 1882 = (3 : ZMod 169653067) ^ (941 + 941) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 941 * (3 : ZMod 169653067) ^ 941 := by rw [pow_add]
          _ = 68428117 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 169653067) ^ 3765 = 63694770 := by
        calc
          (3 : ZMod 169653067) ^ 3765 = (3 : ZMod 169653067) ^ (1882 + 1882 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 1882 * (3 : ZMod 169653067) ^ 1882) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 63694770 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 169653067) ^ 7530 = 168647551 := by
        calc
          (3 : ZMod 169653067) ^ 7530 = (3 : ZMod 169653067) ^ (3765 + 3765) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 3765 * (3 : ZMod 169653067) ^ 3765 := by rw [pow_add]
          _ = 168647551 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 169653067) ^ 15061 = 129746942 := by
        calc
          (3 : ZMod 169653067) ^ 15061 = (3 : ZMod 169653067) ^ (7530 + 7530 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 7530 * (3 : ZMod 169653067) ^ 7530) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 129746942 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 169653067) ^ 30123 = 75783812 := by
        calc
          (3 : ZMod 169653067) ^ 30123 = (3 : ZMod 169653067) ^ (15061 + 15061 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 15061 * (3 : ZMod 169653067) ^ 15061) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 75783812 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 169653067) ^ 60246 = 112082633 := by
        calc
          (3 : ZMod 169653067) ^ 60246 = (3 : ZMod 169653067) ^ (30123 + 30123) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 30123 * (3 : ZMod 169653067) ^ 30123 := by rw [pow_add]
          _ = 112082633 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 169653067) ^ 120492 = 169362465 := by
        calc
          (3 : ZMod 169653067) ^ 120492 = (3 : ZMod 169653067) ^ (60246 + 60246) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 60246 * (3 : ZMod 169653067) ^ 60246 := by rw [pow_add]
          _ = 169362465 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 169653067) ^ 240984 = 131948105 := by
        calc
          (3 : ZMod 169653067) ^ 240984 = (3 : ZMod 169653067) ^ (120492 + 120492) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 120492 * (3 : ZMod 169653067) ^ 120492 := by rw [pow_add]
          _ = 131948105 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 169653067) ^ 481968 = 129329767 := by
        calc
          (3 : ZMod 169653067) ^ 481968 = (3 : ZMod 169653067) ^ (240984 + 240984) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 240984 * (3 : ZMod 169653067) ^ 240984 := by rw [pow_add]
          _ = 129329767 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 169653067) ^ 963937 = 39202987 := by
        calc
          (3 : ZMod 169653067) ^ 963937 = (3 : ZMod 169653067) ^ (481968 + 481968 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 481968 * (3 : ZMod 169653067) ^ 481968) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 39202987 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 169653067) ^ 1927875 = 17859850 := by
        calc
          (3 : ZMod 169653067) ^ 1927875 = (3 : ZMod 169653067) ^ (963937 + 963937 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 963937 * (3 : ZMod 169653067) ^ 963937) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 17859850 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 169653067) ^ 3855751 = 30552144 := by
        calc
          (3 : ZMod 169653067) ^ 3855751 = (3 : ZMod 169653067) ^ (1927875 + 1927875 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 1927875 * (3 : ZMod 169653067) ^ 1927875) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 30552144 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 169653067) ^ 7711503 = 29312461 := by
        calc
          (3 : ZMod 169653067) ^ 7711503 = (3 : ZMod 169653067) ^ (3855751 + 3855751 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 3855751 * (3 : ZMod 169653067) ^ 3855751) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 29312461 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 169653067) ^ 15423006 = 27381130 := by
        calc
          (3 : ZMod 169653067) ^ 15423006 = (3 : ZMod 169653067) ^ (7711503 + 7711503) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 7711503 * (3 : ZMod 169653067) ^ 7711503 := by rw [pow_add]
          _ = 27381130 := by rw [factor_2_22]; decide
      change (3 : ZMod 169653067) ^ 15423006 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (3 : ZMod 169653067) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 169653067) ^ 2 = 9 := by
        calc
          (3 : ZMod 169653067) ^ 2 = (3 : ZMod 169653067) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 1 * (3 : ZMod 169653067) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 169653067) ^ 4 = 81 := by
        calc
          (3 : ZMod 169653067) ^ 4 = (3 : ZMod 169653067) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 2 * (3 : ZMod 169653067) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 169653067) ^ 8 = 6561 := by
        calc
          (3 : ZMod 169653067) ^ 8 = (3 : ZMod 169653067) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 4 * (3 : ZMod 169653067) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 169653067) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 169653067) ^ 17 = (3 : ZMod 169653067) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 8 * (3 : ZMod 169653067) ^ 8) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 169653067) ^ 34 = 26760942 := by
        calc
          (3 : ZMod 169653067) ^ 34 = (3 : ZMod 169653067) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 17 * (3 : ZMod 169653067) ^ 17 := by rw [pow_add]
          _ = 26760942 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 169653067) ^ 69 = 22960842 := by
        calc
          (3 : ZMod 169653067) ^ 69 = (3 : ZMod 169653067) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 34 * (3 : ZMod 169653067) ^ 34) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 22960842 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 169653067) ^ 139 = 69408439 := by
        calc
          (3 : ZMod 169653067) ^ 139 = (3 : ZMod 169653067) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 69 * (3 : ZMod 169653067) ^ 69) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 69408439 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 169653067) ^ 279 = 87443659 := by
        calc
          (3 : ZMod 169653067) ^ 279 = (3 : ZMod 169653067) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 139 * (3 : ZMod 169653067) ^ 139) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 87443659 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 169653067) ^ 559 = 124719145 := by
        calc
          (3 : ZMod 169653067) ^ 559 = (3 : ZMod 169653067) ^ (279 + 279 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 279 * (3 : ZMod 169653067) ^ 279) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 124719145 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 169653067) ^ 1119 = 67028090 := by
        calc
          (3 : ZMod 169653067) ^ 1119 = (3 : ZMod 169653067) ^ (559 + 559 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 559 * (3 : ZMod 169653067) ^ 559) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 67028090 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 169653067) ^ 2238 = 113733276 := by
        calc
          (3 : ZMod 169653067) ^ 2238 = (3 : ZMod 169653067) ^ (1119 + 1119) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 1119 * (3 : ZMod 169653067) ^ 1119 := by rw [pow_add]
          _ = 113733276 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 169653067) ^ 4477 = 96580508 := by
        calc
          (3 : ZMod 169653067) ^ 4477 = (3 : ZMod 169653067) ^ (2238 + 2238 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 2238 * (3 : ZMod 169653067) ^ 2238) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 96580508 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 169653067) ^ 8955 = 5300607 := by
        calc
          (3 : ZMod 169653067) ^ 8955 = (3 : ZMod 169653067) ^ (4477 + 4477 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 4477 * (3 : ZMod 169653067) ^ 4477) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 5300607 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 169653067) ^ 17911 = 61468536 := by
        calc
          (3 : ZMod 169653067) ^ 17911 = (3 : ZMod 169653067) ^ (8955 + 8955 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 8955 * (3 : ZMod 169653067) ^ 8955) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 61468536 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 169653067) ^ 35822 = 139151556 := by
        calc
          (3 : ZMod 169653067) ^ 35822 = (3 : ZMod 169653067) ^ (17911 + 17911) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 17911 * (3 : ZMod 169653067) ^ 17911 := by rw [pow_add]
          _ = 139151556 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 169653067) ^ 71644 = 41693057 := by
        calc
          (3 : ZMod 169653067) ^ 71644 = (3 : ZMod 169653067) ^ (35822 + 35822) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 35822 * (3 : ZMod 169653067) ^ 35822 := by rw [pow_add]
          _ = 41693057 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 169653067) ^ 143288 = 40848226 := by
        calc
          (3 : ZMod 169653067) ^ 143288 = (3 : ZMod 169653067) ^ (71644 + 71644) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 71644 * (3 : ZMod 169653067) ^ 71644 := by rw [pow_add]
          _ = 40848226 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 169653067) ^ 286576 = 124237465 := by
        calc
          (3 : ZMod 169653067) ^ 286576 = (3 : ZMod 169653067) ^ (143288 + 143288) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 143288 * (3 : ZMod 169653067) ^ 143288 := by rw [pow_add]
          _ = 124237465 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 169653067) ^ 573152 = 63214132 := by
        calc
          (3 : ZMod 169653067) ^ 573152 = (3 : ZMod 169653067) ^ (286576 + 286576) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 286576 * (3 : ZMod 169653067) ^ 286576 := by rw [pow_add]
          _ = 63214132 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 169653067) ^ 1146304 = 161170322 := by
        calc
          (3 : ZMod 169653067) ^ 1146304 = (3 : ZMod 169653067) ^ (573152 + 573152) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 573152 * (3 : ZMod 169653067) ^ 573152 := by rw [pow_add]
          _ = 161170322 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 169653067) ^ 2292609 = 84427600 := by
        calc
          (3 : ZMod 169653067) ^ 2292609 = (3 : ZMod 169653067) ^ (1146304 + 1146304 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 1146304 * (3 : ZMod 169653067) ^ 1146304) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 84427600 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 169653067) ^ 4585218 = 55773843 := by
        calc
          (3 : ZMod 169653067) ^ 4585218 = (3 : ZMod 169653067) ^ (2292609 + 2292609) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 2292609 * (3 : ZMod 169653067) ^ 2292609 := by rw [pow_add]
          _ = 55773843 := by rw [factor_3_21]; decide
      change (3 : ZMod 169653067) ^ 4585218 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (3 : ZMod 169653067) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 169653067) ^ 2 = 9 := by
        calc
          (3 : ZMod 169653067) ^ 2 = (3 : ZMod 169653067) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 1 * (3 : ZMod 169653067) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 169653067) ^ 4 = 81 := by
        calc
          (3 : ZMod 169653067) ^ 4 = (3 : ZMod 169653067) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 2 * (3 : ZMod 169653067) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 169653067) ^ 9 = 19683 := by
        calc
          (3 : ZMod 169653067) ^ 9 = (3 : ZMod 169653067) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 4 * (3 : ZMod 169653067) ^ 4) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 169653067) ^ 19 = 144343065 := by
        calc
          (3 : ZMod 169653067) ^ 19 = (3 : ZMod 169653067) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 9 * (3 : ZMod 169653067) ^ 9) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 144343065 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 169653067) ^ 38 = 131799498 := by
        calc
          (3 : ZMod 169653067) ^ 38 = (3 : ZMod 169653067) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 19 * (3 : ZMod 169653067) ^ 19 := by rw [pow_add]
          _ = 131799498 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 169653067) ^ 76 = 167706689 := by
        calc
          (3 : ZMod 169653067) ^ 76 = (3 : ZMod 169653067) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 38 * (3 : ZMod 169653067) ^ 38 := by rw [pow_add]
          _ = 167706689 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 169653067) ^ 152 = 34332774 := by
        calc
          (3 : ZMod 169653067) ^ 152 = (3 : ZMod 169653067) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 76 * (3 : ZMod 169653067) ^ 76 := by rw [pow_add]
          _ = 34332774 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 169653067) ^ 305 = 120609288 := by
        calc
          (3 : ZMod 169653067) ^ 305 = (3 : ZMod 169653067) ^ (152 + 152 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 152 * (3 : ZMod 169653067) ^ 152) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 120609288 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 169653067) ^ 610 = 104411204 := by
        calc
          (3 : ZMod 169653067) ^ 610 = (3 : ZMod 169653067) ^ (305 + 305) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 305 * (3 : ZMod 169653067) ^ 305 := by rw [pow_add]
          _ = 104411204 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 169653067) ^ 1221 = 48582599 := by
        calc
          (3 : ZMod 169653067) ^ 1221 = (3 : ZMod 169653067) ^ (610 + 610 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = ((3 : ZMod 169653067) ^ 610 * (3 : ZMod 169653067) ^ 610) * (3 : ZMod 169653067) := by rw [pow_succ, pow_add]
          _ = 48582599 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 169653067) ^ 2442 = 150590959 := by
        calc
          (3 : ZMod 169653067) ^ 2442 = (3 : ZMod 169653067) ^ (1221 + 1221) :=
            congrArg (fun n : ℕ => (3 : ZMod 169653067) ^ n) (by norm_num)
          _ = (3 : ZMod 169653067) ^ 1221 * (3 : ZMod 169653067) ^ 1221 := by rw [pow_add]
          _ = 150590959 := by rw [factor_4_10]; decide
      change (3 : ZMod 169653067) ^ 2442 ≠ 1
      rw [factor_4_11]
      decide

#print axioms prime_lucas_169653067

end TotientTailPeriodKiller
end Erdos249257
