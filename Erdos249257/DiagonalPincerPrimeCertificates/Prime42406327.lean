import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_42406327 : Nat.Prime 42406327 := by
  apply lucas_primality 42406327 (3 : ZMod 42406327)
  ·
      have fermat_0 : (3 : ZMod 42406327) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 42406327) ^ 2 = 9 := by
        calc
          (3 : ZMod 42406327) ^ 2 = (3 : ZMod 42406327) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 1 * (3 : ZMod 42406327) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 42406327) ^ 5 = 243 := by
        calc
          (3 : ZMod 42406327) ^ 5 = (3 : ZMod 42406327) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 2 * (3 : ZMod 42406327) ^ 2) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 42406327) ^ 10 = 59049 := by
        calc
          (3 : ZMod 42406327) ^ 10 = (3 : ZMod 42406327) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 5 * (3 : ZMod 42406327) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 42406327) ^ 20 = 9465587 := by
        calc
          (3 : ZMod 42406327) ^ 20 = (3 : ZMod 42406327) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 10 * (3 : ZMod 42406327) ^ 10 := by rw [pow_add]
          _ = 9465587 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 42406327) ^ 40 = 19785486 := by
        calc
          (3 : ZMod 42406327) ^ 40 = (3 : ZMod 42406327) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 20 * (3 : ZMod 42406327) ^ 20 := by rw [pow_add]
          _ = 19785486 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 42406327) ^ 80 = 14633750 := by
        calc
          (3 : ZMod 42406327) ^ 80 = (3 : ZMod 42406327) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 40 * (3 : ZMod 42406327) ^ 40 := by rw [pow_add]
          _ = 14633750 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 42406327) ^ 161 = 7916452 := by
        calc
          (3 : ZMod 42406327) ^ 161 = (3 : ZMod 42406327) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 80 * (3 : ZMod 42406327) ^ 80) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 7916452 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 42406327) ^ 323 = 23327735 := by
        calc
          (3 : ZMod 42406327) ^ 323 = (3 : ZMod 42406327) ^ (161 + 161 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 161 * (3 : ZMod 42406327) ^ 161) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 23327735 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 42406327) ^ 647 = 1204980 := by
        calc
          (3 : ZMod 42406327) ^ 647 = (3 : ZMod 42406327) ^ (323 + 323 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 323 * (3 : ZMod 42406327) ^ 323) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 1204980 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 42406327) ^ 1294 = 26570247 := by
        calc
          (3 : ZMod 42406327) ^ 1294 = (3 : ZMod 42406327) ^ (647 + 647) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 647 * (3 : ZMod 42406327) ^ 647 := by rw [pow_add]
          _ = 26570247 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 42406327) ^ 2588 = 38124629 := by
        calc
          (3 : ZMod 42406327) ^ 2588 = (3 : ZMod 42406327) ^ (1294 + 1294) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 1294 * (3 : ZMod 42406327) ^ 1294 := by rw [pow_add]
          _ = 38124629 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 42406327) ^ 5176 = 4099872 := by
        calc
          (3 : ZMod 42406327) ^ 5176 = (3 : ZMod 42406327) ^ (2588 + 2588) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 2588 * (3 : ZMod 42406327) ^ 2588 := by rw [pow_add]
          _ = 4099872 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 42406327) ^ 10353 = 3592007 := by
        calc
          (3 : ZMod 42406327) ^ 10353 = (3 : ZMod 42406327) ^ (5176 + 5176 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 5176 * (3 : ZMod 42406327) ^ 5176) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 3592007 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 42406327) ^ 20706 = 7641356 := by
        calc
          (3 : ZMod 42406327) ^ 20706 = (3 : ZMod 42406327) ^ (10353 + 10353) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 10353 * (3 : ZMod 42406327) ^ 10353 := by rw [pow_add]
          _ = 7641356 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 42406327) ^ 41412 = 32120588 := by
        calc
          (3 : ZMod 42406327) ^ 41412 = (3 : ZMod 42406327) ^ (20706 + 20706) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 20706 * (3 : ZMod 42406327) ^ 20706 := by rw [pow_add]
          _ = 32120588 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 42406327) ^ 82824 = 19612019 := by
        calc
          (3 : ZMod 42406327) ^ 82824 = (3 : ZMod 42406327) ^ (41412 + 41412) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 41412 * (3 : ZMod 42406327) ^ 41412 := by rw [pow_add]
          _ = 19612019 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 42406327) ^ 165649 = 26660724 := by
        calc
          (3 : ZMod 42406327) ^ 165649 = (3 : ZMod 42406327) ^ (82824 + 82824 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 82824 * (3 : ZMod 42406327) ^ 82824) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 26660724 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 42406327) ^ 331299 = 8734275 := by
        calc
          (3 : ZMod 42406327) ^ 331299 = (3 : ZMod 42406327) ^ (165649 + 165649 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 165649 * (3 : ZMod 42406327) ^ 165649) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 8734275 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 42406327) ^ 662598 = 19317743 := by
        calc
          (3 : ZMod 42406327) ^ 662598 = (3 : ZMod 42406327) ^ (331299 + 331299) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 331299 * (3 : ZMod 42406327) ^ 331299 := by rw [pow_add]
          _ = 19317743 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 42406327) ^ 1325197 = 35263592 := by
        calc
          (3 : ZMod 42406327) ^ 1325197 = (3 : ZMod 42406327) ^ (662598 + 662598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 662598 * (3 : ZMod 42406327) ^ 662598) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 35263592 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 42406327) ^ 2650395 = 21176731 := by
        calc
          (3 : ZMod 42406327) ^ 2650395 = (3 : ZMod 42406327) ^ (1325197 + 1325197 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 1325197 * (3 : ZMod 42406327) ^ 1325197) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 21176731 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 42406327) ^ 5300790 = 30777406 := by
        calc
          (3 : ZMod 42406327) ^ 5300790 = (3 : ZMod 42406327) ^ (2650395 + 2650395) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 2650395 * (3 : ZMod 42406327) ^ 2650395 := by rw [pow_add]
          _ = 30777406 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 42406327) ^ 10601581 = 17349503 := by
        calc
          (3 : ZMod 42406327) ^ 10601581 = (3 : ZMod 42406327) ^ (5300790 + 5300790 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 5300790 * (3 : ZMod 42406327) ^ 5300790) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 17349503 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 42406327) ^ 21203163 = 42406326 := by
        calc
          (3 : ZMod 42406327) ^ 21203163 = (3 : ZMod 42406327) ^ (10601581 + 10601581 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 10601581 * (3 : ZMod 42406327) ^ 10601581) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 42406326 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 42406327) ^ 42406326 = 1 := by
        calc
          (3 : ZMod 42406327) ^ 42406326 = (3 : ZMod 42406327) ^ (21203163 + 21203163) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 21203163 * (3 : ZMod 42406327) ^ 21203163 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (31, 1), (75997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (31, 1), (75997, 1)] : List FactorBlock).map factorBlockValue).prod = 42406327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 42406327) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 42406327) ^ 2 = 9 := by
        calc
          (3 : ZMod 42406327) ^ 2 = (3 : ZMod 42406327) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 1 * (3 : ZMod 42406327) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 42406327) ^ 5 = 243 := by
        calc
          (3 : ZMod 42406327) ^ 5 = (3 : ZMod 42406327) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 2 * (3 : ZMod 42406327) ^ 2) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 42406327) ^ 10 = 59049 := by
        calc
          (3 : ZMod 42406327) ^ 10 = (3 : ZMod 42406327) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 5 * (3 : ZMod 42406327) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 42406327) ^ 20 = 9465587 := by
        calc
          (3 : ZMod 42406327) ^ 20 = (3 : ZMod 42406327) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 10 * (3 : ZMod 42406327) ^ 10 := by rw [pow_add]
          _ = 9465587 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 42406327) ^ 40 = 19785486 := by
        calc
          (3 : ZMod 42406327) ^ 40 = (3 : ZMod 42406327) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 20 * (3 : ZMod 42406327) ^ 20 := by rw [pow_add]
          _ = 19785486 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 42406327) ^ 80 = 14633750 := by
        calc
          (3 : ZMod 42406327) ^ 80 = (3 : ZMod 42406327) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 40 * (3 : ZMod 42406327) ^ 40 := by rw [pow_add]
          _ = 14633750 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 42406327) ^ 161 = 7916452 := by
        calc
          (3 : ZMod 42406327) ^ 161 = (3 : ZMod 42406327) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 80 * (3 : ZMod 42406327) ^ 80) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 7916452 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 42406327) ^ 323 = 23327735 := by
        calc
          (3 : ZMod 42406327) ^ 323 = (3 : ZMod 42406327) ^ (161 + 161 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 161 * (3 : ZMod 42406327) ^ 161) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 23327735 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 42406327) ^ 647 = 1204980 := by
        calc
          (3 : ZMod 42406327) ^ 647 = (3 : ZMod 42406327) ^ (323 + 323 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 323 * (3 : ZMod 42406327) ^ 323) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 1204980 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 42406327) ^ 1294 = 26570247 := by
        calc
          (3 : ZMod 42406327) ^ 1294 = (3 : ZMod 42406327) ^ (647 + 647) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 647 * (3 : ZMod 42406327) ^ 647 := by rw [pow_add]
          _ = 26570247 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 42406327) ^ 2588 = 38124629 := by
        calc
          (3 : ZMod 42406327) ^ 2588 = (3 : ZMod 42406327) ^ (1294 + 1294) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 1294 * (3 : ZMod 42406327) ^ 1294 := by rw [pow_add]
          _ = 38124629 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 42406327) ^ 5176 = 4099872 := by
        calc
          (3 : ZMod 42406327) ^ 5176 = (3 : ZMod 42406327) ^ (2588 + 2588) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 2588 * (3 : ZMod 42406327) ^ 2588 := by rw [pow_add]
          _ = 4099872 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 42406327) ^ 10353 = 3592007 := by
        calc
          (3 : ZMod 42406327) ^ 10353 = (3 : ZMod 42406327) ^ (5176 + 5176 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 5176 * (3 : ZMod 42406327) ^ 5176) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 3592007 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 42406327) ^ 20706 = 7641356 := by
        calc
          (3 : ZMod 42406327) ^ 20706 = (3 : ZMod 42406327) ^ (10353 + 10353) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 10353 * (3 : ZMod 42406327) ^ 10353 := by rw [pow_add]
          _ = 7641356 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 42406327) ^ 41412 = 32120588 := by
        calc
          (3 : ZMod 42406327) ^ 41412 = (3 : ZMod 42406327) ^ (20706 + 20706) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 20706 * (3 : ZMod 42406327) ^ 20706 := by rw [pow_add]
          _ = 32120588 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 42406327) ^ 82824 = 19612019 := by
        calc
          (3 : ZMod 42406327) ^ 82824 = (3 : ZMod 42406327) ^ (41412 + 41412) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 41412 * (3 : ZMod 42406327) ^ 41412 := by rw [pow_add]
          _ = 19612019 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 42406327) ^ 165649 = 26660724 := by
        calc
          (3 : ZMod 42406327) ^ 165649 = (3 : ZMod 42406327) ^ (82824 + 82824 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 82824 * (3 : ZMod 42406327) ^ 82824) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 26660724 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 42406327) ^ 331299 = 8734275 := by
        calc
          (3 : ZMod 42406327) ^ 331299 = (3 : ZMod 42406327) ^ (165649 + 165649 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 165649 * (3 : ZMod 42406327) ^ 165649) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 8734275 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 42406327) ^ 662598 = 19317743 := by
        calc
          (3 : ZMod 42406327) ^ 662598 = (3 : ZMod 42406327) ^ (331299 + 331299) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 331299 * (3 : ZMod 42406327) ^ 331299 := by rw [pow_add]
          _ = 19317743 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 42406327) ^ 1325197 = 35263592 := by
        calc
          (3 : ZMod 42406327) ^ 1325197 = (3 : ZMod 42406327) ^ (662598 + 662598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 662598 * (3 : ZMod 42406327) ^ 662598) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 35263592 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 42406327) ^ 2650395 = 21176731 := by
        calc
          (3 : ZMod 42406327) ^ 2650395 = (3 : ZMod 42406327) ^ (1325197 + 1325197 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 1325197 * (3 : ZMod 42406327) ^ 1325197) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 21176731 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 42406327) ^ 5300790 = 30777406 := by
        calc
          (3 : ZMod 42406327) ^ 5300790 = (3 : ZMod 42406327) ^ (2650395 + 2650395) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 2650395 * (3 : ZMod 42406327) ^ 2650395 := by rw [pow_add]
          _ = 30777406 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 42406327) ^ 10601581 = 17349503 := by
        calc
          (3 : ZMod 42406327) ^ 10601581 = (3 : ZMod 42406327) ^ (5300790 + 5300790 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 5300790 * (3 : ZMod 42406327) ^ 5300790) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 17349503 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 42406327) ^ 21203163 = 42406326 := by
        calc
          (3 : ZMod 42406327) ^ 21203163 = (3 : ZMod 42406327) ^ (10601581 + 10601581 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 10601581 * (3 : ZMod 42406327) ^ 10601581) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 42406326 := by rw [factor_0_23]; decide
      change (3 : ZMod 42406327) ^ 21203163 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (3 : ZMod 42406327) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 42406327) ^ 3 = 27 := by
        calc
          (3 : ZMod 42406327) ^ 3 = (3 : ZMod 42406327) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 1 * (3 : ZMod 42406327) ^ 1) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 42406327) ^ 6 = 729 := by
        calc
          (3 : ZMod 42406327) ^ 6 = (3 : ZMod 42406327) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 3 * (3 : ZMod 42406327) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 42406327) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 42406327) ^ 13 = (3 : ZMod 42406327) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 6 * (3 : ZMod 42406327) ^ 6) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 42406327) ^ 26 = 30587949 := by
        calc
          (3 : ZMod 42406327) ^ 26 = (3 : ZMod 42406327) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 13 * (3 : ZMod 42406327) ^ 13 := by rw [pow_add]
          _ = 30587949 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 42406327) ^ 53 = 181104 := by
        calc
          (3 : ZMod 42406327) ^ 53 = (3 : ZMod 42406327) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 26 * (3 : ZMod 42406327) ^ 26) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 181104 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 42406327) ^ 107 = 13297808 := by
        calc
          (3 : ZMod 42406327) ^ 107 = (3 : ZMod 42406327) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 53 * (3 : ZMod 42406327) ^ 53) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 13297808 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 42406327) ^ 215 = 41653049 := by
        calc
          (3 : ZMod 42406327) ^ 215 = (3 : ZMod 42406327) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 107 * (3 : ZMod 42406327) ^ 107) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 41653049 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 42406327) ^ 431 = 8457418 := by
        calc
          (3 : ZMod 42406327) ^ 431 = (3 : ZMod 42406327) ^ (215 + 215 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 215 * (3 : ZMod 42406327) ^ 215) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 8457418 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 42406327) ^ 862 = 22504995 := by
        calc
          (3 : ZMod 42406327) ^ 862 = (3 : ZMod 42406327) ^ (431 + 431) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 431 * (3 : ZMod 42406327) ^ 431 := by rw [pow_add]
          _ = 22504995 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 42406327) ^ 1725 = 20992257 := by
        calc
          (3 : ZMod 42406327) ^ 1725 = (3 : ZMod 42406327) ^ (862 + 862 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 862 * (3 : ZMod 42406327) ^ 862) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 20992257 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 42406327) ^ 3451 = 23748903 := by
        calc
          (3 : ZMod 42406327) ^ 3451 = (3 : ZMod 42406327) ^ (1725 + 1725 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 1725 * (3 : ZMod 42406327) ^ 1725) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 23748903 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 42406327) ^ 6902 = 10873340 := by
        calc
          (3 : ZMod 42406327) ^ 6902 = (3 : ZMod 42406327) ^ (3451 + 3451) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 3451 * (3 : ZMod 42406327) ^ 3451 := by rw [pow_add]
          _ = 10873340 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 42406327) ^ 13804 = 4578368 := by
        calc
          (3 : ZMod 42406327) ^ 13804 = (3 : ZMod 42406327) ^ (6902 + 6902) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 6902 * (3 : ZMod 42406327) ^ 6902 := by rw [pow_add]
          _ = 4578368 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 42406327) ^ 27608 = 6107324 := by
        calc
          (3 : ZMod 42406327) ^ 27608 = (3 : ZMod 42406327) ^ (13804 + 13804) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 13804 * (3 : ZMod 42406327) ^ 13804 := by rw [pow_add]
          _ = 6107324 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 42406327) ^ 55216 = 30995259 := by
        calc
          (3 : ZMod 42406327) ^ 55216 = (3 : ZMod 42406327) ^ (27608 + 27608) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 27608 * (3 : ZMod 42406327) ^ 27608 := by rw [pow_add]
          _ = 30995259 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 42406327) ^ 110433 = 3020428 := by
        calc
          (3 : ZMod 42406327) ^ 110433 = (3 : ZMod 42406327) ^ (55216 + 55216 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 55216 * (3 : ZMod 42406327) ^ 55216) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 3020428 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 42406327) ^ 220866 = 27363020 := by
        calc
          (3 : ZMod 42406327) ^ 220866 = (3 : ZMod 42406327) ^ (110433 + 110433) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 110433 * (3 : ZMod 42406327) ^ 110433 := by rw [pow_add]
          _ = 27363020 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 42406327) ^ 441732 = 18305038 := by
        calc
          (3 : ZMod 42406327) ^ 441732 = (3 : ZMod 42406327) ^ (220866 + 220866) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 220866 * (3 : ZMod 42406327) ^ 220866 := by rw [pow_add]
          _ = 18305038 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 42406327) ^ 883465 = 10605866 := by
        calc
          (3 : ZMod 42406327) ^ 883465 = (3 : ZMod 42406327) ^ (441732 + 441732 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 441732 * (3 : ZMod 42406327) ^ 441732) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 10605866 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 42406327) ^ 1766930 = 42208357 := by
        calc
          (3 : ZMod 42406327) ^ 1766930 = (3 : ZMod 42406327) ^ (883465 + 883465) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 883465 * (3 : ZMod 42406327) ^ 883465 := by rw [pow_add]
          _ = 42208357 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 42406327) ^ 3533860 = 8674752 := by
        calc
          (3 : ZMod 42406327) ^ 3533860 = (3 : ZMod 42406327) ^ (1766930 + 1766930) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 1766930 * (3 : ZMod 42406327) ^ 1766930 := by rw [pow_add]
          _ = 8674752 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 42406327) ^ 7067721 = 26024255 := by
        calc
          (3 : ZMod 42406327) ^ 7067721 = (3 : ZMod 42406327) ^ (3533860 + 3533860 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 3533860 * (3 : ZMod 42406327) ^ 3533860) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 26024255 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 42406327) ^ 14135442 = 26024254 := by
        calc
          (3 : ZMod 42406327) ^ 14135442 = (3 : ZMod 42406327) ^ (7067721 + 7067721) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 7067721 * (3 : ZMod 42406327) ^ 7067721 := by rw [pow_add]
          _ = 26024254 := by rw [factor_1_22]; decide
      change (3 : ZMod 42406327) ^ 14135442 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (3 : ZMod 42406327) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 42406327) ^ 2 = 9 := by
        calc
          (3 : ZMod 42406327) ^ 2 = (3 : ZMod 42406327) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 1 * (3 : ZMod 42406327) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 42406327) ^ 5 = 243 := by
        calc
          (3 : ZMod 42406327) ^ 5 = (3 : ZMod 42406327) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 2 * (3 : ZMod 42406327) ^ 2) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 42406327) ^ 10 = 59049 := by
        calc
          (3 : ZMod 42406327) ^ 10 = (3 : ZMod 42406327) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 5 * (3 : ZMod 42406327) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 42406327) ^ 20 = 9465587 := by
        calc
          (3 : ZMod 42406327) ^ 20 = (3 : ZMod 42406327) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 10 * (3 : ZMod 42406327) ^ 10 := by rw [pow_add]
          _ = 9465587 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 42406327) ^ 41 = 16950131 := by
        calc
          (3 : ZMod 42406327) ^ 41 = (3 : ZMod 42406327) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 20 * (3 : ZMod 42406327) ^ 20) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 16950131 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 42406327) ^ 83 = 13454307 := by
        calc
          (3 : ZMod 42406327) ^ 83 = (3 : ZMod 42406327) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 41 * (3 : ZMod 42406327) ^ 41) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 13454307 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 42406327) ^ 166 = 15413121 := by
        calc
          (3 : ZMod 42406327) ^ 166 = (3 : ZMod 42406327) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 83 * (3 : ZMod 42406327) ^ 83 := by rw [pow_add]
          _ = 15413121 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 42406327) ^ 333 = 37110401 := by
        calc
          (3 : ZMod 42406327) ^ 333 = (3 : ZMod 42406327) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 166 * (3 : ZMod 42406327) ^ 166) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 37110401 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 42406327) ^ 667 = 25281705 := by
        calc
          (3 : ZMod 42406327) ^ 667 = (3 : ZMod 42406327) ^ (333 + 333 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 333 * (3 : ZMod 42406327) ^ 333) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 25281705 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 42406327) ^ 1335 = 22930774 := by
        calc
          (3 : ZMod 42406327) ^ 1335 = (3 : ZMod 42406327) ^ (667 + 667 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 667 * (3 : ZMod 42406327) ^ 667) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 22930774 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 42406327) ^ 2671 = 19603134 := by
        calc
          (3 : ZMod 42406327) ^ 2671 = (3 : ZMod 42406327) ^ (1335 + 1335 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 1335 * (3 : ZMod 42406327) ^ 1335) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 19603134 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 42406327) ^ 5343 = 20311732 := by
        calc
          (3 : ZMod 42406327) ^ 5343 = (3 : ZMod 42406327) ^ (2671 + 2671 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 2671 * (3 : ZMod 42406327) ^ 2671) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 20311732 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 42406327) ^ 10687 = 25677363 := by
        calc
          (3 : ZMod 42406327) ^ 10687 = (3 : ZMod 42406327) ^ (5343 + 5343 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 5343 * (3 : ZMod 42406327) ^ 5343) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 25677363 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 42406327) ^ 21374 = 13824781 := by
        calc
          (3 : ZMod 42406327) ^ 21374 = (3 : ZMod 42406327) ^ (10687 + 10687) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 10687 * (3 : ZMod 42406327) ^ 10687 := by rw [pow_add]
          _ = 13824781 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 42406327) ^ 42748 = 17222847 := by
        calc
          (3 : ZMod 42406327) ^ 42748 = (3 : ZMod 42406327) ^ (21374 + 21374) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 21374 * (3 : ZMod 42406327) ^ 21374 := by rw [pow_add]
          _ = 17222847 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 42406327) ^ 85496 = 11087208 := by
        calc
          (3 : ZMod 42406327) ^ 85496 = (3 : ZMod 42406327) ^ (42748 + 42748) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 42748 * (3 : ZMod 42406327) ^ 42748 := by rw [pow_add]
          _ = 11087208 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 42406327) ^ 170993 = 20558749 := by
        calc
          (3 : ZMod 42406327) ^ 170993 = (3 : ZMod 42406327) ^ (85496 + 85496 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 85496 * (3 : ZMod 42406327) ^ 85496) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 20558749 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 42406327) ^ 341986 = 37895408 := by
        calc
          (3 : ZMod 42406327) ^ 341986 = (3 : ZMod 42406327) ^ (170993 + 170993) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 170993 * (3 : ZMod 42406327) ^ 170993 := by rw [pow_add]
          _ = 37895408 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 42406327) ^ 683973 = 33173700 := by
        calc
          (3 : ZMod 42406327) ^ 683973 = (3 : ZMod 42406327) ^ (341986 + 341986 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 341986 * (3 : ZMod 42406327) ^ 341986) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 33173700 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 42406327) ^ 1367946 = 19355159 := by
        calc
          (3 : ZMod 42406327) ^ 1367946 = (3 : ZMod 42406327) ^ (683973 + 683973) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 683973 * (3 : ZMod 42406327) ^ 683973 := by rw [pow_add]
          _ = 19355159 := by rw [factor_2_19]; decide
      change (3 : ZMod 42406327) ^ 1367946 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (3 : ZMod 42406327) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 42406327) ^ 2 = 9 := by
        calc
          (3 : ZMod 42406327) ^ 2 = (3 : ZMod 42406327) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 1 * (3 : ZMod 42406327) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 42406327) ^ 4 = 81 := by
        calc
          (3 : ZMod 42406327) ^ 4 = (3 : ZMod 42406327) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 2 * (3 : ZMod 42406327) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 42406327) ^ 8 = 6561 := by
        calc
          (3 : ZMod 42406327) ^ 8 = (3 : ZMod 42406327) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 4 * (3 : ZMod 42406327) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 42406327) ^ 17 = 1921182 := by
        calc
          (3 : ZMod 42406327) ^ 17 = (3 : ZMod 42406327) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 8 * (3 : ZMod 42406327) ^ 8) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 1921182 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 42406327) ^ 34 = 20794025 := by
        calc
          (3 : ZMod 42406327) ^ 34 = (3 : ZMod 42406327) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 17 * (3 : ZMod 42406327) ^ 17 := by rw [pow_add]
          _ = 20794025 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 42406327) ^ 69 = 39016958 := by
        calc
          (3 : ZMod 42406327) ^ 69 = (3 : ZMod 42406327) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 34 * (3 : ZMod 42406327) ^ 34) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 39016958 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 42406327) ^ 139 = 14326891 := by
        calc
          (3 : ZMod 42406327) ^ 139 = (3 : ZMod 42406327) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 69 * (3 : ZMod 42406327) ^ 69) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 14326891 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 42406327) ^ 279 = 26440879 := by
        calc
          (3 : ZMod 42406327) ^ 279 = (3 : ZMod 42406327) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = ((3 : ZMod 42406327) ^ 139 * (3 : ZMod 42406327) ^ 139) * (3 : ZMod 42406327) := by rw [pow_succ, pow_add]
          _ = 26440879 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 42406327) ^ 558 = 3572374 := by
        calc
          (3 : ZMod 42406327) ^ 558 = (3 : ZMod 42406327) ^ (279 + 279) :=
            congrArg (fun n : ℕ => (3 : ZMod 42406327) ^ n) (by norm_num)
          _ = (3 : ZMod 42406327) ^ 279 * (3 : ZMod 42406327) ^ 279 := by rw [pow_add]
          _ = 3572374 := by rw [factor_3_8]; decide
      change (3 : ZMod 42406327) ^ 558 ≠ 1
      rw [factor_3_9]
      decide

#print axioms prime_lucas_42406327

end TotientTailPeriodKiller
end Erdos249257
