import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_314954641 : Nat.Prime 314954641 := by
  apply lucas_primality 314954641 (17 : ZMod 314954641)
  ·
      have fermat_0 : (17 : ZMod 314954641) ^ 1 = 17 := by norm_num
      have fermat_1 : (17 : ZMod 314954641) ^ 2 = 289 := by
        calc
          (17 : ZMod 314954641) ^ 2 = (17 : ZMod 314954641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1 * (17 : ZMod 314954641) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [fermat_0]; decide
      have fermat_2 : (17 : ZMod 314954641) ^ 4 = 83521 := by
        calc
          (17 : ZMod 314954641) ^ 4 = (17 : ZMod 314954641) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 2 * (17 : ZMod 314954641) ^ 2 := by rw [pow_add]
          _ = 83521 := by rw [fermat_1]; decide
      have fermat_3 : (17 : ZMod 314954641) ^ 9 = 164931481 := by
        calc
          (17 : ZMod 314954641) ^ 9 = (17 : ZMod 314954641) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 4 * (17 : ZMod 314954641) ^ 4) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 164931481 := by rw [fermat_2]; decide
      have fermat_4 : (17 : ZMod 314954641) ^ 18 = 132255880 := by
        calc
          (17 : ZMod 314954641) ^ 18 = (17 : ZMod 314954641) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 9 * (17 : ZMod 314954641) ^ 9 := by rw [pow_add]
          _ = 132255880 := by rw [fermat_3]; decide
      have fermat_5 : (17 : ZMod 314954641) ^ 37 = 280714698 := by
        calc
          (17 : ZMod 314954641) ^ 37 = (17 : ZMod 314954641) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 18 * (17 : ZMod 314954641) ^ 18) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 280714698 := by rw [fermat_4]; decide
      have fermat_6 : (17 : ZMod 314954641) ^ 75 = 168766440 := by
        calc
          (17 : ZMod 314954641) ^ 75 = (17 : ZMod 314954641) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 37 * (17 : ZMod 314954641) ^ 37) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 168766440 := by rw [fermat_5]; decide
      have fermat_7 : (17 : ZMod 314954641) ^ 150 = 264503098 := by
        calc
          (17 : ZMod 314954641) ^ 150 = (17 : ZMod 314954641) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 75 * (17 : ZMod 314954641) ^ 75 := by rw [pow_add]
          _ = 264503098 := by rw [fermat_6]; decide
      have fermat_8 : (17 : ZMod 314954641) ^ 300 = 292323584 := by
        calc
          (17 : ZMod 314954641) ^ 300 = (17 : ZMod 314954641) ^ (150 + 150) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 150 * (17 : ZMod 314954641) ^ 150 := by rw [pow_add]
          _ = 292323584 := by rw [fermat_7]; decide
      have fermat_9 : (17 : ZMod 314954641) ^ 600 = 306611176 := by
        calc
          (17 : ZMod 314954641) ^ 600 = (17 : ZMod 314954641) ^ (300 + 300) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 300 * (17 : ZMod 314954641) ^ 300 := by rw [pow_add]
          _ = 306611176 := by rw [fermat_8]; decide
      have fermat_10 : (17 : ZMod 314954641) ^ 1201 = 48907170 := by
        calc
          (17 : ZMod 314954641) ^ 1201 = (17 : ZMod 314954641) ^ (600 + 600 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 600 * (17 : ZMod 314954641) ^ 600) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 48907170 := by rw [fermat_9]; decide
      have fermat_11 : (17 : ZMod 314954641) ^ 2402 = 224610758 := by
        calc
          (17 : ZMod 314954641) ^ 2402 = (17 : ZMod 314954641) ^ (1201 + 1201) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1201 * (17 : ZMod 314954641) ^ 1201 := by rw [pow_add]
          _ = 224610758 := by rw [fermat_10]; decide
      have fermat_12 : (17 : ZMod 314954641) ^ 4805 = 53894258 := by
        calc
          (17 : ZMod 314954641) ^ 4805 = (17 : ZMod 314954641) ^ (2402 + 2402 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 2402 * (17 : ZMod 314954641) ^ 2402) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 53894258 := by rw [fermat_11]; decide
      have fermat_13 : (17 : ZMod 314954641) ^ 9611 = 247392826 := by
        calc
          (17 : ZMod 314954641) ^ 9611 = (17 : ZMod 314954641) ^ (4805 + 4805 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 4805 * (17 : ZMod 314954641) ^ 4805) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 247392826 := by rw [fermat_12]; decide
      have fermat_14 : (17 : ZMod 314954641) ^ 19223 = 179444438 := by
        calc
          (17 : ZMod 314954641) ^ 19223 = (17 : ZMod 314954641) ^ (9611 + 9611 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 9611 * (17 : ZMod 314954641) ^ 9611) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 179444438 := by rw [fermat_13]; decide
      have fermat_15 : (17 : ZMod 314954641) ^ 38446 = 198767688 := by
        calc
          (17 : ZMod 314954641) ^ 38446 = (17 : ZMod 314954641) ^ (19223 + 19223) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 19223 * (17 : ZMod 314954641) ^ 19223 := by rw [pow_add]
          _ = 198767688 := by rw [fermat_14]; decide
      have fermat_16 : (17 : ZMod 314954641) ^ 76893 = 127732589 := by
        calc
          (17 : ZMod 314954641) ^ 76893 = (17 : ZMod 314954641) ^ (38446 + 38446 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 38446 * (17 : ZMod 314954641) ^ 38446) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 127732589 := by rw [fermat_15]; decide
      have fermat_17 : (17 : ZMod 314954641) ^ 153786 = 127641461 := by
        calc
          (17 : ZMod 314954641) ^ 153786 = (17 : ZMod 314954641) ^ (76893 + 76893) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 76893 * (17 : ZMod 314954641) ^ 76893 := by rw [pow_add]
          _ = 127641461 := by rw [fermat_16]; decide
      have fermat_18 : (17 : ZMod 314954641) ^ 307572 = 84681910 := by
        calc
          (17 : ZMod 314954641) ^ 307572 = (17 : ZMod 314954641) ^ (153786 + 153786) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 153786 * (17 : ZMod 314954641) ^ 153786 := by rw [pow_add]
          _ = 84681910 := by rw [fermat_17]; decide
      have fermat_19 : (17 : ZMod 314954641) ^ 615145 = 278652379 := by
        calc
          (17 : ZMod 314954641) ^ 615145 = (17 : ZMod 314954641) ^ (307572 + 307572 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 307572 * (17 : ZMod 314954641) ^ 307572) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 278652379 := by rw [fermat_18]; decide
      have fermat_20 : (17 : ZMod 314954641) ^ 1230291 = 137992654 := by
        calc
          (17 : ZMod 314954641) ^ 1230291 = (17 : ZMod 314954641) ^ (615145 + 615145 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 615145 * (17 : ZMod 314954641) ^ 615145) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 137992654 := by rw [fermat_19]; decide
      have fermat_21 : (17 : ZMod 314954641) ^ 2460583 = 139717480 := by
        calc
          (17 : ZMod 314954641) ^ 2460583 = (17 : ZMod 314954641) ^ (1230291 + 1230291 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1230291 * (17 : ZMod 314954641) ^ 1230291) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 139717480 := by rw [fermat_20]; decide
      have fermat_22 : (17 : ZMod 314954641) ^ 4921166 = 215662689 := by
        calc
          (17 : ZMod 314954641) ^ 4921166 = (17 : ZMod 314954641) ^ (2460583 + 2460583) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 2460583 * (17 : ZMod 314954641) ^ 2460583 := by rw [pow_add]
          _ = 215662689 := by rw [fermat_21]; decide
      have fermat_23 : (17 : ZMod 314954641) ^ 9842332 = 145515088 := by
        calc
          (17 : ZMod 314954641) ^ 9842332 = (17 : ZMod 314954641) ^ (4921166 + 4921166) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 4921166 * (17 : ZMod 314954641) ^ 4921166 := by rw [pow_add]
          _ = 145515088 := by rw [fermat_22]; decide
      have fermat_24 : (17 : ZMod 314954641) ^ 19684665 = 184053237 := by
        calc
          (17 : ZMod 314954641) ^ 19684665 = (17 : ZMod 314954641) ^ (9842332 + 9842332 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 9842332 * (17 : ZMod 314954641) ^ 9842332) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 184053237 := by rw [fermat_23]; decide
      have fermat_25 : (17 : ZMod 314954641) ^ 39369330 = 90681273 := by
        calc
          (17 : ZMod 314954641) ^ 39369330 = (17 : ZMod 314954641) ^ (19684665 + 19684665) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 19684665 * (17 : ZMod 314954641) ^ 19684665 := by rw [pow_add]
          _ = 90681273 := by rw [fermat_24]; decide
      have fermat_26 : (17 : ZMod 314954641) ^ 78738660 = 187730832 := by
        calc
          (17 : ZMod 314954641) ^ 78738660 = (17 : ZMod 314954641) ^ (39369330 + 39369330) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 39369330 * (17 : ZMod 314954641) ^ 39369330 := by rw [pow_add]
          _ = 187730832 := by rw [fermat_25]; decide
      have fermat_27 : (17 : ZMod 314954641) ^ 157477320 = 314954640 := by
        calc
          (17 : ZMod 314954641) ^ 157477320 = (17 : ZMod 314954641) ^ (78738660 + 78738660) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 78738660 * (17 : ZMod 314954641) ^ 78738660 := by rw [pow_add]
          _ = 314954640 := by rw [fermat_26]; decide
      have fermat_28 : (17 : ZMod 314954641) ^ 314954640 = 1 := by
        calc
          (17 : ZMod 314954641) ^ 314954640 = (17 : ZMod 314954641) ^ (157477320 + 157477320) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 157477320 * (17 : ZMod 314954641) ^ 157477320 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 314954641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (17 : ZMod 314954641) ^ 1 = 17 := by norm_num
      have factor_0_1 : (17 : ZMod 314954641) ^ 2 = 289 := by
        calc
          (17 : ZMod 314954641) ^ 2 = (17 : ZMod 314954641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1 * (17 : ZMod 314954641) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_0_0]; decide
      have factor_0_2 : (17 : ZMod 314954641) ^ 4 = 83521 := by
        calc
          (17 : ZMod 314954641) ^ 4 = (17 : ZMod 314954641) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 2 * (17 : ZMod 314954641) ^ 2 := by rw [pow_add]
          _ = 83521 := by rw [factor_0_1]; decide
      have factor_0_3 : (17 : ZMod 314954641) ^ 9 = 164931481 := by
        calc
          (17 : ZMod 314954641) ^ 9 = (17 : ZMod 314954641) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 4 * (17 : ZMod 314954641) ^ 4) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 164931481 := by rw [factor_0_2]; decide
      have factor_0_4 : (17 : ZMod 314954641) ^ 18 = 132255880 := by
        calc
          (17 : ZMod 314954641) ^ 18 = (17 : ZMod 314954641) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 9 * (17 : ZMod 314954641) ^ 9 := by rw [pow_add]
          _ = 132255880 := by rw [factor_0_3]; decide
      have factor_0_5 : (17 : ZMod 314954641) ^ 37 = 280714698 := by
        calc
          (17 : ZMod 314954641) ^ 37 = (17 : ZMod 314954641) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 18 * (17 : ZMod 314954641) ^ 18) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 280714698 := by rw [factor_0_4]; decide
      have factor_0_6 : (17 : ZMod 314954641) ^ 75 = 168766440 := by
        calc
          (17 : ZMod 314954641) ^ 75 = (17 : ZMod 314954641) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 37 * (17 : ZMod 314954641) ^ 37) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 168766440 := by rw [factor_0_5]; decide
      have factor_0_7 : (17 : ZMod 314954641) ^ 150 = 264503098 := by
        calc
          (17 : ZMod 314954641) ^ 150 = (17 : ZMod 314954641) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 75 * (17 : ZMod 314954641) ^ 75 := by rw [pow_add]
          _ = 264503098 := by rw [factor_0_6]; decide
      have factor_0_8 : (17 : ZMod 314954641) ^ 300 = 292323584 := by
        calc
          (17 : ZMod 314954641) ^ 300 = (17 : ZMod 314954641) ^ (150 + 150) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 150 * (17 : ZMod 314954641) ^ 150 := by rw [pow_add]
          _ = 292323584 := by rw [factor_0_7]; decide
      have factor_0_9 : (17 : ZMod 314954641) ^ 600 = 306611176 := by
        calc
          (17 : ZMod 314954641) ^ 600 = (17 : ZMod 314954641) ^ (300 + 300) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 300 * (17 : ZMod 314954641) ^ 300 := by rw [pow_add]
          _ = 306611176 := by rw [factor_0_8]; decide
      have factor_0_10 : (17 : ZMod 314954641) ^ 1201 = 48907170 := by
        calc
          (17 : ZMod 314954641) ^ 1201 = (17 : ZMod 314954641) ^ (600 + 600 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 600 * (17 : ZMod 314954641) ^ 600) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 48907170 := by rw [factor_0_9]; decide
      have factor_0_11 : (17 : ZMod 314954641) ^ 2402 = 224610758 := by
        calc
          (17 : ZMod 314954641) ^ 2402 = (17 : ZMod 314954641) ^ (1201 + 1201) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1201 * (17 : ZMod 314954641) ^ 1201 := by rw [pow_add]
          _ = 224610758 := by rw [factor_0_10]; decide
      have factor_0_12 : (17 : ZMod 314954641) ^ 4805 = 53894258 := by
        calc
          (17 : ZMod 314954641) ^ 4805 = (17 : ZMod 314954641) ^ (2402 + 2402 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 2402 * (17 : ZMod 314954641) ^ 2402) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 53894258 := by rw [factor_0_11]; decide
      have factor_0_13 : (17 : ZMod 314954641) ^ 9611 = 247392826 := by
        calc
          (17 : ZMod 314954641) ^ 9611 = (17 : ZMod 314954641) ^ (4805 + 4805 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 4805 * (17 : ZMod 314954641) ^ 4805) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 247392826 := by rw [factor_0_12]; decide
      have factor_0_14 : (17 : ZMod 314954641) ^ 19223 = 179444438 := by
        calc
          (17 : ZMod 314954641) ^ 19223 = (17 : ZMod 314954641) ^ (9611 + 9611 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 9611 * (17 : ZMod 314954641) ^ 9611) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 179444438 := by rw [factor_0_13]; decide
      have factor_0_15 : (17 : ZMod 314954641) ^ 38446 = 198767688 := by
        calc
          (17 : ZMod 314954641) ^ 38446 = (17 : ZMod 314954641) ^ (19223 + 19223) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 19223 * (17 : ZMod 314954641) ^ 19223 := by rw [pow_add]
          _ = 198767688 := by rw [factor_0_14]; decide
      have factor_0_16 : (17 : ZMod 314954641) ^ 76893 = 127732589 := by
        calc
          (17 : ZMod 314954641) ^ 76893 = (17 : ZMod 314954641) ^ (38446 + 38446 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 38446 * (17 : ZMod 314954641) ^ 38446) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 127732589 := by rw [factor_0_15]; decide
      have factor_0_17 : (17 : ZMod 314954641) ^ 153786 = 127641461 := by
        calc
          (17 : ZMod 314954641) ^ 153786 = (17 : ZMod 314954641) ^ (76893 + 76893) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 76893 * (17 : ZMod 314954641) ^ 76893 := by rw [pow_add]
          _ = 127641461 := by rw [factor_0_16]; decide
      have factor_0_18 : (17 : ZMod 314954641) ^ 307572 = 84681910 := by
        calc
          (17 : ZMod 314954641) ^ 307572 = (17 : ZMod 314954641) ^ (153786 + 153786) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 153786 * (17 : ZMod 314954641) ^ 153786 := by rw [pow_add]
          _ = 84681910 := by rw [factor_0_17]; decide
      have factor_0_19 : (17 : ZMod 314954641) ^ 615145 = 278652379 := by
        calc
          (17 : ZMod 314954641) ^ 615145 = (17 : ZMod 314954641) ^ (307572 + 307572 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 307572 * (17 : ZMod 314954641) ^ 307572) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 278652379 := by rw [factor_0_18]; decide
      have factor_0_20 : (17 : ZMod 314954641) ^ 1230291 = 137992654 := by
        calc
          (17 : ZMod 314954641) ^ 1230291 = (17 : ZMod 314954641) ^ (615145 + 615145 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 615145 * (17 : ZMod 314954641) ^ 615145) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 137992654 := by rw [factor_0_19]; decide
      have factor_0_21 : (17 : ZMod 314954641) ^ 2460583 = 139717480 := by
        calc
          (17 : ZMod 314954641) ^ 2460583 = (17 : ZMod 314954641) ^ (1230291 + 1230291 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1230291 * (17 : ZMod 314954641) ^ 1230291) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 139717480 := by rw [factor_0_20]; decide
      have factor_0_22 : (17 : ZMod 314954641) ^ 4921166 = 215662689 := by
        calc
          (17 : ZMod 314954641) ^ 4921166 = (17 : ZMod 314954641) ^ (2460583 + 2460583) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 2460583 * (17 : ZMod 314954641) ^ 2460583 := by rw [pow_add]
          _ = 215662689 := by rw [factor_0_21]; decide
      have factor_0_23 : (17 : ZMod 314954641) ^ 9842332 = 145515088 := by
        calc
          (17 : ZMod 314954641) ^ 9842332 = (17 : ZMod 314954641) ^ (4921166 + 4921166) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 4921166 * (17 : ZMod 314954641) ^ 4921166 := by rw [pow_add]
          _ = 145515088 := by rw [factor_0_22]; decide
      have factor_0_24 : (17 : ZMod 314954641) ^ 19684665 = 184053237 := by
        calc
          (17 : ZMod 314954641) ^ 19684665 = (17 : ZMod 314954641) ^ (9842332 + 9842332 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 9842332 * (17 : ZMod 314954641) ^ 9842332) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 184053237 := by rw [factor_0_23]; decide
      have factor_0_25 : (17 : ZMod 314954641) ^ 39369330 = 90681273 := by
        calc
          (17 : ZMod 314954641) ^ 39369330 = (17 : ZMod 314954641) ^ (19684665 + 19684665) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 19684665 * (17 : ZMod 314954641) ^ 19684665 := by rw [pow_add]
          _ = 90681273 := by rw [factor_0_24]; decide
      have factor_0_26 : (17 : ZMod 314954641) ^ 78738660 = 187730832 := by
        calc
          (17 : ZMod 314954641) ^ 78738660 = (17 : ZMod 314954641) ^ (39369330 + 39369330) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 39369330 * (17 : ZMod 314954641) ^ 39369330 := by rw [pow_add]
          _ = 187730832 := by rw [factor_0_25]; decide
      have factor_0_27 : (17 : ZMod 314954641) ^ 157477320 = 314954640 := by
        calc
          (17 : ZMod 314954641) ^ 157477320 = (17 : ZMod 314954641) ^ (78738660 + 78738660) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 78738660 * (17 : ZMod 314954641) ^ 78738660 := by rw [pow_add]
          _ = 314954640 := by rw [factor_0_26]; decide
      change (17 : ZMod 314954641) ^ 157477320 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (17 : ZMod 314954641) ^ 1 = 17 := by norm_num
      have factor_1_1 : (17 : ZMod 314954641) ^ 3 = 4913 := by
        calc
          (17 : ZMod 314954641) ^ 3 = (17 : ZMod 314954641) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1 * (17 : ZMod 314954641) ^ 1) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_1_0]; decide
      have factor_1_2 : (17 : ZMod 314954641) ^ 6 = 24137569 := by
        calc
          (17 : ZMod 314954641) ^ 6 = (17 : ZMod 314954641) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 3 * (17 : ZMod 314954641) ^ 3 := by rw [pow_add]
          _ = 24137569 := by rw [factor_1_1]; decide
      have factor_1_3 : (17 : ZMod 314954641) ^ 12 = 245029501 := by
        calc
          (17 : ZMod 314954641) ^ 12 = (17 : ZMod 314954641) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 6 * (17 : ZMod 314954641) ^ 6 := by rw [pow_add]
          _ = 245029501 := by rw [factor_1_2]; decide
      have factor_1_4 : (17 : ZMod 314954641) ^ 25 = 70931819 := by
        calc
          (17 : ZMod 314954641) ^ 25 = (17 : ZMod 314954641) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 12 * (17 : ZMod 314954641) ^ 12) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 70931819 := by rw [factor_1_3]; decide
      have factor_1_5 : (17 : ZMod 314954641) ^ 50 = 35515447 := by
        calc
          (17 : ZMod 314954641) ^ 50 = (17 : ZMod 314954641) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 25 * (17 : ZMod 314954641) ^ 25 := by rw [pow_add]
          _ = 35515447 := by rw [factor_1_4]; decide
      have factor_1_6 : (17 : ZMod 314954641) ^ 100 = 251691677 := by
        calc
          (17 : ZMod 314954641) ^ 100 = (17 : ZMod 314954641) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 50 * (17 : ZMod 314954641) ^ 50 := by rw [pow_add]
          _ = 251691677 := by rw [factor_1_5]; decide
      have factor_1_7 : (17 : ZMod 314954641) ^ 200 = 291492302 := by
        calc
          (17 : ZMod 314954641) ^ 200 = (17 : ZMod 314954641) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 100 * (17 : ZMod 314954641) ^ 100 := by rw [pow_add]
          _ = 291492302 := by rw [factor_1_6]; decide
      have factor_1_8 : (17 : ZMod 314954641) ^ 400 = 165310070 := by
        calc
          (17 : ZMod 314954641) ^ 400 = (17 : ZMod 314954641) ^ (200 + 200) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 200 * (17 : ZMod 314954641) ^ 200 := by rw [pow_add]
          _ = 165310070 := by rw [factor_1_7]; decide
      have factor_1_9 : (17 : ZMod 314954641) ^ 800 = 296697495 := by
        calc
          (17 : ZMod 314954641) ^ 800 = (17 : ZMod 314954641) ^ (400 + 400) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 400 * (17 : ZMod 314954641) ^ 400 := by rw [pow_add]
          _ = 296697495 := by rw [factor_1_8]; decide
      have factor_1_10 : (17 : ZMod 314954641) ^ 1601 = 171243461 := by
        calc
          (17 : ZMod 314954641) ^ 1601 = (17 : ZMod 314954641) ^ (800 + 800 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 800 * (17 : ZMod 314954641) ^ 800) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 171243461 := by rw [factor_1_9]; decide
      have factor_1_11 : (17 : ZMod 314954641) ^ 3203 = 92553150 := by
        calc
          (17 : ZMod 314954641) ^ 3203 = (17 : ZMod 314954641) ^ (1601 + 1601 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1601 * (17 : ZMod 314954641) ^ 1601) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 92553150 := by rw [factor_1_10]; decide
      have factor_1_12 : (17 : ZMod 314954641) ^ 6407 = 208792840 := by
        calc
          (17 : ZMod 314954641) ^ 6407 = (17 : ZMod 314954641) ^ (3203 + 3203 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 3203 * (17 : ZMod 314954641) ^ 3203) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 208792840 := by rw [factor_1_11]; decide
      have factor_1_13 : (17 : ZMod 314954641) ^ 12815 = 184560897 := by
        calc
          (17 : ZMod 314954641) ^ 12815 = (17 : ZMod 314954641) ^ (6407 + 6407 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 6407 * (17 : ZMod 314954641) ^ 6407) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 184560897 := by rw [factor_1_12]; decide
      have factor_1_14 : (17 : ZMod 314954641) ^ 25631 = 270001828 := by
        calc
          (17 : ZMod 314954641) ^ 25631 = (17 : ZMod 314954641) ^ (12815 + 12815 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 12815 * (17 : ZMod 314954641) ^ 12815) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 270001828 := by rw [factor_1_13]; decide
      have factor_1_15 : (17 : ZMod 314954641) ^ 51262 = 120864149 := by
        calc
          (17 : ZMod 314954641) ^ 51262 = (17 : ZMod 314954641) ^ (25631 + 25631) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 25631 * (17 : ZMod 314954641) ^ 25631 := by rw [pow_add]
          _ = 120864149 := by rw [factor_1_14]; decide
      have factor_1_16 : (17 : ZMod 314954641) ^ 102524 = 132566707 := by
        calc
          (17 : ZMod 314954641) ^ 102524 = (17 : ZMod 314954641) ^ (51262 + 51262) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 51262 * (17 : ZMod 314954641) ^ 51262 := by rw [pow_add]
          _ = 132566707 := by rw [factor_1_15]; decide
      have factor_1_17 : (17 : ZMod 314954641) ^ 205048 = 149641395 := by
        calc
          (17 : ZMod 314954641) ^ 205048 = (17 : ZMod 314954641) ^ (102524 + 102524) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 102524 * (17 : ZMod 314954641) ^ 102524 := by rw [pow_add]
          _ = 149641395 := by rw [factor_1_16]; decide
      have factor_1_18 : (17 : ZMod 314954641) ^ 410097 = 19518033 := by
        calc
          (17 : ZMod 314954641) ^ 410097 = (17 : ZMod 314954641) ^ (205048 + 205048 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 205048 * (17 : ZMod 314954641) ^ 205048) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 19518033 := by rw [factor_1_17]; decide
      have factor_1_19 : (17 : ZMod 314954641) ^ 820194 = 226167539 := by
        calc
          (17 : ZMod 314954641) ^ 820194 = (17 : ZMod 314954641) ^ (410097 + 410097) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 410097 * (17 : ZMod 314954641) ^ 410097 := by rw [pow_add]
          _ = 226167539 := by rw [factor_1_18]; decide
      have factor_1_20 : (17 : ZMod 314954641) ^ 1640388 = 168514929 := by
        calc
          (17 : ZMod 314954641) ^ 1640388 = (17 : ZMod 314954641) ^ (820194 + 820194) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 820194 * (17 : ZMod 314954641) ^ 820194 := by rw [pow_add]
          _ = 168514929 := by rw [factor_1_19]; decide
      have factor_1_21 : (17 : ZMod 314954641) ^ 3280777 = 108303374 := by
        calc
          (17 : ZMod 314954641) ^ 3280777 = (17 : ZMod 314954641) ^ (1640388 + 1640388 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1640388 * (17 : ZMod 314954641) ^ 1640388) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 108303374 := by rw [factor_1_20]; decide
      have factor_1_22 : (17 : ZMod 314954641) ^ 6561555 = 120293490 := by
        calc
          (17 : ZMod 314954641) ^ 6561555 = (17 : ZMod 314954641) ^ (3280777 + 3280777 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 3280777 * (17 : ZMod 314954641) ^ 3280777) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 120293490 := by rw [factor_1_21]; decide
      have factor_1_23 : (17 : ZMod 314954641) ^ 13123110 = 155928274 := by
        calc
          (17 : ZMod 314954641) ^ 13123110 = (17 : ZMod 314954641) ^ (6561555 + 6561555) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 6561555 * (17 : ZMod 314954641) ^ 6561555 := by rw [pow_add]
          _ = 155928274 := by rw [factor_1_22]; decide
      have factor_1_24 : (17 : ZMod 314954641) ^ 26246220 = 141865364 := by
        calc
          (17 : ZMod 314954641) ^ 26246220 = (17 : ZMod 314954641) ^ (13123110 + 13123110) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 13123110 * (17 : ZMod 314954641) ^ 13123110 := by rw [pow_add]
          _ = 141865364 := by rw [factor_1_23]; decide
      have factor_1_25 : (17 : ZMod 314954641) ^ 52492440 = 103852485 := by
        calc
          (17 : ZMod 314954641) ^ 52492440 = (17 : ZMod 314954641) ^ (26246220 + 26246220) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 26246220 * (17 : ZMod 314954641) ^ 26246220 := by rw [pow_add]
          _ = 103852485 := by rw [factor_1_24]; decide
      have factor_1_26 : (17 : ZMod 314954641) ^ 104984880 = 103852484 := by
        calc
          (17 : ZMod 314954641) ^ 104984880 = (17 : ZMod 314954641) ^ (52492440 + 52492440) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 52492440 * (17 : ZMod 314954641) ^ 52492440 := by rw [pow_add]
          _ = 103852484 := by rw [factor_1_25]; decide
      change (17 : ZMod 314954641) ^ 104984880 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (17 : ZMod 314954641) ^ 1 = 17 := by norm_num
      have factor_2_1 : (17 : ZMod 314954641) ^ 3 = 4913 := by
        calc
          (17 : ZMod 314954641) ^ 3 = (17 : ZMod 314954641) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1 * (17 : ZMod 314954641) ^ 1) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_2_0]; decide
      have factor_2_2 : (17 : ZMod 314954641) ^ 7 = 95384032 := by
        calc
          (17 : ZMod 314954641) ^ 7 = (17 : ZMod 314954641) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 3 * (17 : ZMod 314954641) ^ 3) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 95384032 := by rw [factor_2_1]; decide
      have factor_2_3 : (17 : ZMod 314954641) ^ 15 = 73300511 := by
        calc
          (17 : ZMod 314954641) ^ 15 = (17 : ZMod 314954641) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 7 * (17 : ZMod 314954641) ^ 7) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 73300511 := by rw [factor_2_2]; decide
      have factor_2_4 : (17 : ZMod 314954641) ^ 30 = 309131954 := by
        calc
          (17 : ZMod 314954641) ^ 30 = (17 : ZMod 314954641) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 15 * (17 : ZMod 314954641) ^ 15 := by rw [pow_add]
          _ = 309131954 := by rw [factor_2_3]; decide
      have factor_2_5 : (17 : ZMod 314954641) ^ 60 = 76614883 := by
        calc
          (17 : ZMod 314954641) ^ 60 = (17 : ZMod 314954641) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 30 * (17 : ZMod 314954641) ^ 30 := by rw [pow_add]
          _ = 76614883 := by rw [factor_2_4]; decide
      have factor_2_6 : (17 : ZMod 314954641) ^ 120 = 102186512 := by
        calc
          (17 : ZMod 314954641) ^ 120 = (17 : ZMod 314954641) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 60 * (17 : ZMod 314954641) ^ 60 := by rw [pow_add]
          _ = 102186512 := by rw [factor_2_5]; decide
      have factor_2_7 : (17 : ZMod 314954641) ^ 240 = 218079740 := by
        calc
          (17 : ZMod 314954641) ^ 240 = (17 : ZMod 314954641) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 120 * (17 : ZMod 314954641) ^ 120 := by rw [pow_add]
          _ = 218079740 := by rw [factor_2_6]; decide
      have factor_2_8 : (17 : ZMod 314954641) ^ 480 = 172051625 := by
        calc
          (17 : ZMod 314954641) ^ 480 = (17 : ZMod 314954641) ^ (240 + 240) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 240 * (17 : ZMod 314954641) ^ 240 := by rw [pow_add]
          _ = 172051625 := by rw [factor_2_7]; decide
      have factor_2_9 : (17 : ZMod 314954641) ^ 961 = 153388278 := by
        calc
          (17 : ZMod 314954641) ^ 961 = (17 : ZMod 314954641) ^ (480 + 480 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 480 * (17 : ZMod 314954641) ^ 480) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 153388278 := by rw [factor_2_8]; decide
      have factor_2_10 : (17 : ZMod 314954641) ^ 1922 = 192801379 := by
        calc
          (17 : ZMod 314954641) ^ 1922 = (17 : ZMod 314954641) ^ (961 + 961) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 961 * (17 : ZMod 314954641) ^ 961 := by rw [pow_add]
          _ = 192801379 := by rw [factor_2_9]; decide
      have factor_2_11 : (17 : ZMod 314954641) ^ 3844 = 158685757 := by
        calc
          (17 : ZMod 314954641) ^ 3844 = (17 : ZMod 314954641) ^ (1922 + 1922) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1922 * (17 : ZMod 314954641) ^ 1922 := by rw [pow_add]
          _ = 158685757 := by rw [factor_2_10]; decide
      have factor_2_12 : (17 : ZMod 314954641) ^ 7689 = 300670127 := by
        calc
          (17 : ZMod 314954641) ^ 7689 = (17 : ZMod 314954641) ^ (3844 + 3844 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 3844 * (17 : ZMod 314954641) ^ 3844) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 300670127 := by rw [factor_2_11]; decide
      have factor_2_13 : (17 : ZMod 314954641) ^ 15378 = 196588654 := by
        calc
          (17 : ZMod 314954641) ^ 15378 = (17 : ZMod 314954641) ^ (7689 + 7689) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 7689 * (17 : ZMod 314954641) ^ 7689 := by rw [pow_add]
          _ = 196588654 := by rw [factor_2_12]; decide
      have factor_2_14 : (17 : ZMod 314954641) ^ 30757 = 118295065 := by
        calc
          (17 : ZMod 314954641) ^ 30757 = (17 : ZMod 314954641) ^ (15378 + 15378 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 15378 * (17 : ZMod 314954641) ^ 15378) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 118295065 := by rw [factor_2_13]; decide
      have factor_2_15 : (17 : ZMod 314954641) ^ 61514 = 150136992 := by
        calc
          (17 : ZMod 314954641) ^ 61514 = (17 : ZMod 314954641) ^ (30757 + 30757) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 30757 * (17 : ZMod 314954641) ^ 30757 := by rw [pow_add]
          _ = 150136992 := by rw [factor_2_14]; decide
      have factor_2_16 : (17 : ZMod 314954641) ^ 123029 = 268867598 := by
        calc
          (17 : ZMod 314954641) ^ 123029 = (17 : ZMod 314954641) ^ (61514 + 61514 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 61514 * (17 : ZMod 314954641) ^ 61514) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 268867598 := by rw [factor_2_15]; decide
      have factor_2_17 : (17 : ZMod 314954641) ^ 246058 = 173000692 := by
        calc
          (17 : ZMod 314954641) ^ 246058 = (17 : ZMod 314954641) ^ (123029 + 123029) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 123029 * (17 : ZMod 314954641) ^ 123029 := by rw [pow_add]
          _ = 173000692 := by rw [factor_2_16]; decide
      have factor_2_18 : (17 : ZMod 314954641) ^ 492116 = 38612842 := by
        calc
          (17 : ZMod 314954641) ^ 492116 = (17 : ZMod 314954641) ^ (246058 + 246058) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 246058 * (17 : ZMod 314954641) ^ 246058 := by rw [pow_add]
          _ = 38612842 := by rw [factor_2_17]; decide
      have factor_2_19 : (17 : ZMod 314954641) ^ 984233 = 23988507 := by
        calc
          (17 : ZMod 314954641) ^ 984233 = (17 : ZMod 314954641) ^ (492116 + 492116 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 492116 * (17 : ZMod 314954641) ^ 492116) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 23988507 := by rw [factor_2_18]; decide
      have factor_2_20 : (17 : ZMod 314954641) ^ 1968466 = 197746846 := by
        calc
          (17 : ZMod 314954641) ^ 1968466 = (17 : ZMod 314954641) ^ (984233 + 984233) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 984233 * (17 : ZMod 314954641) ^ 984233 := by rw [pow_add]
          _ = 197746846 := by rw [factor_2_19]; decide
      have factor_2_21 : (17 : ZMod 314954641) ^ 3936933 = 55052058 := by
        calc
          (17 : ZMod 314954641) ^ 3936933 = (17 : ZMod 314954641) ^ (1968466 + 1968466 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1968466 * (17 : ZMod 314954641) ^ 1968466) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 55052058 := by rw [factor_2_20]; decide
      have factor_2_22 : (17 : ZMod 314954641) ^ 7873866 = 263216537 := by
        calc
          (17 : ZMod 314954641) ^ 7873866 = (17 : ZMod 314954641) ^ (3936933 + 3936933) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 3936933 * (17 : ZMod 314954641) ^ 3936933 := by rw [pow_add]
          _ = 263216537 := by rw [factor_2_21]; decide
      have factor_2_23 : (17 : ZMod 314954641) ^ 15747732 = 101237075 := by
        calc
          (17 : ZMod 314954641) ^ 15747732 = (17 : ZMod 314954641) ^ (7873866 + 7873866) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 7873866 * (17 : ZMod 314954641) ^ 7873866 := by rw [pow_add]
          _ = 101237075 := by rw [factor_2_22]; decide
      have factor_2_24 : (17 : ZMod 314954641) ^ 31495464 = 82681805 := by
        calc
          (17 : ZMod 314954641) ^ 31495464 = (17 : ZMod 314954641) ^ (15747732 + 15747732) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 15747732 * (17 : ZMod 314954641) ^ 15747732 := by rw [pow_add]
          _ = 82681805 := by rw [factor_2_23]; decide
      have factor_2_25 : (17 : ZMod 314954641) ^ 62990928 = 162549861 := by
        calc
          (17 : ZMod 314954641) ^ 62990928 = (17 : ZMod 314954641) ^ (31495464 + 31495464) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 31495464 * (17 : ZMod 314954641) ^ 31495464 := by rw [pow_add]
          _ = 162549861 := by rw [factor_2_24]; decide
      change (17 : ZMod 314954641) ^ 62990928 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (17 : ZMod 314954641) ^ 1 = 17 := by norm_num
      have factor_3_1 : (17 : ZMod 314954641) ^ 2 = 289 := by
        calc
          (17 : ZMod 314954641) ^ 2 = (17 : ZMod 314954641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1 * (17 : ZMod 314954641) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_3_0]; decide
      have factor_3_2 : (17 : ZMod 314954641) ^ 5 = 1419857 := by
        calc
          (17 : ZMod 314954641) ^ 5 = (17 : ZMod 314954641) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 2 * (17 : ZMod 314954641) ^ 2) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 1419857 := by rw [factor_3_1]; decide
      have factor_3_3 : (17 : ZMod 314954641) ^ 10 = 284198049 := by
        calc
          (17 : ZMod 314954641) ^ 10 = (17 : ZMod 314954641) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 5 * (17 : ZMod 314954641) ^ 5 := by rw [pow_add]
          _ = 284198049 := by rw [factor_3_2]; decide
      have factor_3_4 : (17 : ZMod 314954641) ^ 21 = 21714057 := by
        calc
          (17 : ZMod 314954641) ^ 21 = (17 : ZMod 314954641) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 10 * (17 : ZMod 314954641) ^ 10) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 21714057 := by rw [factor_3_3]; decide
      have factor_3_5 : (17 : ZMod 314954641) ^ 42 = 260681968 := by
        calc
          (17 : ZMod 314954641) ^ 42 = (17 : ZMod 314954641) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 21 * (17 : ZMod 314954641) ^ 21 := by rw [pow_add]
          _ = 260681968 := by rw [factor_3_4]; decide
      have factor_3_6 : (17 : ZMod 314954641) ^ 85 = 287422245 := by
        calc
          (17 : ZMod 314954641) ^ 85 = (17 : ZMod 314954641) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 42 * (17 : ZMod 314954641) ^ 42) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 287422245 := by rw [factor_3_5]; decide
      have factor_3_7 : (17 : ZMod 314954641) ^ 171 = 307168913 := by
        calc
          (17 : ZMod 314954641) ^ 171 = (17 : ZMod 314954641) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 85 * (17 : ZMod 314954641) ^ 85) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 307168913 := by rw [factor_3_6]; decide
      have factor_3_8 : (17 : ZMod 314954641) ^ 343 = 13215033 := by
        calc
          (17 : ZMod 314954641) ^ 343 = (17 : ZMod 314954641) ^ (171 + 171 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 171 * (17 : ZMod 314954641) ^ 171) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 13215033 := by rw [factor_3_7]; decide
      have factor_3_9 : (17 : ZMod 314954641) ^ 686 = 102985486 := by
        calc
          (17 : ZMod 314954641) ^ 686 = (17 : ZMod 314954641) ^ (343 + 343) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 343 * (17 : ZMod 314954641) ^ 343 := by rw [pow_add]
          _ = 102985486 := by rw [factor_3_8]; decide
      have factor_3_10 : (17 : ZMod 314954641) ^ 1373 = 253130160 := by
        calc
          (17 : ZMod 314954641) ^ 1373 = (17 : ZMod 314954641) ^ (686 + 686 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 686 * (17 : ZMod 314954641) ^ 686) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 253130160 := by rw [factor_3_9]; decide
      have factor_3_11 : (17 : ZMod 314954641) ^ 2746 = 234386795 := by
        calc
          (17 : ZMod 314954641) ^ 2746 = (17 : ZMod 314954641) ^ (1373 + 1373) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1373 * (17 : ZMod 314954641) ^ 1373 := by rw [pow_add]
          _ = 234386795 := by rw [factor_3_10]; decide
      have factor_3_12 : (17 : ZMod 314954641) ^ 5492 = 137671995 := by
        calc
          (17 : ZMod 314954641) ^ 5492 = (17 : ZMod 314954641) ^ (2746 + 2746) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 2746 * (17 : ZMod 314954641) ^ 2746 := by rw [pow_add]
          _ = 137671995 := by rw [factor_3_11]; decide
      have factor_3_13 : (17 : ZMod 314954641) ^ 10984 = 30428070 := by
        calc
          (17 : ZMod 314954641) ^ 10984 = (17 : ZMod 314954641) ^ (5492 + 5492) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 5492 * (17 : ZMod 314954641) ^ 5492 := by rw [pow_add]
          _ = 30428070 := by rw [factor_3_12]; decide
      have factor_3_14 : (17 : ZMod 314954641) ^ 21969 = 171645855 := by
        calc
          (17 : ZMod 314954641) ^ 21969 = (17 : ZMod 314954641) ^ (10984 + 10984 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 10984 * (17 : ZMod 314954641) ^ 10984) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 171645855 := by rw [factor_3_13]; decide
      have factor_3_15 : (17 : ZMod 314954641) ^ 43938 = 242239886 := by
        calc
          (17 : ZMod 314954641) ^ 43938 = (17 : ZMod 314954641) ^ (21969 + 21969) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 21969 * (17 : ZMod 314954641) ^ 21969 := by rw [pow_add]
          _ = 242239886 := by rw [factor_3_14]; decide
      have factor_3_16 : (17 : ZMod 314954641) ^ 87877 = 301079983 := by
        calc
          (17 : ZMod 314954641) ^ 87877 = (17 : ZMod 314954641) ^ (43938 + 43938 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 43938 * (17 : ZMod 314954641) ^ 43938) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 301079983 := by rw [factor_3_15]; decide
      have factor_3_17 : (17 : ZMod 314954641) ^ 175755 = 60975432 := by
        calc
          (17 : ZMod 314954641) ^ 175755 = (17 : ZMod 314954641) ^ (87877 + 87877 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 87877 * (17 : ZMod 314954641) ^ 87877) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 60975432 := by rw [factor_3_16]; decide
      have factor_3_18 : (17 : ZMod 314954641) ^ 351511 = 151165404 := by
        calc
          (17 : ZMod 314954641) ^ 351511 = (17 : ZMod 314954641) ^ (175755 + 175755 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 175755 * (17 : ZMod 314954641) ^ 175755) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 151165404 := by rw [factor_3_17]; decide
      have factor_3_19 : (17 : ZMod 314954641) ^ 703023 = 90512648 := by
        calc
          (17 : ZMod 314954641) ^ 703023 = (17 : ZMod 314954641) ^ (351511 + 351511 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 351511 * (17 : ZMod 314954641) ^ 351511) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 90512648 := by rw [factor_3_18]; decide
      have factor_3_20 : (17 : ZMod 314954641) ^ 1406047 = 23207643 := by
        calc
          (17 : ZMod 314954641) ^ 1406047 = (17 : ZMod 314954641) ^ (703023 + 703023 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 703023 * (17 : ZMod 314954641) ^ 703023) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 23207643 := by rw [factor_3_19]; decide
      have factor_3_21 : (17 : ZMod 314954641) ^ 2812095 = 117068792 := by
        calc
          (17 : ZMod 314954641) ^ 2812095 = (17 : ZMod 314954641) ^ (1406047 + 1406047 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1406047 * (17 : ZMod 314954641) ^ 1406047) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 117068792 := by rw [factor_3_20]; decide
      have factor_3_22 : (17 : ZMod 314954641) ^ 5624190 = 145724098 := by
        calc
          (17 : ZMod 314954641) ^ 5624190 = (17 : ZMod 314954641) ^ (2812095 + 2812095) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 2812095 * (17 : ZMod 314954641) ^ 2812095 := by rw [pow_add]
          _ = 145724098 := by rw [factor_3_21]; decide
      have factor_3_23 : (17 : ZMod 314954641) ^ 11248380 = 314671810 := by
        calc
          (17 : ZMod 314954641) ^ 11248380 = (17 : ZMod 314954641) ^ (5624190 + 5624190) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 5624190 * (17 : ZMod 314954641) ^ 5624190 := by rw [pow_add]
          _ = 314671810 := by rw [factor_3_22]; decide
      have factor_3_24 : (17 : ZMod 314954641) ^ 22496760 = 309850388 := by
        calc
          (17 : ZMod 314954641) ^ 22496760 = (17 : ZMod 314954641) ^ (11248380 + 11248380) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 11248380 * (17 : ZMod 314954641) ^ 11248380 := by rw [pow_add]
          _ = 309850388 := by rw [factor_3_23]; decide
      have factor_3_25 : (17 : ZMod 314954641) ^ 44993520 = 35829848 := by
        calc
          (17 : ZMod 314954641) ^ 44993520 = (17 : ZMod 314954641) ^ (22496760 + 22496760) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 22496760 * (17 : ZMod 314954641) ^ 22496760 := by rw [pow_add]
          _ = 35829848 := by rw [factor_3_24]; decide
      change (17 : ZMod 314954641) ^ 44993520 ≠ 1
      rw [factor_3_25]
      decide
    ·
      have factor_4_0 : (17 : ZMod 314954641) ^ 1 = 17 := by norm_num
      have factor_4_1 : (17 : ZMod 314954641) ^ 3 = 4913 := by
        calc
          (17 : ZMod 314954641) ^ 3 = (17 : ZMod 314954641) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1 * (17 : ZMod 314954641) ^ 1) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_4_0]; decide
      have factor_4_2 : (17 : ZMod 314954641) ^ 6 = 24137569 := by
        calc
          (17 : ZMod 314954641) ^ 6 = (17 : ZMod 314954641) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 3 * (17 : ZMod 314954641) ^ 3 := by rw [pow_add]
          _ = 24137569 := by rw [factor_4_1]; decide
      have factor_4_3 : (17 : ZMod 314954641) ^ 13 = 71091184 := by
        calc
          (17 : ZMod 314954641) ^ 13 = (17 : ZMod 314954641) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 6 * (17 : ZMod 314954641) ^ 6) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 71091184 := by rw [factor_4_2]; decide
      have factor_4_4 : (17 : ZMod 314954641) ^ 27 = 27244026 := by
        calc
          (17 : ZMod 314954641) ^ 27 = (17 : ZMod 314954641) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 13 * (17 : ZMod 314954641) ^ 13) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 27244026 := by rw [factor_4_3]; decide
      have factor_4_5 : (17 : ZMod 314954641) ^ 54 = 42839949 := by
        calc
          (17 : ZMod 314954641) ^ 54 = (17 : ZMod 314954641) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 27 * (17 : ZMod 314954641) ^ 27 := by rw [pow_add]
          _ = 42839949 := by rw [factor_4_4]; decide
      have factor_4_6 : (17 : ZMod 314954641) ^ 109 = 162922989 := by
        calc
          (17 : ZMod 314954641) ^ 109 = (17 : ZMod 314954641) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 54 * (17 : ZMod 314954641) ^ 54) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 162922989 := by rw [factor_4_5]; decide
      have factor_4_7 : (17 : ZMod 314954641) ^ 218 = 42540595 := by
        calc
          (17 : ZMod 314954641) ^ 218 = (17 : ZMod 314954641) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 109 * (17 : ZMod 314954641) ^ 109 := by rw [pow_add]
          _ = 42540595 := by rw [factor_4_6]; decide
      have factor_4_8 : (17 : ZMod 314954641) ^ 436 = 256821792 := by
        calc
          (17 : ZMod 314954641) ^ 436 = (17 : ZMod 314954641) ^ (218 + 218) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 218 * (17 : ZMod 314954641) ^ 218 := by rw [pow_add]
          _ = 256821792 := by rw [factor_4_7]; decide
      have factor_4_9 : (17 : ZMod 314954641) ^ 873 = 292618876 := by
        calc
          (17 : ZMod 314954641) ^ 873 = (17 : ZMod 314954641) ^ (436 + 436 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 436 * (17 : ZMod 314954641) ^ 436) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 292618876 := by rw [factor_4_8]; decide
      have factor_4_10 : (17 : ZMod 314954641) ^ 1747 = 116141720 := by
        calc
          (17 : ZMod 314954641) ^ 1747 = (17 : ZMod 314954641) ^ (873 + 873 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 873 * (17 : ZMod 314954641) ^ 873) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 116141720 := by rw [factor_4_9]; decide
      have factor_4_11 : (17 : ZMod 314954641) ^ 3495 = 160028266 := by
        calc
          (17 : ZMod 314954641) ^ 3495 = (17 : ZMod 314954641) ^ (1747 + 1747 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1747 * (17 : ZMod 314954641) ^ 1747) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 160028266 := by rw [factor_4_10]; decide
      have factor_4_12 : (17 : ZMod 314954641) ^ 6990 = 281322250 := by
        calc
          (17 : ZMod 314954641) ^ 6990 = (17 : ZMod 314954641) ^ (3495 + 3495) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 3495 * (17 : ZMod 314954641) ^ 3495 := by rw [pow_add]
          _ = 281322250 := by rw [factor_4_11]; decide
      have factor_4_13 : (17 : ZMod 314954641) ^ 13980 = 178050251 := by
        calc
          (17 : ZMod 314954641) ^ 13980 = (17 : ZMod 314954641) ^ (6990 + 6990) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 6990 * (17 : ZMod 314954641) ^ 6990 := by rw [pow_add]
          _ = 178050251 := by rw [factor_4_12]; decide
      have factor_4_14 : (17 : ZMod 314954641) ^ 27961 = 111598226 := by
        calc
          (17 : ZMod 314954641) ^ 27961 = (17 : ZMod 314954641) ^ (13980 + 13980 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 13980 * (17 : ZMod 314954641) ^ 13980) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 111598226 := by rw [factor_4_13]; decide
      have factor_4_15 : (17 : ZMod 314954641) ^ 55922 = 234674274 := by
        calc
          (17 : ZMod 314954641) ^ 55922 = (17 : ZMod 314954641) ^ (27961 + 27961) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 27961 * (17 : ZMod 314954641) ^ 27961 := by rw [pow_add]
          _ = 234674274 := by rw [factor_4_14]; decide
      have factor_4_16 : (17 : ZMod 314954641) ^ 111844 = 34820024 := by
        calc
          (17 : ZMod 314954641) ^ 111844 = (17 : ZMod 314954641) ^ (55922 + 55922) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 55922 * (17 : ZMod 314954641) ^ 55922 := by rw [pow_add]
          _ = 34820024 := by rw [factor_4_15]; decide
      have factor_4_17 : (17 : ZMod 314954641) ^ 223689 = 118726699 := by
        calc
          (17 : ZMod 314954641) ^ 223689 = (17 : ZMod 314954641) ^ (111844 + 111844 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 111844 * (17 : ZMod 314954641) ^ 111844) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 118726699 := by rw [factor_4_16]; decide
      have factor_4_18 : (17 : ZMod 314954641) ^ 447378 = 86183338 := by
        calc
          (17 : ZMod 314954641) ^ 447378 = (17 : ZMod 314954641) ^ (223689 + 223689) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 223689 * (17 : ZMod 314954641) ^ 223689 := by rw [pow_add]
          _ = 86183338 := by rw [factor_4_17]; decide
      have factor_4_19 : (17 : ZMod 314954641) ^ 894757 = 153520676 := by
        calc
          (17 : ZMod 314954641) ^ 894757 = (17 : ZMod 314954641) ^ (447378 + 447378 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 447378 * (17 : ZMod 314954641) ^ 447378) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 153520676 := by rw [factor_4_18]; decide
      have factor_4_20 : (17 : ZMod 314954641) ^ 1789515 = 116324368 := by
        calc
          (17 : ZMod 314954641) ^ 1789515 = (17 : ZMod 314954641) ^ (894757 + 894757 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 894757 * (17 : ZMod 314954641) ^ 894757) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 116324368 := by rw [factor_4_19]; decide
      have factor_4_21 : (17 : ZMod 314954641) ^ 3579030 = 143873344 := by
        calc
          (17 : ZMod 314954641) ^ 3579030 = (17 : ZMod 314954641) ^ (1789515 + 1789515) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1789515 * (17 : ZMod 314954641) ^ 1789515 := by rw [pow_add]
          _ = 143873344 := by rw [factor_4_20]; decide
      have factor_4_22 : (17 : ZMod 314954641) ^ 7158060 = 120913010 := by
        calc
          (17 : ZMod 314954641) ^ 7158060 = (17 : ZMod 314954641) ^ (3579030 + 3579030) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 3579030 * (17 : ZMod 314954641) ^ 3579030 := by rw [pow_add]
          _ = 120913010 := by rw [factor_4_21]; decide
      have factor_4_23 : (17 : ZMod 314954641) ^ 14316120 = 287657978 := by
        calc
          (17 : ZMod 314954641) ^ 14316120 = (17 : ZMod 314954641) ^ (7158060 + 7158060) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 7158060 * (17 : ZMod 314954641) ^ 7158060 := by rw [pow_add]
          _ = 287657978 := by rw [factor_4_22]; decide
      have factor_4_24 : (17 : ZMod 314954641) ^ 28632240 = 89534127 := by
        calc
          (17 : ZMod 314954641) ^ 28632240 = (17 : ZMod 314954641) ^ (14316120 + 14316120) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 14316120 * (17 : ZMod 314954641) ^ 14316120 := by rw [pow_add]
          _ = 89534127 := by rw [factor_4_23]; decide
      change (17 : ZMod 314954641) ^ 28632240 ≠ 1
      rw [factor_4_24]
      decide
    ·
      have factor_5_0 : (17 : ZMod 314954641) ^ 1 = 17 := by norm_num
      have factor_5_1 : (17 : ZMod 314954641) ^ 2 = 289 := by
        calc
          (17 : ZMod 314954641) ^ 2 = (17 : ZMod 314954641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1 * (17 : ZMod 314954641) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_5_0]; decide
      have factor_5_2 : (17 : ZMod 314954641) ^ 5 = 1419857 := by
        calc
          (17 : ZMod 314954641) ^ 5 = (17 : ZMod 314954641) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 2 * (17 : ZMod 314954641) ^ 2) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 1419857 := by rw [factor_5_1]; decide
      have factor_5_3 : (17 : ZMod 314954641) ^ 11 = 107047218 := by
        calc
          (17 : ZMod 314954641) ^ 11 = (17 : ZMod 314954641) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 5 * (17 : ZMod 314954641) ^ 5) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 107047218 := by rw [factor_5_2]; decide
      have factor_5_4 : (17 : ZMod 314954641) ^ 23 = 291224294 := by
        calc
          (17 : ZMod 314954641) ^ 23 = (17 : ZMod 314954641) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 11 * (17 : ZMod 314954641) ^ 11) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 291224294 := by rw [factor_5_3]; decide
      have factor_5_5 : (17 : ZMod 314954641) ^ 46 = 234226280 := by
        calc
          (17 : ZMod 314954641) ^ 46 = (17 : ZMod 314954641) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 23 * (17 : ZMod 314954641) ^ 23 := by rw [pow_add]
          _ = 234226280 := by rw [factor_5_4]; decide
      have factor_5_6 : (17 : ZMod 314954641) ^ 92 = 67029836 := by
        calc
          (17 : ZMod 314954641) ^ 92 = (17 : ZMod 314954641) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 46 * (17 : ZMod 314954641) ^ 46 := by rw [pow_add]
          _ = 67029836 := by rw [factor_5_5]; decide
      have factor_5_7 : (17 : ZMod 314954641) ^ 184 = 254906474 := by
        calc
          (17 : ZMod 314954641) ^ 184 = (17 : ZMod 314954641) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 92 * (17 : ZMod 314954641) ^ 92 := by rw [pow_add]
          _ = 254906474 := by rw [factor_5_6]; decide
      have factor_5_8 : (17 : ZMod 314954641) ^ 369 = 207816390 := by
        calc
          (17 : ZMod 314954641) ^ 369 = (17 : ZMod 314954641) ^ (184 + 184 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 184 * (17 : ZMod 314954641) ^ 184) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 207816390 := by rw [factor_5_7]; decide
      have factor_5_9 : (17 : ZMod 314954641) ^ 739 = 176624901 := by
        calc
          (17 : ZMod 314954641) ^ 739 = (17 : ZMod 314954641) ^ (369 + 369 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 369 * (17 : ZMod 314954641) ^ 369) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 176624901 := by rw [factor_5_8]; decide
      have factor_5_10 : (17 : ZMod 314954641) ^ 1478 = 196361809 := by
        calc
          (17 : ZMod 314954641) ^ 1478 = (17 : ZMod 314954641) ^ (739 + 739) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 739 * (17 : ZMod 314954641) ^ 739 := by rw [pow_add]
          _ = 196361809 := by rw [factor_5_9]; decide
      have factor_5_11 : (17 : ZMod 314954641) ^ 2957 = 182524471 := by
        calc
          (17 : ZMod 314954641) ^ 2957 = (17 : ZMod 314954641) ^ (1478 + 1478 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1478 * (17 : ZMod 314954641) ^ 1478) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 182524471 := by rw [factor_5_10]; decide
      have factor_5_12 : (17 : ZMod 314954641) ^ 5914 = 260204526 := by
        calc
          (17 : ZMod 314954641) ^ 5914 = (17 : ZMod 314954641) ^ (2957 + 2957) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 2957 * (17 : ZMod 314954641) ^ 2957 := by rw [pow_add]
          _ = 260204526 := by rw [factor_5_11]; decide
      have factor_5_13 : (17 : ZMod 314954641) ^ 11829 = 51556753 := by
        calc
          (17 : ZMod 314954641) ^ 11829 = (17 : ZMod 314954641) ^ (5914 + 5914 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 5914 * (17 : ZMod 314954641) ^ 5914) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 51556753 := by rw [factor_5_12]; decide
      have factor_5_14 : (17 : ZMod 314954641) ^ 23659 = 242781784 := by
        calc
          (17 : ZMod 314954641) ^ 23659 = (17 : ZMod 314954641) ^ (11829 + 11829 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 11829 * (17 : ZMod 314954641) ^ 11829) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 242781784 := by rw [factor_5_13]; decide
      have factor_5_15 : (17 : ZMod 314954641) ^ 47318 = 178668850 := by
        calc
          (17 : ZMod 314954641) ^ 47318 = (17 : ZMod 314954641) ^ (23659 + 23659) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 23659 * (17 : ZMod 314954641) ^ 23659 := by rw [pow_add]
          _ = 178668850 := by rw [factor_5_14]; decide
      have factor_5_16 : (17 : ZMod 314954641) ^ 94637 = 143753111 := by
        calc
          (17 : ZMod 314954641) ^ 94637 = (17 : ZMod 314954641) ^ (47318 + 47318 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 47318 * (17 : ZMod 314954641) ^ 47318) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 143753111 := by rw [factor_5_15]; decide
      have factor_5_17 : (17 : ZMod 314954641) ^ 189275 = 76687438 := by
        calc
          (17 : ZMod 314954641) ^ 189275 = (17 : ZMod 314954641) ^ (94637 + 94637 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 94637 * (17 : ZMod 314954641) ^ 94637) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 76687438 := by rw [factor_5_16]; decide
      have factor_5_18 : (17 : ZMod 314954641) ^ 378551 = 237746887 := by
        calc
          (17 : ZMod 314954641) ^ 378551 = (17 : ZMod 314954641) ^ (189275 + 189275 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 189275 * (17 : ZMod 314954641) ^ 189275) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 237746887 := by rw [factor_5_17]; decide
      have factor_5_19 : (17 : ZMod 314954641) ^ 757102 = 76777943 := by
        calc
          (17 : ZMod 314954641) ^ 757102 = (17 : ZMod 314954641) ^ (378551 + 378551) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 378551 * (17 : ZMod 314954641) ^ 378551 := by rw [pow_add]
          _ = 76777943 := by rw [factor_5_18]; decide
      have factor_5_20 : (17 : ZMod 314954641) ^ 1514205 = 166342918 := by
        calc
          (17 : ZMod 314954641) ^ 1514205 = (17 : ZMod 314954641) ^ (757102 + 757102 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 757102 * (17 : ZMod 314954641) ^ 757102) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 166342918 := by rw [factor_5_19]; decide
      have factor_5_21 : (17 : ZMod 314954641) ^ 3028410 = 234858591 := by
        calc
          (17 : ZMod 314954641) ^ 3028410 = (17 : ZMod 314954641) ^ (1514205 + 1514205) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1514205 * (17 : ZMod 314954641) ^ 1514205 := by rw [pow_add]
          _ = 234858591 := by rw [factor_5_20]; decide
      have factor_5_22 : (17 : ZMod 314954641) ^ 6056820 = 2598890 := by
        calc
          (17 : ZMod 314954641) ^ 6056820 = (17 : ZMod 314954641) ^ (3028410 + 3028410) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 3028410 * (17 : ZMod 314954641) ^ 3028410 := by rw [pow_add]
          _ = 2598890 := by rw [factor_5_21]; decide
      have factor_5_23 : (17 : ZMod 314954641) ^ 12113640 = 26955855 := by
        calc
          (17 : ZMod 314954641) ^ 12113640 = (17 : ZMod 314954641) ^ (6056820 + 6056820) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 6056820 * (17 : ZMod 314954641) ^ 6056820 := by rw [pow_add]
          _ = 26955855 := by rw [factor_5_22]; decide
      have factor_5_24 : (17 : ZMod 314954641) ^ 24227280 = 124534129 := by
        calc
          (17 : ZMod 314954641) ^ 24227280 = (17 : ZMod 314954641) ^ (12113640 + 12113640) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 12113640 * (17 : ZMod 314954641) ^ 12113640 := by rw [pow_add]
          _ = 124534129 := by rw [factor_5_23]; decide
      change (17 : ZMod 314954641) ^ 24227280 ≠ 1
      rw [factor_5_24]
      decide
    ·
      have factor_6_0 : (17 : ZMod 314954641) ^ 1 = 17 := by norm_num
      have factor_6_1 : (17 : ZMod 314954641) ^ 3 = 4913 := by
        calc
          (17 : ZMod 314954641) ^ 3 = (17 : ZMod 314954641) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1 * (17 : ZMod 314954641) ^ 1) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_6_0]; decide
      have factor_6_2 : (17 : ZMod 314954641) ^ 7 = 95384032 := by
        calc
          (17 : ZMod 314954641) ^ 7 = (17 : ZMod 314954641) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 3 * (17 : ZMod 314954641) ^ 3) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 95384032 := by rw [factor_6_1]; decide
      have factor_6_3 : (17 : ZMod 314954641) ^ 15 = 73300511 := by
        calc
          (17 : ZMod 314954641) ^ 15 = (17 : ZMod 314954641) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 7 * (17 : ZMod 314954641) ^ 7) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 73300511 := by rw [factor_6_2]; decide
      have factor_6_4 : (17 : ZMod 314954641) ^ 31 = 215968962 := by
        calc
          (17 : ZMod 314954641) ^ 31 = (17 : ZMod 314954641) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 15 * (17 : ZMod 314954641) ^ 15) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 215968962 := by rw [factor_6_3]; decide
      have factor_6_5 : (17 : ZMod 314954641) ^ 63 = 38124184 := by
        calc
          (17 : ZMod 314954641) ^ 63 = (17 : ZMod 314954641) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 31 * (17 : ZMod 314954641) ^ 31) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 38124184 := by rw [factor_6_4]; decide
      have factor_6_6 : (17 : ZMod 314954641) ^ 126 = 98469774 := by
        calc
          (17 : ZMod 314954641) ^ 126 = (17 : ZMod 314954641) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 63 * (17 : ZMod 314954641) ^ 63 := by rw [pow_add]
          _ = 98469774 := by rw [factor_6_5]; decide
      have factor_6_7 : (17 : ZMod 314954641) ^ 252 = 138572110 := by
        calc
          (17 : ZMod 314954641) ^ 252 = (17 : ZMod 314954641) ^ (126 + 126) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 126 * (17 : ZMod 314954641) ^ 126 := by rw [pow_add]
          _ = 138572110 := by rw [factor_6_6]; decide
      have factor_6_8 : (17 : ZMod 314954641) ^ 505 = 169075086 := by
        calc
          (17 : ZMod 314954641) ^ 505 = (17 : ZMod 314954641) ^ (252 + 252 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 252 * (17 : ZMod 314954641) ^ 252) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 169075086 := by rw [factor_6_7]; decide
      have factor_6_9 : (17 : ZMod 314954641) ^ 1011 = 310434359 := by
        calc
          (17 : ZMod 314954641) ^ 1011 = (17 : ZMod 314954641) ^ (505 + 505 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 505 * (17 : ZMod 314954641) ^ 505) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 310434359 := by rw [factor_6_8]; decide
      have factor_6_10 : (17 : ZMod 314954641) ^ 2023 = 130054059 := by
        calc
          (17 : ZMod 314954641) ^ 2023 = (17 : ZMod 314954641) ^ (1011 + 1011 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1011 * (17 : ZMod 314954641) ^ 1011) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 130054059 := by rw [factor_6_9]; decide
      have factor_6_11 : (17 : ZMod 314954641) ^ 4047 = 115174963 := by
        calc
          (17 : ZMod 314954641) ^ 4047 = (17 : ZMod 314954641) ^ (2023 + 2023 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 2023 * (17 : ZMod 314954641) ^ 2023) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 115174963 := by rw [factor_6_10]; decide
      have factor_6_12 : (17 : ZMod 314954641) ^ 8094 = 249182370 := by
        calc
          (17 : ZMod 314954641) ^ 8094 = (17 : ZMod 314954641) ^ (4047 + 4047) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 4047 * (17 : ZMod 314954641) ^ 4047 := by rw [pow_add]
          _ = 249182370 := by rw [factor_6_11]; decide
      have factor_6_13 : (17 : ZMod 314954641) ^ 16188 = 191244397 := by
        calc
          (17 : ZMod 314954641) ^ 16188 = (17 : ZMod 314954641) ^ (8094 + 8094) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 8094 * (17 : ZMod 314954641) ^ 8094 := by rw [pow_add]
          _ = 191244397 := by rw [factor_6_12]; decide
      have factor_6_14 : (17 : ZMod 314954641) ^ 32376 = 207628660 := by
        calc
          (17 : ZMod 314954641) ^ 32376 = (17 : ZMod 314954641) ^ (16188 + 16188) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 16188 * (17 : ZMod 314954641) ^ 16188 := by rw [pow_add]
          _ = 207628660 := by rw [factor_6_13]; decide
      have factor_6_15 : (17 : ZMod 314954641) ^ 64752 = 191628466 := by
        calc
          (17 : ZMod 314954641) ^ 64752 = (17 : ZMod 314954641) ^ (32376 + 32376) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 32376 * (17 : ZMod 314954641) ^ 32376 := by rw [pow_add]
          _ = 191628466 := by rw [factor_6_14]; decide
      have factor_6_16 : (17 : ZMod 314954641) ^ 129504 = 3002435 := by
        calc
          (17 : ZMod 314954641) ^ 129504 = (17 : ZMod 314954641) ^ (64752 + 64752) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 64752 * (17 : ZMod 314954641) ^ 64752 := by rw [pow_add]
          _ = 3002435 := by rw [factor_6_15]; decide
      have factor_6_17 : (17 : ZMod 314954641) ^ 259008 = 299149164 := by
        calc
          (17 : ZMod 314954641) ^ 259008 = (17 : ZMod 314954641) ^ (129504 + 129504) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 129504 * (17 : ZMod 314954641) ^ 129504 := by rw [pow_add]
          _ = 299149164 := by rw [factor_6_16]; decide
      have factor_6_18 : (17 : ZMod 314954641) ^ 518017 = 201394555 := by
        calc
          (17 : ZMod 314954641) ^ 518017 = (17 : ZMod 314954641) ^ (259008 + 259008 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 259008 * (17 : ZMod 314954641) ^ 259008) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 201394555 := by rw [factor_6_17]; decide
      have factor_6_19 : (17 : ZMod 314954641) ^ 1036035 = 141375785 := by
        calc
          (17 : ZMod 314954641) ^ 1036035 = (17 : ZMod 314954641) ^ (518017 + 518017 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 518017 * (17 : ZMod 314954641) ^ 518017) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 141375785 := by rw [factor_6_18]; decide
      have factor_6_20 : (17 : ZMod 314954641) ^ 2072070 = 44614976 := by
        calc
          (17 : ZMod 314954641) ^ 2072070 = (17 : ZMod 314954641) ^ (1036035 + 1036035) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1036035 * (17 : ZMod 314954641) ^ 1036035 := by rw [pow_add]
          _ = 44614976 := by rw [factor_6_19]; decide
      have factor_6_21 : (17 : ZMod 314954641) ^ 4144140 = 74865831 := by
        calc
          (17 : ZMod 314954641) ^ 4144140 = (17 : ZMod 314954641) ^ (2072070 + 2072070) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 2072070 * (17 : ZMod 314954641) ^ 2072070 := by rw [pow_add]
          _ = 74865831 := by rw [factor_6_20]; decide
      have factor_6_22 : (17 : ZMod 314954641) ^ 8288280 = 174278609 := by
        calc
          (17 : ZMod 314954641) ^ 8288280 = (17 : ZMod 314954641) ^ (4144140 + 4144140) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 4144140 * (17 : ZMod 314954641) ^ 4144140 := by rw [pow_add]
          _ = 174278609 := by rw [factor_6_21]; decide
      have factor_6_23 : (17 : ZMod 314954641) ^ 16576560 = 80251066 := by
        calc
          (17 : ZMod 314954641) ^ 16576560 = (17 : ZMod 314954641) ^ (8288280 + 8288280) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 8288280 * (17 : ZMod 314954641) ^ 8288280 := by rw [pow_add]
          _ = 80251066 := by rw [factor_6_22]; decide
      change (17 : ZMod 314954641) ^ 16576560 ≠ 1
      rw [factor_6_23]
      decide
    ·
      have factor_7_0 : (17 : ZMod 314954641) ^ 1 = 17 := by norm_num
      have factor_7_1 : (17 : ZMod 314954641) ^ 3 = 4913 := by
        calc
          (17 : ZMod 314954641) ^ 3 = (17 : ZMod 314954641) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1 * (17 : ZMod 314954641) ^ 1) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_7_0]; decide
      have factor_7_2 : (17 : ZMod 314954641) ^ 6 = 24137569 := by
        calc
          (17 : ZMod 314954641) ^ 6 = (17 : ZMod 314954641) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 3 * (17 : ZMod 314954641) ^ 3 := by rw [pow_add]
          _ = 24137569 := by rw [factor_7_1]; decide
      have factor_7_3 : (17 : ZMod 314954641) ^ 13 = 71091184 := by
        calc
          (17 : ZMod 314954641) ^ 13 = (17 : ZMod 314954641) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 6 * (17 : ZMod 314954641) ^ 6) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 71091184 := by rw [factor_7_2]; decide
      have factor_7_4 : (17 : ZMod 314954641) ^ 26 = 260977000 := by
        calc
          (17 : ZMod 314954641) ^ 26 = (17 : ZMod 314954641) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 13 * (17 : ZMod 314954641) ^ 13 := by rw [pow_add]
          _ = 260977000 := by rw [factor_7_3]; decide
      have factor_7_5 : (17 : ZMod 314954641) ^ 52 = 185415671 := by
        calc
          (17 : ZMod 314954641) ^ 52 = (17 : ZMod 314954641) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 26 * (17 : ZMod 314954641) ^ 26 := by rw [pow_add]
          _ = 185415671 := by rw [factor_7_4]; decide
      have factor_7_6 : (17 : ZMod 314954641) ^ 104 = 207995813 := by
        calc
          (17 : ZMod 314954641) ^ 104 = (17 : ZMod 314954641) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 52 * (17 : ZMod 314954641) ^ 52 := by rw [pow_add]
          _ = 207995813 := by rw [factor_7_5]; decide
      have factor_7_7 : (17 : ZMod 314954641) ^ 208 = 235516848 := by
        calc
          (17 : ZMod 314954641) ^ 208 = (17 : ZMod 314954641) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 104 * (17 : ZMod 314954641) ^ 104 := by rw [pow_add]
          _ = 235516848 := by rw [factor_7_6]; decide
      have factor_7_8 : (17 : ZMod 314954641) ^ 417 = 61735236 := by
        calc
          (17 : ZMod 314954641) ^ 417 = (17 : ZMod 314954641) ^ (208 + 208 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 208 * (17 : ZMod 314954641) ^ 208) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 61735236 := by rw [factor_7_7]; decide
      have factor_7_9 : (17 : ZMod 314954641) ^ 835 = 99491436 := by
        calc
          (17 : ZMod 314954641) ^ 835 = (17 : ZMod 314954641) ^ (417 + 417 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 417 * (17 : ZMod 314954641) ^ 417) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 99491436 := by rw [factor_7_8]; decide
      have factor_7_10 : (17 : ZMod 314954641) ^ 1671 = 280482662 := by
        calc
          (17 : ZMod 314954641) ^ 1671 = (17 : ZMod 314954641) ^ (835 + 835 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 835 * (17 : ZMod 314954641) ^ 835) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 280482662 := by rw [factor_7_9]; decide
      have factor_7_11 : (17 : ZMod 314954641) ^ 3343 = 265606770 := by
        calc
          (17 : ZMod 314954641) ^ 3343 = (17 : ZMod 314954641) ^ (1671 + 1671 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 1671 * (17 : ZMod 314954641) ^ 1671) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 265606770 := by rw [factor_7_10]; decide
      have factor_7_12 : (17 : ZMod 314954641) ^ 6686 = 95571255 := by
        calc
          (17 : ZMod 314954641) ^ 6686 = (17 : ZMod 314954641) ^ (3343 + 3343) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 3343 * (17 : ZMod 314954641) ^ 3343 := by rw [pow_add]
          _ = 95571255 := by rw [factor_7_11]; decide
      have factor_7_13 : (17 : ZMod 314954641) ^ 13372 = 39220373 := by
        calc
          (17 : ZMod 314954641) ^ 13372 = (17 : ZMod 314954641) ^ (6686 + 6686) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 6686 * (17 : ZMod 314954641) ^ 6686 := by rw [pow_add]
          _ = 39220373 := by rw [factor_7_12]; decide
      have factor_7_14 : (17 : ZMod 314954641) ^ 26745 = 115461397 := by
        calc
          (17 : ZMod 314954641) ^ 26745 = (17 : ZMod 314954641) ^ (13372 + 13372 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 13372 * (17 : ZMod 314954641) ^ 13372) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 115461397 := by rw [factor_7_13]; decide
      have factor_7_15 : (17 : ZMod 314954641) ^ 53490 = 293418219 := by
        calc
          (17 : ZMod 314954641) ^ 53490 = (17 : ZMod 314954641) ^ (26745 + 26745) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 26745 * (17 : ZMod 314954641) ^ 26745 := by rw [pow_add]
          _ = 293418219 := by rw [factor_7_14]; decide
      have factor_7_16 : (17 : ZMod 314954641) ^ 106981 = 37209044 := by
        calc
          (17 : ZMod 314954641) ^ 106981 = (17 : ZMod 314954641) ^ (53490 + 53490 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 53490 * (17 : ZMod 314954641) ^ 53490) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 37209044 := by rw [factor_7_15]; decide
      have factor_7_17 : (17 : ZMod 314954641) ^ 213963 = 237763925 := by
        calc
          (17 : ZMod 314954641) ^ 213963 = (17 : ZMod 314954641) ^ (106981 + 106981 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 106981 * (17 : ZMod 314954641) ^ 106981) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 237763925 := by rw [factor_7_16]; decide
      have factor_7_18 : (17 : ZMod 314954641) ^ 427927 = 185549719 := by
        calc
          (17 : ZMod 314954641) ^ 427927 = (17 : ZMod 314954641) ^ (213963 + 213963 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 213963 * (17 : ZMod 314954641) ^ 213963) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 185549719 := by rw [factor_7_17]; decide
      have factor_7_19 : (17 : ZMod 314954641) ^ 855855 = 59563935 := by
        calc
          (17 : ZMod 314954641) ^ 855855 = (17 : ZMod 314954641) ^ (427927 + 427927 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = ((17 : ZMod 314954641) ^ 427927 * (17 : ZMod 314954641) ^ 427927) * (17 : ZMod 314954641) := by rw [pow_succ, pow_add]
          _ = 59563935 := by rw [factor_7_18]; decide
      have factor_7_20 : (17 : ZMod 314954641) ^ 1711710 = 52168268 := by
        calc
          (17 : ZMod 314954641) ^ 1711710 = (17 : ZMod 314954641) ^ (855855 + 855855) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 855855 * (17 : ZMod 314954641) ^ 855855 := by rw [pow_add]
          _ = 52168268 := by rw [factor_7_19]; decide
      have factor_7_21 : (17 : ZMod 314954641) ^ 3423420 = 93964568 := by
        calc
          (17 : ZMod 314954641) ^ 3423420 = (17 : ZMod 314954641) ^ (1711710 + 1711710) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 1711710 * (17 : ZMod 314954641) ^ 1711710 := by rw [pow_add]
          _ = 93964568 := by rw [factor_7_20]; decide
      have factor_7_22 : (17 : ZMod 314954641) ^ 6846840 = 214435257 := by
        calc
          (17 : ZMod 314954641) ^ 6846840 = (17 : ZMod 314954641) ^ (3423420 + 3423420) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 3423420 * (17 : ZMod 314954641) ^ 3423420 := by rw [pow_add]
          _ = 214435257 := by rw [factor_7_21]; decide
      have factor_7_23 : (17 : ZMod 314954641) ^ 13693680 = 109292181 := by
        calc
          (17 : ZMod 314954641) ^ 13693680 = (17 : ZMod 314954641) ^ (6846840 + 6846840) :=
            congrArg (fun n : ℕ => (17 : ZMod 314954641) ^ n) (by norm_num)
          _ = (17 : ZMod 314954641) ^ 6846840 * (17 : ZMod 314954641) ^ 6846840 := by rw [pow_add]
          _ = 109292181 := by rw [factor_7_22]; decide
      change (17 : ZMod 314954641) ^ 13693680 ≠ 1
      rw [factor_7_23]
      decide

#print axioms prime_lucas_314954641

end TotientTailPeriodKiller
end Erdos249257
