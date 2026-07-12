import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime262886497

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1577318983 : Nat.Prime 1577318983 := by
  apply lucas_primality 1577318983 (3 : ZMod 1577318983)
  ·
      have fermat_0 : (3 : ZMod 1577318983) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 1577318983) ^ 2 = 9 := by
        calc
          (3 : ZMod 1577318983) ^ 2 = (3 : ZMod 1577318983) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 1 * (3 : ZMod 1577318983) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 1577318983) ^ 5 = 243 := by
        calc
          (3 : ZMod 1577318983) ^ 5 = (3 : ZMod 1577318983) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 2 * (3 : ZMod 1577318983) ^ 2) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 1577318983) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1577318983) ^ 11 = (3 : ZMod 1577318983) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 5 * (3 : ZMod 1577318983) ^ 5) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 1577318983) ^ 23 = 1081358830 := by
        calc
          (3 : ZMod 1577318983) ^ 23 = (3 : ZMod 1577318983) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 11 * (3 : ZMod 1577318983) ^ 11) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1081358830 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 1577318983) ^ 47 = 846177572 := by
        calc
          (3 : ZMod 1577318983) ^ 47 = (3 : ZMod 1577318983) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 23 * (3 : ZMod 1577318983) ^ 23) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 846177572 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 1577318983) ^ 94 = 1205668672 := by
        calc
          (3 : ZMod 1577318983) ^ 94 = (3 : ZMod 1577318983) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 47 * (3 : ZMod 1577318983) ^ 47 := by rw [pow_add]
          _ = 1205668672 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 1577318983) ^ 188 = 1025400559 := by
        calc
          (3 : ZMod 1577318983) ^ 188 = (3 : ZMod 1577318983) ^ (94 + 94) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 94 * (3 : ZMod 1577318983) ^ 94 := by rw [pow_add]
          _ = 1025400559 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 1577318983) ^ 376 = 610160454 := by
        calc
          (3 : ZMod 1577318983) ^ 376 = (3 : ZMod 1577318983) ^ (188 + 188) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 188 * (3 : ZMod 1577318983) ^ 188 := by rw [pow_add]
          _ = 610160454 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 1577318983) ^ 752 = 233396832 := by
        calc
          (3 : ZMod 1577318983) ^ 752 = (3 : ZMod 1577318983) ^ (376 + 376) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 376 * (3 : ZMod 1577318983) ^ 376 := by rw [pow_add]
          _ = 233396832 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 1577318983) ^ 1504 = 996853980 := by
        calc
          (3 : ZMod 1577318983) ^ 1504 = (3 : ZMod 1577318983) ^ (752 + 752) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 752 * (3 : ZMod 1577318983) ^ 752 := by rw [pow_add]
          _ = 996853980 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 1577318983) ^ 3008 = 535927741 := by
        calc
          (3 : ZMod 1577318983) ^ 3008 = (3 : ZMod 1577318983) ^ (1504 + 1504) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 1504 * (3 : ZMod 1577318983) ^ 1504 := by rw [pow_add]
          _ = 535927741 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 1577318983) ^ 6016 = 1476092888 := by
        calc
          (3 : ZMod 1577318983) ^ 6016 = (3 : ZMod 1577318983) ^ (3008 + 3008) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 3008 * (3 : ZMod 1577318983) ^ 3008 := by rw [pow_add]
          _ = 1476092888 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 1577318983) ^ 12033 = 741308882 := by
        calc
          (3 : ZMod 1577318983) ^ 12033 = (3 : ZMod 1577318983) ^ (6016 + 6016 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 6016 * (3 : ZMod 1577318983) ^ 6016) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 741308882 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 1577318983) ^ 24067 = 60578675 := by
        calc
          (3 : ZMod 1577318983) ^ 24067 = (3 : ZMod 1577318983) ^ (12033 + 12033 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 12033 * (3 : ZMod 1577318983) ^ 12033) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 60578675 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 1577318983) ^ 48135 = 721654999 := by
        calc
          (3 : ZMod 1577318983) ^ 48135 = (3 : ZMod 1577318983) ^ (24067 + 24067 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 24067 * (3 : ZMod 1577318983) ^ 24067) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 721654999 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 1577318983) ^ 96271 = 1566750756 := by
        calc
          (3 : ZMod 1577318983) ^ 96271 = (3 : ZMod 1577318983) ^ (48135 + 48135 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 48135 * (3 : ZMod 1577318983) ^ 48135) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1566750756 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 1577318983) ^ 192543 = 280806812 := by
        calc
          (3 : ZMod 1577318983) ^ 192543 = (3 : ZMod 1577318983) ^ (96271 + 96271 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 96271 * (3 : ZMod 1577318983) ^ 96271) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 280806812 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 1577318983) ^ 385087 = 1469448050 := by
        calc
          (3 : ZMod 1577318983) ^ 385087 = (3 : ZMod 1577318983) ^ (192543 + 192543 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 192543 * (3 : ZMod 1577318983) ^ 192543) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1469448050 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 1577318983) ^ 770175 = 1569072729 := by
        calc
          (3 : ZMod 1577318983) ^ 770175 = (3 : ZMod 1577318983) ^ (385087 + 385087 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 385087 * (3 : ZMod 1577318983) ^ 385087) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1569072729 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 1577318983) ^ 1540350 = 906356403 := by
        calc
          (3 : ZMod 1577318983) ^ 1540350 = (3 : ZMod 1577318983) ^ (770175 + 770175) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 770175 * (3 : ZMod 1577318983) ^ 770175 := by rw [pow_add]
          _ = 906356403 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 1577318983) ^ 3080701 = 620407448 := by
        calc
          (3 : ZMod 1577318983) ^ 3080701 = (3 : ZMod 1577318983) ^ (1540350 + 1540350 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 1540350 * (3 : ZMod 1577318983) ^ 1540350) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 620407448 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 1577318983) ^ 6161402 = 1057865166 := by
        calc
          (3 : ZMod 1577318983) ^ 6161402 = (3 : ZMod 1577318983) ^ (3080701 + 3080701) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 3080701 * (3 : ZMod 1577318983) ^ 3080701 := by rw [pow_add]
          _ = 1057865166 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 1577318983) ^ 12322804 = 419538821 := by
        calc
          (3 : ZMod 1577318983) ^ 12322804 = (3 : ZMod 1577318983) ^ (6161402 + 6161402) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 6161402 * (3 : ZMod 1577318983) ^ 6161402 := by rw [pow_add]
          _ = 419538821 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 1577318983) ^ 24645609 = 1461746544 := by
        calc
          (3 : ZMod 1577318983) ^ 24645609 = (3 : ZMod 1577318983) ^ (12322804 + 12322804 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 12322804 * (3 : ZMod 1577318983) ^ 12322804) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1461746544 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 1577318983) ^ 49291218 = 714646424 := by
        calc
          (3 : ZMod 1577318983) ^ 49291218 = (3 : ZMod 1577318983) ^ (24645609 + 24645609) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 24645609 * (3 : ZMod 1577318983) ^ 24645609 := by rw [pow_add]
          _ = 714646424 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 1577318983) ^ 98582436 = 366269282 := by
        calc
          (3 : ZMod 1577318983) ^ 98582436 = (3 : ZMod 1577318983) ^ (49291218 + 49291218) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 49291218 * (3 : ZMod 1577318983) ^ 49291218 := by rw [pow_add]
          _ = 366269282 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 1577318983) ^ 197164872 = 763388307 := by
        calc
          (3 : ZMod 1577318983) ^ 197164872 = (3 : ZMod 1577318983) ^ (98582436 + 98582436) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 98582436 * (3 : ZMod 1577318983) ^ 98582436 := by rw [pow_add]
          _ = 763388307 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 1577318983) ^ 394329745 = 1091792493 := by
        calc
          (3 : ZMod 1577318983) ^ 394329745 = (3 : ZMod 1577318983) ^ (197164872 + 197164872 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 197164872 * (3 : ZMod 1577318983) ^ 197164872) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1091792493 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 1577318983) ^ 788659491 = 1577318982 := by
        calc
          (3 : ZMod 1577318983) ^ 788659491 = (3 : ZMod 1577318983) ^ (394329745 + 394329745 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 394329745 * (3 : ZMod 1577318983) ^ 394329745) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1577318982 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 1577318983) ^ 1577318982 = 1 := by
        calc
          (3 : ZMod 1577318983) ^ 1577318982 = (3 : ZMod 1577318983) ^ (788659491 + 788659491) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 788659491 * (3 : ZMod 1577318983) ^ 788659491 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (262886497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (262886497, 1)] : List FactorBlock).map factorBlockValue).prod = 1577318983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_262886497) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 1577318983) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 1577318983) ^ 2 = 9 := by
        calc
          (3 : ZMod 1577318983) ^ 2 = (3 : ZMod 1577318983) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 1 * (3 : ZMod 1577318983) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 1577318983) ^ 5 = 243 := by
        calc
          (3 : ZMod 1577318983) ^ 5 = (3 : ZMod 1577318983) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 2 * (3 : ZMod 1577318983) ^ 2) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 1577318983) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1577318983) ^ 11 = (3 : ZMod 1577318983) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 5 * (3 : ZMod 1577318983) ^ 5) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 1577318983) ^ 23 = 1081358830 := by
        calc
          (3 : ZMod 1577318983) ^ 23 = (3 : ZMod 1577318983) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 11 * (3 : ZMod 1577318983) ^ 11) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1081358830 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 1577318983) ^ 47 = 846177572 := by
        calc
          (3 : ZMod 1577318983) ^ 47 = (3 : ZMod 1577318983) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 23 * (3 : ZMod 1577318983) ^ 23) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 846177572 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 1577318983) ^ 94 = 1205668672 := by
        calc
          (3 : ZMod 1577318983) ^ 94 = (3 : ZMod 1577318983) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 47 * (3 : ZMod 1577318983) ^ 47 := by rw [pow_add]
          _ = 1205668672 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 1577318983) ^ 188 = 1025400559 := by
        calc
          (3 : ZMod 1577318983) ^ 188 = (3 : ZMod 1577318983) ^ (94 + 94) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 94 * (3 : ZMod 1577318983) ^ 94 := by rw [pow_add]
          _ = 1025400559 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 1577318983) ^ 376 = 610160454 := by
        calc
          (3 : ZMod 1577318983) ^ 376 = (3 : ZMod 1577318983) ^ (188 + 188) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 188 * (3 : ZMod 1577318983) ^ 188 := by rw [pow_add]
          _ = 610160454 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 1577318983) ^ 752 = 233396832 := by
        calc
          (3 : ZMod 1577318983) ^ 752 = (3 : ZMod 1577318983) ^ (376 + 376) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 376 * (3 : ZMod 1577318983) ^ 376 := by rw [pow_add]
          _ = 233396832 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 1577318983) ^ 1504 = 996853980 := by
        calc
          (3 : ZMod 1577318983) ^ 1504 = (3 : ZMod 1577318983) ^ (752 + 752) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 752 * (3 : ZMod 1577318983) ^ 752 := by rw [pow_add]
          _ = 996853980 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 1577318983) ^ 3008 = 535927741 := by
        calc
          (3 : ZMod 1577318983) ^ 3008 = (3 : ZMod 1577318983) ^ (1504 + 1504) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 1504 * (3 : ZMod 1577318983) ^ 1504 := by rw [pow_add]
          _ = 535927741 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 1577318983) ^ 6016 = 1476092888 := by
        calc
          (3 : ZMod 1577318983) ^ 6016 = (3 : ZMod 1577318983) ^ (3008 + 3008) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 3008 * (3 : ZMod 1577318983) ^ 3008 := by rw [pow_add]
          _ = 1476092888 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 1577318983) ^ 12033 = 741308882 := by
        calc
          (3 : ZMod 1577318983) ^ 12033 = (3 : ZMod 1577318983) ^ (6016 + 6016 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 6016 * (3 : ZMod 1577318983) ^ 6016) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 741308882 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 1577318983) ^ 24067 = 60578675 := by
        calc
          (3 : ZMod 1577318983) ^ 24067 = (3 : ZMod 1577318983) ^ (12033 + 12033 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 12033 * (3 : ZMod 1577318983) ^ 12033) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 60578675 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 1577318983) ^ 48135 = 721654999 := by
        calc
          (3 : ZMod 1577318983) ^ 48135 = (3 : ZMod 1577318983) ^ (24067 + 24067 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 24067 * (3 : ZMod 1577318983) ^ 24067) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 721654999 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 1577318983) ^ 96271 = 1566750756 := by
        calc
          (3 : ZMod 1577318983) ^ 96271 = (3 : ZMod 1577318983) ^ (48135 + 48135 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 48135 * (3 : ZMod 1577318983) ^ 48135) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1566750756 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 1577318983) ^ 192543 = 280806812 := by
        calc
          (3 : ZMod 1577318983) ^ 192543 = (3 : ZMod 1577318983) ^ (96271 + 96271 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 96271 * (3 : ZMod 1577318983) ^ 96271) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 280806812 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 1577318983) ^ 385087 = 1469448050 := by
        calc
          (3 : ZMod 1577318983) ^ 385087 = (3 : ZMod 1577318983) ^ (192543 + 192543 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 192543 * (3 : ZMod 1577318983) ^ 192543) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1469448050 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 1577318983) ^ 770175 = 1569072729 := by
        calc
          (3 : ZMod 1577318983) ^ 770175 = (3 : ZMod 1577318983) ^ (385087 + 385087 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 385087 * (3 : ZMod 1577318983) ^ 385087) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1569072729 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 1577318983) ^ 1540350 = 906356403 := by
        calc
          (3 : ZMod 1577318983) ^ 1540350 = (3 : ZMod 1577318983) ^ (770175 + 770175) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 770175 * (3 : ZMod 1577318983) ^ 770175 := by rw [pow_add]
          _ = 906356403 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 1577318983) ^ 3080701 = 620407448 := by
        calc
          (3 : ZMod 1577318983) ^ 3080701 = (3 : ZMod 1577318983) ^ (1540350 + 1540350 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 1540350 * (3 : ZMod 1577318983) ^ 1540350) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 620407448 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 1577318983) ^ 6161402 = 1057865166 := by
        calc
          (3 : ZMod 1577318983) ^ 6161402 = (3 : ZMod 1577318983) ^ (3080701 + 3080701) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 3080701 * (3 : ZMod 1577318983) ^ 3080701 := by rw [pow_add]
          _ = 1057865166 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 1577318983) ^ 12322804 = 419538821 := by
        calc
          (3 : ZMod 1577318983) ^ 12322804 = (3 : ZMod 1577318983) ^ (6161402 + 6161402) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 6161402 * (3 : ZMod 1577318983) ^ 6161402 := by rw [pow_add]
          _ = 419538821 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 1577318983) ^ 24645609 = 1461746544 := by
        calc
          (3 : ZMod 1577318983) ^ 24645609 = (3 : ZMod 1577318983) ^ (12322804 + 12322804 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 12322804 * (3 : ZMod 1577318983) ^ 12322804) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1461746544 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 1577318983) ^ 49291218 = 714646424 := by
        calc
          (3 : ZMod 1577318983) ^ 49291218 = (3 : ZMod 1577318983) ^ (24645609 + 24645609) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 24645609 * (3 : ZMod 1577318983) ^ 24645609 := by rw [pow_add]
          _ = 714646424 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 1577318983) ^ 98582436 = 366269282 := by
        calc
          (3 : ZMod 1577318983) ^ 98582436 = (3 : ZMod 1577318983) ^ (49291218 + 49291218) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 49291218 * (3 : ZMod 1577318983) ^ 49291218 := by rw [pow_add]
          _ = 366269282 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 1577318983) ^ 197164872 = 763388307 := by
        calc
          (3 : ZMod 1577318983) ^ 197164872 = (3 : ZMod 1577318983) ^ (98582436 + 98582436) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 98582436 * (3 : ZMod 1577318983) ^ 98582436 := by rw [pow_add]
          _ = 763388307 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 1577318983) ^ 394329745 = 1091792493 := by
        calc
          (3 : ZMod 1577318983) ^ 394329745 = (3 : ZMod 1577318983) ^ (197164872 + 197164872 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 197164872 * (3 : ZMod 1577318983) ^ 197164872) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1091792493 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 1577318983) ^ 788659491 = 1577318982 := by
        calc
          (3 : ZMod 1577318983) ^ 788659491 = (3 : ZMod 1577318983) ^ (394329745 + 394329745 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 394329745 * (3 : ZMod 1577318983) ^ 394329745) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1577318982 := by rw [factor_0_28]; decide
      change (3 : ZMod 1577318983) ^ 788659491 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (3 : ZMod 1577318983) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 1577318983) ^ 3 = 27 := by
        calc
          (3 : ZMod 1577318983) ^ 3 = (3 : ZMod 1577318983) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 1 * (3 : ZMod 1577318983) ^ 1) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 1577318983) ^ 7 = 2187 := by
        calc
          (3 : ZMod 1577318983) ^ 7 = (3 : ZMod 1577318983) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 3 * (3 : ZMod 1577318983) ^ 3) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 1577318983) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 1577318983) ^ 15 = (3 : ZMod 1577318983) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 7 * (3 : ZMod 1577318983) ^ 7) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 1577318983) ^ 31 = 14498096 := by
        calc
          (3 : ZMod 1577318983) ^ 31 = (3 : ZMod 1577318983) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 15 * (3 : ZMod 1577318983) ^ 15) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 14498096 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 1577318983) ^ 62 = 1259950636 := by
        calc
          (3 : ZMod 1577318983) ^ 62 = (3 : ZMod 1577318983) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 31 * (3 : ZMod 1577318983) ^ 31 := by rw [pow_add]
          _ = 1259950636 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 1577318983) ^ 125 = 707035056 := by
        calc
          (3 : ZMod 1577318983) ^ 125 = (3 : ZMod 1577318983) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 62 * (3 : ZMod 1577318983) ^ 62) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 707035056 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 1577318983) ^ 250 = 800400896 := by
        calc
          (3 : ZMod 1577318983) ^ 250 = (3 : ZMod 1577318983) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 125 * (3 : ZMod 1577318983) ^ 125 := by rw [pow_add]
          _ = 800400896 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 1577318983) ^ 501 = 420630600 := by
        calc
          (3 : ZMod 1577318983) ^ 501 = (3 : ZMod 1577318983) ^ (250 + 250 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 250 * (3 : ZMod 1577318983) ^ 250) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 420630600 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 1577318983) ^ 1002 = 1004208038 := by
        calc
          (3 : ZMod 1577318983) ^ 1002 = (3 : ZMod 1577318983) ^ (501 + 501) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 501 * (3 : ZMod 1577318983) ^ 501 := by rw [pow_add]
          _ = 1004208038 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 1577318983) ^ 2005 = 276311497 := by
        calc
          (3 : ZMod 1577318983) ^ 2005 = (3 : ZMod 1577318983) ^ (1002 + 1002 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 1002 * (3 : ZMod 1577318983) ^ 1002) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 276311497 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 1577318983) ^ 4011 = 189970707 := by
        calc
          (3 : ZMod 1577318983) ^ 4011 = (3 : ZMod 1577318983) ^ (2005 + 2005 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 2005 * (3 : ZMod 1577318983) ^ 2005) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 189970707 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 1577318983) ^ 8022 = 465317809 := by
        calc
          (3 : ZMod 1577318983) ^ 8022 = (3 : ZMod 1577318983) ^ (4011 + 4011) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 4011 * (3 : ZMod 1577318983) ^ 4011 := by rw [pow_add]
          _ = 465317809 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 1577318983) ^ 16045 = 926726899 := by
        calc
          (3 : ZMod 1577318983) ^ 16045 = (3 : ZMod 1577318983) ^ (8022 + 8022 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 8022 * (3 : ZMod 1577318983) ^ 8022) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 926726899 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 1577318983) ^ 32090 = 1282322435 := by
        calc
          (3 : ZMod 1577318983) ^ 32090 = (3 : ZMod 1577318983) ^ (16045 + 16045) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 16045 * (3 : ZMod 1577318983) ^ 16045 := by rw [pow_add]
          _ = 1282322435 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 1577318983) ^ 64181 = 60179471 := by
        calc
          (3 : ZMod 1577318983) ^ 64181 = (3 : ZMod 1577318983) ^ (32090 + 32090 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 32090 * (3 : ZMod 1577318983) ^ 32090) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 60179471 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 1577318983) ^ 128362 = 179940317 := by
        calc
          (3 : ZMod 1577318983) ^ 128362 = (3 : ZMod 1577318983) ^ (64181 + 64181) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 64181 * (3 : ZMod 1577318983) ^ 64181 := by rw [pow_add]
          _ = 179940317 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 1577318983) ^ 256725 = 775701265 := by
        calc
          (3 : ZMod 1577318983) ^ 256725 = (3 : ZMod 1577318983) ^ (128362 + 128362 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 128362 * (3 : ZMod 1577318983) ^ 128362) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 775701265 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 1577318983) ^ 513450 = 958700800 := by
        calc
          (3 : ZMod 1577318983) ^ 513450 = (3 : ZMod 1577318983) ^ (256725 + 256725) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 256725 * (3 : ZMod 1577318983) ^ 256725 := by rw [pow_add]
          _ = 958700800 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 1577318983) ^ 1026900 = 1352605196 := by
        calc
          (3 : ZMod 1577318983) ^ 1026900 = (3 : ZMod 1577318983) ^ (513450 + 513450) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 513450 * (3 : ZMod 1577318983) ^ 513450 := by rw [pow_add]
          _ = 1352605196 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 1577318983) ^ 2053800 = 878076318 := by
        calc
          (3 : ZMod 1577318983) ^ 2053800 = (3 : ZMod 1577318983) ^ (1026900 + 1026900) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 1026900 * (3 : ZMod 1577318983) ^ 1026900 := by rw [pow_add]
          _ = 878076318 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 1577318983) ^ 4107601 = 961503572 := by
        calc
          (3 : ZMod 1577318983) ^ 4107601 = (3 : ZMod 1577318983) ^ (2053800 + 2053800 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 2053800 * (3 : ZMod 1577318983) ^ 2053800) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 961503572 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 1577318983) ^ 8215203 = 1298466843 := by
        calc
          (3 : ZMod 1577318983) ^ 8215203 = (3 : ZMod 1577318983) ^ (4107601 + 4107601 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 4107601 * (3 : ZMod 1577318983) ^ 4107601) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1298466843 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 1577318983) ^ 16430406 = 913224917 := by
        calc
          (3 : ZMod 1577318983) ^ 16430406 = (3 : ZMod 1577318983) ^ (8215203 + 8215203) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 8215203 * (3 : ZMod 1577318983) ^ 8215203 := by rw [pow_add]
          _ = 913224917 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 1577318983) ^ 32860812 = 1366049726 := by
        calc
          (3 : ZMod 1577318983) ^ 32860812 = (3 : ZMod 1577318983) ^ (16430406 + 16430406) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 16430406 * (3 : ZMod 1577318983) ^ 16430406 := by rw [pow_add]
          _ = 1366049726 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 1577318983) ^ 65721624 = 825901091 := by
        calc
          (3 : ZMod 1577318983) ^ 65721624 = (3 : ZMod 1577318983) ^ (32860812 + 32860812) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 32860812 * (3 : ZMod 1577318983) ^ 32860812 := by rw [pow_add]
          _ = 825901091 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 1577318983) ^ 131443248 = 545896246 := by
        calc
          (3 : ZMod 1577318983) ^ 131443248 = (3 : ZMod 1577318983) ^ (65721624 + 65721624) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 65721624 * (3 : ZMod 1577318983) ^ 65721624 := by rw [pow_add]
          _ = 545896246 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 1577318983) ^ 262886497 = 1516949227 := by
        calc
          (3 : ZMod 1577318983) ^ 262886497 = (3 : ZMod 1577318983) ^ (131443248 + 131443248 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 131443248 * (3 : ZMod 1577318983) ^ 131443248) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 1516949227 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 1577318983) ^ 525772994 = 1516949226 := by
        calc
          (3 : ZMod 1577318983) ^ 525772994 = (3 : ZMod 1577318983) ^ (262886497 + 262886497) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 262886497 * (3 : ZMod 1577318983) ^ 262886497 := by rw [pow_add]
          _ = 1516949226 := by rw [factor_1_27]; decide
      change (3 : ZMod 1577318983) ^ 525772994 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (3 : ZMod 1577318983) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 1577318983) ^ 3 = 27 := by
        calc
          (3 : ZMod 1577318983) ^ 3 = (3 : ZMod 1577318983) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = ((3 : ZMod 1577318983) ^ 1 * (3 : ZMod 1577318983) ^ 1) * (3 : ZMod 1577318983) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 1577318983) ^ 6 = 729 := by
        calc
          (3 : ZMod 1577318983) ^ 6 = (3 : ZMod 1577318983) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1577318983) ^ n) (by norm_num)
          _ = (3 : ZMod 1577318983) ^ 3 * (3 : ZMod 1577318983) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      change (3 : ZMod 1577318983) ^ 6 ≠ 1
      rw [factor_2_2]
      decide

#print axioms prime_lucas_1577318983

end TotientTailPeriodKiller
end Erdos249257
