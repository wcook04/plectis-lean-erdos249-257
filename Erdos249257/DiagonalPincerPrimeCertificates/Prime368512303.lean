import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_368512303 : Nat.Prime 368512303 := by
  apply lucas_primality 368512303 (3 : ZMod 368512303)
  ·
      have fermat_0 : (3 : ZMod 368512303) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 368512303) ^ 2 = 9 := by
        calc
          (3 : ZMod 368512303) ^ 2 = (3 : ZMod 368512303) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1 * (3 : ZMod 368512303) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 368512303) ^ 5 = 243 := by
        calc
          (3 : ZMod 368512303) ^ 5 = (3 : ZMod 368512303) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 2 * (3 : ZMod 368512303) ^ 2) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 368512303) ^ 10 = 59049 := by
        calc
          (3 : ZMod 368512303) ^ 10 = (3 : ZMod 368512303) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 5 * (3 : ZMod 368512303) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 368512303) ^ 21 = 142008719 := by
        calc
          (3 : ZMod 368512303) ^ 21 = (3 : ZMod 368512303) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 10 * (3 : ZMod 368512303) ^ 10) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 142008719 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 368512303) ^ 43 = 106548764 := by
        calc
          (3 : ZMod 368512303) ^ 43 = (3 : ZMod 368512303) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 21 * (3 : ZMod 368512303) ^ 21) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 106548764 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 368512303) ^ 87 = 336690907 := by
        calc
          (3 : ZMod 368512303) ^ 87 = (3 : ZMod 368512303) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 43 * (3 : ZMod 368512303) ^ 43) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 336690907 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 368512303) ^ 175 = 198808673 := by
        calc
          (3 : ZMod 368512303) ^ 175 = (3 : ZMod 368512303) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 87 * (3 : ZMod 368512303) ^ 87) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 198808673 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 368512303) ^ 351 = 182617812 := by
        calc
          (3 : ZMod 368512303) ^ 351 = (3 : ZMod 368512303) ^ (175 + 175 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 175 * (3 : ZMod 368512303) ^ 175) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 182617812 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 368512303) ^ 702 = 4830284 := by
        calc
          (3 : ZMod 368512303) ^ 702 = (3 : ZMod 368512303) ^ (351 + 351) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 351 * (3 : ZMod 368512303) ^ 351 := by rw [pow_add]
          _ = 4830284 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 368512303) ^ 1405 = 72242451 := by
        calc
          (3 : ZMod 368512303) ^ 1405 = (3 : ZMod 368512303) ^ (702 + 702 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 702 * (3 : ZMod 368512303) ^ 702) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 72242451 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 368512303) ^ 2811 = 31140349 := by
        calc
          (3 : ZMod 368512303) ^ 2811 = (3 : ZMod 368512303) ^ (1405 + 1405 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 1405 * (3 : ZMod 368512303) ^ 1405) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 31140349 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 368512303) ^ 5623 = 13874262 := by
        calc
          (3 : ZMod 368512303) ^ 5623 = (3 : ZMod 368512303) ^ (2811 + 2811 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 2811 * (3 : ZMod 368512303) ^ 2811) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 13874262 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 368512303) ^ 11246 = 164986473 := by
        calc
          (3 : ZMod 368512303) ^ 11246 = (3 : ZMod 368512303) ^ (5623 + 5623) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 5623 * (3 : ZMod 368512303) ^ 5623 := by rw [pow_add]
          _ = 164986473 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 368512303) ^ 22492 = 234872578 := by
        calc
          (3 : ZMod 368512303) ^ 22492 = (3 : ZMod 368512303) ^ (11246 + 11246) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 11246 * (3 : ZMod 368512303) ^ 11246 := by rw [pow_add]
          _ = 234872578 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 368512303) ^ 44984 = 267631261 := by
        calc
          (3 : ZMod 368512303) ^ 44984 = (3 : ZMod 368512303) ^ (22492 + 22492) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 22492 * (3 : ZMod 368512303) ^ 22492 := by rw [pow_add]
          _ = 267631261 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 368512303) ^ 89968 = 364899655 := by
        calc
          (3 : ZMod 368512303) ^ 89968 = (3 : ZMod 368512303) ^ (44984 + 44984) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 44984 * (3 : ZMod 368512303) ^ 44984 := by rw [pow_add]
          _ = 364899655 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 368512303) ^ 179937 = 350058871 := by
        calc
          (3 : ZMod 368512303) ^ 179937 = (3 : ZMod 368512303) ^ (89968 + 89968 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 89968 * (3 : ZMod 368512303) ^ 89968) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 350058871 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 368512303) ^ 359875 = 230945393 := by
        calc
          (3 : ZMod 368512303) ^ 359875 = (3 : ZMod 368512303) ^ (179937 + 179937 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 179937 * (3 : ZMod 368512303) ^ 179937) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 230945393 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 368512303) ^ 719750 = 216225500 := by
        calc
          (3 : ZMod 368512303) ^ 719750 = (3 : ZMod 368512303) ^ (359875 + 359875) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 359875 * (3 : ZMod 368512303) ^ 359875 := by rw [pow_add]
          _ = 216225500 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 368512303) ^ 1439501 = 201281107 := by
        calc
          (3 : ZMod 368512303) ^ 1439501 = (3 : ZMod 368512303) ^ (719750 + 719750 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 719750 * (3 : ZMod 368512303) ^ 719750) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 201281107 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 368512303) ^ 2879002 = 272128042 := by
        calc
          (3 : ZMod 368512303) ^ 2879002 = (3 : ZMod 368512303) ^ (1439501 + 1439501) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1439501 * (3 : ZMod 368512303) ^ 1439501 := by rw [pow_add]
          _ = 272128042 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 368512303) ^ 5758004 = 360891917 := by
        calc
          (3 : ZMod 368512303) ^ 5758004 = (3 : ZMod 368512303) ^ (2879002 + 2879002) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 2879002 * (3 : ZMod 368512303) ^ 2879002 := by rw [pow_add]
          _ = 360891917 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 368512303) ^ 11516009 = 342246768 := by
        calc
          (3 : ZMod 368512303) ^ 11516009 = (3 : ZMod 368512303) ^ (5758004 + 5758004 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 5758004 * (3 : ZMod 368512303) ^ 5758004) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 342246768 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 368512303) ^ 23032018 = 81345136 := by
        calc
          (3 : ZMod 368512303) ^ 23032018 = (3 : ZMod 368512303) ^ (11516009 + 11516009) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 11516009 * (3 : ZMod 368512303) ^ 11516009 := by rw [pow_add]
          _ = 81345136 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 368512303) ^ 46064037 = 117647797 := by
        calc
          (3 : ZMod 368512303) ^ 46064037 = (3 : ZMod 368512303) ^ (23032018 + 23032018 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 23032018 * (3 : ZMod 368512303) ^ 23032018) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 117647797 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 368512303) ^ 92128075 = 193172094 := by
        calc
          (3 : ZMod 368512303) ^ 92128075 = (3 : ZMod 368512303) ^ (46064037 + 46064037 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 46064037 * (3 : ZMod 368512303) ^ 46064037) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 193172094 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 368512303) ^ 184256151 = 368512302 := by
        calc
          (3 : ZMod 368512303) ^ 184256151 = (3 : ZMod 368512303) ^ (92128075 + 92128075 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 92128075 * (3 : ZMod 368512303) ^ 92128075) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 368512302 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 368512303) ^ 368512302 = 1 := by
        calc
          (3 : ZMod 368512303) ^ 368512302 = (3 : ZMod 368512303) ^ (184256151 + 184256151) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 184256151 * (3 : ZMod 368512303) ^ 184256151 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (643, 1), (4153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (643, 1), (4153, 1)] : List FactorBlock).map factorBlockValue).prod = 368512303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 368512303) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 368512303) ^ 2 = 9 := by
        calc
          (3 : ZMod 368512303) ^ 2 = (3 : ZMod 368512303) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1 * (3 : ZMod 368512303) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 368512303) ^ 5 = 243 := by
        calc
          (3 : ZMod 368512303) ^ 5 = (3 : ZMod 368512303) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 2 * (3 : ZMod 368512303) ^ 2) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 368512303) ^ 10 = 59049 := by
        calc
          (3 : ZMod 368512303) ^ 10 = (3 : ZMod 368512303) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 5 * (3 : ZMod 368512303) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 368512303) ^ 21 = 142008719 := by
        calc
          (3 : ZMod 368512303) ^ 21 = (3 : ZMod 368512303) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 10 * (3 : ZMod 368512303) ^ 10) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 142008719 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 368512303) ^ 43 = 106548764 := by
        calc
          (3 : ZMod 368512303) ^ 43 = (3 : ZMod 368512303) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 21 * (3 : ZMod 368512303) ^ 21) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 106548764 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 368512303) ^ 87 = 336690907 := by
        calc
          (3 : ZMod 368512303) ^ 87 = (3 : ZMod 368512303) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 43 * (3 : ZMod 368512303) ^ 43) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 336690907 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 368512303) ^ 175 = 198808673 := by
        calc
          (3 : ZMod 368512303) ^ 175 = (3 : ZMod 368512303) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 87 * (3 : ZMod 368512303) ^ 87) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 198808673 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 368512303) ^ 351 = 182617812 := by
        calc
          (3 : ZMod 368512303) ^ 351 = (3 : ZMod 368512303) ^ (175 + 175 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 175 * (3 : ZMod 368512303) ^ 175) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 182617812 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 368512303) ^ 702 = 4830284 := by
        calc
          (3 : ZMod 368512303) ^ 702 = (3 : ZMod 368512303) ^ (351 + 351) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 351 * (3 : ZMod 368512303) ^ 351 := by rw [pow_add]
          _ = 4830284 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 368512303) ^ 1405 = 72242451 := by
        calc
          (3 : ZMod 368512303) ^ 1405 = (3 : ZMod 368512303) ^ (702 + 702 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 702 * (3 : ZMod 368512303) ^ 702) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 72242451 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 368512303) ^ 2811 = 31140349 := by
        calc
          (3 : ZMod 368512303) ^ 2811 = (3 : ZMod 368512303) ^ (1405 + 1405 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 1405 * (3 : ZMod 368512303) ^ 1405) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 31140349 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 368512303) ^ 5623 = 13874262 := by
        calc
          (3 : ZMod 368512303) ^ 5623 = (3 : ZMod 368512303) ^ (2811 + 2811 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 2811 * (3 : ZMod 368512303) ^ 2811) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 13874262 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 368512303) ^ 11246 = 164986473 := by
        calc
          (3 : ZMod 368512303) ^ 11246 = (3 : ZMod 368512303) ^ (5623 + 5623) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 5623 * (3 : ZMod 368512303) ^ 5623 := by rw [pow_add]
          _ = 164986473 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 368512303) ^ 22492 = 234872578 := by
        calc
          (3 : ZMod 368512303) ^ 22492 = (3 : ZMod 368512303) ^ (11246 + 11246) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 11246 * (3 : ZMod 368512303) ^ 11246 := by rw [pow_add]
          _ = 234872578 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 368512303) ^ 44984 = 267631261 := by
        calc
          (3 : ZMod 368512303) ^ 44984 = (3 : ZMod 368512303) ^ (22492 + 22492) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 22492 * (3 : ZMod 368512303) ^ 22492 := by rw [pow_add]
          _ = 267631261 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 368512303) ^ 89968 = 364899655 := by
        calc
          (3 : ZMod 368512303) ^ 89968 = (3 : ZMod 368512303) ^ (44984 + 44984) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 44984 * (3 : ZMod 368512303) ^ 44984 := by rw [pow_add]
          _ = 364899655 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 368512303) ^ 179937 = 350058871 := by
        calc
          (3 : ZMod 368512303) ^ 179937 = (3 : ZMod 368512303) ^ (89968 + 89968 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 89968 * (3 : ZMod 368512303) ^ 89968) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 350058871 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 368512303) ^ 359875 = 230945393 := by
        calc
          (3 : ZMod 368512303) ^ 359875 = (3 : ZMod 368512303) ^ (179937 + 179937 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 179937 * (3 : ZMod 368512303) ^ 179937) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 230945393 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 368512303) ^ 719750 = 216225500 := by
        calc
          (3 : ZMod 368512303) ^ 719750 = (3 : ZMod 368512303) ^ (359875 + 359875) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 359875 * (3 : ZMod 368512303) ^ 359875 := by rw [pow_add]
          _ = 216225500 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 368512303) ^ 1439501 = 201281107 := by
        calc
          (3 : ZMod 368512303) ^ 1439501 = (3 : ZMod 368512303) ^ (719750 + 719750 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 719750 * (3 : ZMod 368512303) ^ 719750) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 201281107 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 368512303) ^ 2879002 = 272128042 := by
        calc
          (3 : ZMod 368512303) ^ 2879002 = (3 : ZMod 368512303) ^ (1439501 + 1439501) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1439501 * (3 : ZMod 368512303) ^ 1439501 := by rw [pow_add]
          _ = 272128042 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 368512303) ^ 5758004 = 360891917 := by
        calc
          (3 : ZMod 368512303) ^ 5758004 = (3 : ZMod 368512303) ^ (2879002 + 2879002) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 2879002 * (3 : ZMod 368512303) ^ 2879002 := by rw [pow_add]
          _ = 360891917 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 368512303) ^ 11516009 = 342246768 := by
        calc
          (3 : ZMod 368512303) ^ 11516009 = (3 : ZMod 368512303) ^ (5758004 + 5758004 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 5758004 * (3 : ZMod 368512303) ^ 5758004) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 342246768 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 368512303) ^ 23032018 = 81345136 := by
        calc
          (3 : ZMod 368512303) ^ 23032018 = (3 : ZMod 368512303) ^ (11516009 + 11516009) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 11516009 * (3 : ZMod 368512303) ^ 11516009 := by rw [pow_add]
          _ = 81345136 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 368512303) ^ 46064037 = 117647797 := by
        calc
          (3 : ZMod 368512303) ^ 46064037 = (3 : ZMod 368512303) ^ (23032018 + 23032018 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 23032018 * (3 : ZMod 368512303) ^ 23032018) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 117647797 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 368512303) ^ 92128075 = 193172094 := by
        calc
          (3 : ZMod 368512303) ^ 92128075 = (3 : ZMod 368512303) ^ (46064037 + 46064037 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 46064037 * (3 : ZMod 368512303) ^ 46064037) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 193172094 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 368512303) ^ 184256151 = 368512302 := by
        calc
          (3 : ZMod 368512303) ^ 184256151 = (3 : ZMod 368512303) ^ (92128075 + 92128075 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 92128075 * (3 : ZMod 368512303) ^ 92128075) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 368512302 := by rw [factor_0_26]; decide
      change (3 : ZMod 368512303) ^ 184256151 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (3 : ZMod 368512303) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 368512303) ^ 3 = 27 := by
        calc
          (3 : ZMod 368512303) ^ 3 = (3 : ZMod 368512303) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 1 * (3 : ZMod 368512303) ^ 1) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 368512303) ^ 7 = 2187 := by
        calc
          (3 : ZMod 368512303) ^ 7 = (3 : ZMod 368512303) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 3 * (3 : ZMod 368512303) ^ 3) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 368512303) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 368512303) ^ 14 = (3 : ZMod 368512303) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 7 * (3 : ZMod 368512303) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 368512303) ^ 29 = 120103375 := by
        calc
          (3 : ZMod 368512303) ^ 29 = (3 : ZMod 368512303) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 14 * (3 : ZMod 368512303) ^ 14) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 120103375 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 368512303) ^ 58 = 258775758 := by
        calc
          (3 : ZMod 368512303) ^ 58 = (3 : ZMod 368512303) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 29 * (3 : ZMod 368512303) ^ 29 := by rw [pow_add]
          _ = 258775758 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 368512303) ^ 117 = 19403890 := by
        calc
          (3 : ZMod 368512303) ^ 117 = (3 : ZMod 368512303) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 58 * (3 : ZMod 368512303) ^ 58) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 19403890 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 368512303) ^ 234 = 84595485 := by
        calc
          (3 : ZMod 368512303) ^ 234 = (3 : ZMod 368512303) ^ (117 + 117) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 117 * (3 : ZMod 368512303) ^ 117 := by rw [pow_add]
          _ = 84595485 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 368512303) ^ 468 = 291402246 := by
        calc
          (3 : ZMod 368512303) ^ 468 = (3 : ZMod 368512303) ^ (234 + 234) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 234 * (3 : ZMod 368512303) ^ 234 := by rw [pow_add]
          _ = 291402246 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 368512303) ^ 937 = 54926084 := by
        calc
          (3 : ZMod 368512303) ^ 937 = (3 : ZMod 368512303) ^ (468 + 468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 468 * (3 : ZMod 368512303) ^ 468) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 54926084 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 368512303) ^ 1874 = 91441560 := by
        calc
          (3 : ZMod 368512303) ^ 1874 = (3 : ZMod 368512303) ^ (937 + 937) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 937 * (3 : ZMod 368512303) ^ 937 := by rw [pow_add]
          _ = 91441560 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 368512303) ^ 3748 = 368183783 := by
        calc
          (3 : ZMod 368512303) ^ 3748 = (3 : ZMod 368512303) ^ (1874 + 1874) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1874 * (3 : ZMod 368512303) ^ 1874 := by rw [pow_add]
          _ = 368183783 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 368512303) ^ 7497 = 222369166 := by
        calc
          (3 : ZMod 368512303) ^ 7497 = (3 : ZMod 368512303) ^ (3748 + 3748 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 3748 * (3 : ZMod 368512303) ^ 3748) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 222369166 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 368512303) ^ 14994 = 170439886 := by
        calc
          (3 : ZMod 368512303) ^ 14994 = (3 : ZMod 368512303) ^ (7497 + 7497) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 7497 * (3 : ZMod 368512303) ^ 7497 := by rw [pow_add]
          _ = 170439886 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 368512303) ^ 29989 = 103134001 := by
        calc
          (3 : ZMod 368512303) ^ 29989 = (3 : ZMod 368512303) ^ (14994 + 14994 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 14994 * (3 : ZMod 368512303) ^ 14994) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 103134001 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 368512303) ^ 59979 = 337652762 := by
        calc
          (3 : ZMod 368512303) ^ 59979 = (3 : ZMod 368512303) ^ (29989 + 29989 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 29989 * (3 : ZMod 368512303) ^ 29989) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 337652762 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 368512303) ^ 119958 = 303268869 := by
        calc
          (3 : ZMod 368512303) ^ 119958 = (3 : ZMod 368512303) ^ (59979 + 59979) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 59979 * (3 : ZMod 368512303) ^ 59979 := by rw [pow_add]
          _ = 303268869 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 368512303) ^ 239916 = 168494994 := by
        calc
          (3 : ZMod 368512303) ^ 239916 = (3 : ZMod 368512303) ^ (119958 + 119958) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 119958 * (3 : ZMod 368512303) ^ 119958 := by rw [pow_add]
          _ = 168494994 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 368512303) ^ 479833 = 103246746 := by
        calc
          (3 : ZMod 368512303) ^ 479833 = (3 : ZMod 368512303) ^ (239916 + 239916 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 239916 * (3 : ZMod 368512303) ^ 239916) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 103246746 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 368512303) ^ 959667 = 86618532 := by
        calc
          (3 : ZMod 368512303) ^ 959667 = (3 : ZMod 368512303) ^ (479833 + 479833 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 479833 * (3 : ZMod 368512303) ^ 479833) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 86618532 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 368512303) ^ 1919334 = 368454770 := by
        calc
          (3 : ZMod 368512303) ^ 1919334 = (3 : ZMod 368512303) ^ (959667 + 959667) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 959667 * (3 : ZMod 368512303) ^ 959667 := by rw [pow_add]
          _ = 368454770 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 368512303) ^ 3838669 = 348818389 := by
        calc
          (3 : ZMod 368512303) ^ 3838669 = (3 : ZMod 368512303) ^ (1919334 + 1919334 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 1919334 * (3 : ZMod 368512303) ^ 1919334) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 348818389 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 368512303) ^ 7677339 = 50593807 := by
        calc
          (3 : ZMod 368512303) ^ 7677339 = (3 : ZMod 368512303) ^ (3838669 + 3838669 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 3838669 * (3 : ZMod 368512303) ^ 3838669) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 50593807 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 368512303) ^ 15354679 = 147158304 := by
        calc
          (3 : ZMod 368512303) ^ 15354679 = (3 : ZMod 368512303) ^ (7677339 + 7677339 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 7677339 * (3 : ZMod 368512303) ^ 7677339) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 147158304 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 368512303) ^ 30709358 = 280842199 := by
        calc
          (3 : ZMod 368512303) ^ 30709358 = (3 : ZMod 368512303) ^ (15354679 + 15354679) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 15354679 * (3 : ZMod 368512303) ^ 15354679 := by rw [pow_add]
          _ = 280842199 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 368512303) ^ 61418717 = 105501990 := by
        calc
          (3 : ZMod 368512303) ^ 61418717 = (3 : ZMod 368512303) ^ (30709358 + 30709358 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 30709358 * (3 : ZMod 368512303) ^ 30709358) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 105501990 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 368512303) ^ 122837434 = 105501989 := by
        calc
          (3 : ZMod 368512303) ^ 122837434 = (3 : ZMod 368512303) ^ (61418717 + 61418717) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 61418717 * (3 : ZMod 368512303) ^ 61418717 := by rw [pow_add]
          _ = 105501989 := by rw [factor_1_25]; decide
      change (3 : ZMod 368512303) ^ 122837434 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (3 : ZMod 368512303) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 368512303) ^ 3 = 27 := by
        calc
          (3 : ZMod 368512303) ^ 3 = (3 : ZMod 368512303) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 1 * (3 : ZMod 368512303) ^ 1) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 368512303) ^ 7 = 2187 := by
        calc
          (3 : ZMod 368512303) ^ 7 = (3 : ZMod 368512303) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 3 * (3 : ZMod 368512303) ^ 3) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 368512303) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 368512303) ^ 15 = (3 : ZMod 368512303) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 7 * (3 : ZMod 368512303) ^ 7) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 368512303) ^ 30 = 360310125 := by
        calc
          (3 : ZMod 368512303) ^ 30 = (3 : ZMod 368512303) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 15 * (3 : ZMod 368512303) ^ 15 := by rw [pow_add]
          _ = 360310125 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 368512303) ^ 61 = 353724012 := by
        calc
          (3 : ZMod 368512303) ^ 61 = (3 : ZMod 368512303) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 30 * (3 : ZMod 368512303) ^ 30) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 353724012 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 368512303) ^ 122 = 292997634 := by
        calc
          (3 : ZMod 368512303) ^ 122 = (3 : ZMod 368512303) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 61 * (3 : ZMod 368512303) ^ 61 := by rw [pow_add]
          _ = 292997634 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 368512303) ^ 244 = 94526600 := by
        calc
          (3 : ZMod 368512303) ^ 244 = (3 : ZMod 368512303) ^ (122 + 122) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 122 * (3 : ZMod 368512303) ^ 122 := by rw [pow_add]
          _ = 94526600 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 368512303) ^ 488 = 96047724 := by
        calc
          (3 : ZMod 368512303) ^ 488 = (3 : ZMod 368512303) ^ (244 + 244) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 244 * (3 : ZMod 368512303) ^ 244 := by rw [pow_add]
          _ = 96047724 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 368512303) ^ 977 = 57034122 := by
        calc
          (3 : ZMod 368512303) ^ 977 = (3 : ZMod 368512303) ^ (488 + 488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 488 * (3 : ZMod 368512303) ^ 488) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 57034122 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 368512303) ^ 1955 = 159892448 := by
        calc
          (3 : ZMod 368512303) ^ 1955 = (3 : ZMod 368512303) ^ (977 + 977 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 977 * (3 : ZMod 368512303) ^ 977) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 159892448 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 368512303) ^ 3911 = 312034398 := by
        calc
          (3 : ZMod 368512303) ^ 3911 = (3 : ZMod 368512303) ^ (1955 + 1955 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 1955 * (3 : ZMod 368512303) ^ 1955) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 312034398 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 368512303) ^ 7823 = 209658144 := by
        calc
          (3 : ZMod 368512303) ^ 7823 = (3 : ZMod 368512303) ^ (3911 + 3911 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 3911 * (3 : ZMod 368512303) ^ 3911) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 209658144 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 368512303) ^ 15646 = 326180465 := by
        calc
          (3 : ZMod 368512303) ^ 15646 = (3 : ZMod 368512303) ^ (7823 + 7823) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 7823 * (3 : ZMod 368512303) ^ 7823 := by rw [pow_add]
          _ = 326180465 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 368512303) ^ 31293 = 236011952 := by
        calc
          (3 : ZMod 368512303) ^ 31293 = (3 : ZMod 368512303) ^ (15646 + 15646 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 15646 * (3 : ZMod 368512303) ^ 15646) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 236011952 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 368512303) ^ 62587 = 338365524 := by
        calc
          (3 : ZMod 368512303) ^ 62587 = (3 : ZMod 368512303) ^ (31293 + 31293 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 31293 * (3 : ZMod 368512303) ^ 31293) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 338365524 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 368512303) ^ 125174 = 294317817 := by
        calc
          (3 : ZMod 368512303) ^ 125174 = (3 : ZMod 368512303) ^ (62587 + 62587) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 62587 * (3 : ZMod 368512303) ^ 62587 := by rw [pow_add]
          _ = 294317817 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 368512303) ^ 250348 = 79594619 := by
        calc
          (3 : ZMod 368512303) ^ 250348 = (3 : ZMod 368512303) ^ (125174 + 125174) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 125174 * (3 : ZMod 368512303) ^ 125174 := by rw [pow_add]
          _ = 79594619 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 368512303) ^ 500696 = 163430966 := by
        calc
          (3 : ZMod 368512303) ^ 500696 = (3 : ZMod 368512303) ^ (250348 + 250348) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 250348 * (3 : ZMod 368512303) ^ 250348 := by rw [pow_add]
          _ = 163430966 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 368512303) ^ 1001392 = 317304300 := by
        calc
          (3 : ZMod 368512303) ^ 1001392 = (3 : ZMod 368512303) ^ (500696 + 500696) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 500696 * (3 : ZMod 368512303) ^ 500696 := by rw [pow_add]
          _ = 317304300 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 368512303) ^ 2002784 = 94072912 := by
        calc
          (3 : ZMod 368512303) ^ 2002784 = (3 : ZMod 368512303) ^ (1001392 + 1001392) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1001392 * (3 : ZMod 368512303) ^ 1001392 := by rw [pow_add]
          _ = 94072912 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 368512303) ^ 4005568 = 793341 := by
        calc
          (3 : ZMod 368512303) ^ 4005568 = (3 : ZMod 368512303) ^ (2002784 + 2002784) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 2002784 * (3 : ZMod 368512303) ^ 2002784 := by rw [pow_add]
          _ = 793341 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 368512303) ^ 8011137 = 281298574 := by
        calc
          (3 : ZMod 368512303) ^ 8011137 = (3 : ZMod 368512303) ^ (4005568 + 4005568 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 4005568 * (3 : ZMod 368512303) ^ 4005568) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 281298574 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 368512303) ^ 16022274 = 188977998 := by
        calc
          (3 : ZMod 368512303) ^ 16022274 = (3 : ZMod 368512303) ^ (8011137 + 8011137) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 8011137 * (3 : ZMod 368512303) ^ 8011137 := by rw [pow_add]
          _ = 188977998 := by rw [factor_2_22]; decide
      change (3 : ZMod 368512303) ^ 16022274 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (3 : ZMod 368512303) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 368512303) ^ 2 = 9 := by
        calc
          (3 : ZMod 368512303) ^ 2 = (3 : ZMod 368512303) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1 * (3 : ZMod 368512303) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 368512303) ^ 4 = 81 := by
        calc
          (3 : ZMod 368512303) ^ 4 = (3 : ZMod 368512303) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 2 * (3 : ZMod 368512303) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 368512303) ^ 8 = 6561 := by
        calc
          (3 : ZMod 368512303) ^ 8 = (3 : ZMod 368512303) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 4 * (3 : ZMod 368512303) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 368512303) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 368512303) ^ 17 = (3 : ZMod 368512303) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 8 * (3 : ZMod 368512303) ^ 8) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 368512303) ^ 34 = 72648188 := by
        calc
          (3 : ZMod 368512303) ^ 34 = (3 : ZMod 368512303) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 17 * (3 : ZMod 368512303) ^ 17 := by rw [pow_add]
          _ = 72648188 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 368512303) ^ 69 = 261270741 := by
        calc
          (3 : ZMod 368512303) ^ 69 = (3 : ZMod 368512303) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 34 * (3 : ZMod 368512303) ^ 34) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 261270741 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 368512303) ^ 139 = 156431344 := by
        calc
          (3 : ZMod 368512303) ^ 139 = (3 : ZMod 368512303) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 69 * (3 : ZMod 368512303) ^ 69) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 156431344 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 368512303) ^ 279 = 301759693 := by
        calc
          (3 : ZMod 368512303) ^ 279 = (3 : ZMod 368512303) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 139 * (3 : ZMod 368512303) ^ 139) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 301759693 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 368512303) ^ 559 = 257321417 := by
        calc
          (3 : ZMod 368512303) ^ 559 = (3 : ZMod 368512303) ^ (279 + 279 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 279 * (3 : ZMod 368512303) ^ 279) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 257321417 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 368512303) ^ 1119 = 115939854 := by
        calc
          (3 : ZMod 368512303) ^ 1119 = (3 : ZMod 368512303) ^ (559 + 559 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 559 * (3 : ZMod 368512303) ^ 559) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 115939854 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 368512303) ^ 2238 = 38305029 := by
        calc
          (3 : ZMod 368512303) ^ 2238 = (3 : ZMod 368512303) ^ (1119 + 1119) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1119 * (3 : ZMod 368512303) ^ 1119 := by rw [pow_add]
          _ = 38305029 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 368512303) ^ 4477 = 83533761 := by
        calc
          (3 : ZMod 368512303) ^ 4477 = (3 : ZMod 368512303) ^ (2238 + 2238 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 2238 * (3 : ZMod 368512303) ^ 2238) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 83533761 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 368512303) ^ 8954 = 58370736 := by
        calc
          (3 : ZMod 368512303) ^ 8954 = (3 : ZMod 368512303) ^ (4477 + 4477) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 4477 * (3 : ZMod 368512303) ^ 4477 := by rw [pow_add]
          _ = 58370736 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 368512303) ^ 17909 = 135647967 := by
        calc
          (3 : ZMod 368512303) ^ 17909 = (3 : ZMod 368512303) ^ (8954 + 8954 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 8954 * (3 : ZMod 368512303) ^ 8954) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 135647967 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 368512303) ^ 35819 = 367088797 := by
        calc
          (3 : ZMod 368512303) ^ 35819 = (3 : ZMod 368512303) ^ (17909 + 17909 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 17909 * (3 : ZMod 368512303) ^ 17909) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 367088797 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 368512303) ^ 71639 = 129045820 := by
        calc
          (3 : ZMod 368512303) ^ 71639 = (3 : ZMod 368512303) ^ (35819 + 35819 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 35819 * (3 : ZMod 368512303) ^ 35819) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 129045820 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 368512303) ^ 143278 = 327170016 := by
        calc
          (3 : ZMod 368512303) ^ 143278 = (3 : ZMod 368512303) ^ (71639 + 71639) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 71639 * (3 : ZMod 368512303) ^ 71639 := by rw [pow_add]
          _ = 327170016 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 368512303) ^ 286557 = 196768507 := by
        calc
          (3 : ZMod 368512303) ^ 286557 = (3 : ZMod 368512303) ^ (143278 + 143278 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 143278 * (3 : ZMod 368512303) ^ 143278) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 196768507 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 368512303) ^ 573114 = 365479936 := by
        calc
          (3 : ZMod 368512303) ^ 573114 = (3 : ZMod 368512303) ^ (286557 + 286557) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 286557 * (3 : ZMod 368512303) ^ 286557 := by rw [pow_add]
          _ = 365479936 := by rw [factor_3_18]; decide
      change (3 : ZMod 368512303) ^ 573114 ≠ 1
      rw [factor_3_19]
      decide
    ·
      have factor_4_0 : (3 : ZMod 368512303) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 368512303) ^ 2 = 9 := by
        calc
          (3 : ZMod 368512303) ^ 2 = (3 : ZMod 368512303) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1 * (3 : ZMod 368512303) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 368512303) ^ 5 = 243 := by
        calc
          (3 : ZMod 368512303) ^ 5 = (3 : ZMod 368512303) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 2 * (3 : ZMod 368512303) ^ 2) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 368512303) ^ 10 = 59049 := by
        calc
          (3 : ZMod 368512303) ^ 10 = (3 : ZMod 368512303) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 5 * (3 : ZMod 368512303) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 368512303) ^ 21 = 142008719 := by
        calc
          (3 : ZMod 368512303) ^ 21 = (3 : ZMod 368512303) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 10 * (3 : ZMod 368512303) ^ 10) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 142008719 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 368512303) ^ 43 = 106548764 := by
        calc
          (3 : ZMod 368512303) ^ 43 = (3 : ZMod 368512303) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 21 * (3 : ZMod 368512303) ^ 21) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 106548764 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 368512303) ^ 86 = 357905171 := by
        calc
          (3 : ZMod 368512303) ^ 86 = (3 : ZMod 368512303) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 43 * (3 : ZMod 368512303) ^ 43 := by rw [pow_add]
          _ = 357905171 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 368512303) ^ 173 = 63035664 := by
        calc
          (3 : ZMod 368512303) ^ 173 = (3 : ZMod 368512303) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 86 * (3 : ZMod 368512303) ^ 86) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 63035664 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 368512303) ^ 346 = 341966609 := by
        calc
          (3 : ZMod 368512303) ^ 346 = (3 : ZMod 368512303) ^ (173 + 173) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 173 * (3 : ZMod 368512303) ^ 173 := by rw [pow_add]
          _ = 341966609 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 368512303) ^ 693 = 297479897 := by
        calc
          (3 : ZMod 368512303) ^ 693 = (3 : ZMod 368512303) ^ (346 + 346 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 346 * (3 : ZMod 368512303) ^ 346) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 297479897 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 368512303) ^ 1386 = 55736588 := by
        calc
          (3 : ZMod 368512303) ^ 1386 = (3 : ZMod 368512303) ^ (693 + 693) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 693 * (3 : ZMod 368512303) ^ 693 := by rw [pow_add]
          _ = 55736588 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 368512303) ^ 2772 = 51808775 := by
        calc
          (3 : ZMod 368512303) ^ 2772 = (3 : ZMod 368512303) ^ (1386 + 1386) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 1386 * (3 : ZMod 368512303) ^ 1386 := by rw [pow_add]
          _ = 51808775 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 368512303) ^ 5545 = 41806882 := by
        calc
          (3 : ZMod 368512303) ^ 5545 = (3 : ZMod 368512303) ^ (2772 + 2772 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 2772 * (3 : ZMod 368512303) ^ 2772) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 41806882 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 368512303) ^ 11091 = 301161914 := by
        calc
          (3 : ZMod 368512303) ^ 11091 = (3 : ZMod 368512303) ^ (5545 + 5545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 5545 * (3 : ZMod 368512303) ^ 5545) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 301161914 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 368512303) ^ 22183 = 261276674 := by
        calc
          (3 : ZMod 368512303) ^ 22183 = (3 : ZMod 368512303) ^ (11091 + 11091 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 11091 * (3 : ZMod 368512303) ^ 11091) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 261276674 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 368512303) ^ 44367 = 95855512 := by
        calc
          (3 : ZMod 368512303) ^ 44367 = (3 : ZMod 368512303) ^ (22183 + 22183 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = ((3 : ZMod 368512303) ^ 22183 * (3 : ZMod 368512303) ^ 22183) * (3 : ZMod 368512303) := by rw [pow_succ, pow_add]
          _ = 95855512 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 368512303) ^ 88734 = 153182127 := by
        calc
          (3 : ZMod 368512303) ^ 88734 = (3 : ZMod 368512303) ^ (44367 + 44367) :=
            congrArg (fun n : ℕ => (3 : ZMod 368512303) ^ n) (by norm_num)
          _ = (3 : ZMod 368512303) ^ 44367 * (3 : ZMod 368512303) ^ 44367 := by rw [pow_add]
          _ = 153182127 := by rw [factor_4_15]; decide
      change (3 : ZMod 368512303) ^ 88734 ≠ 1
      rw [factor_4_16]
      decide

#print axioms prime_lucas_368512303

end TotientTailPeriodKiller
end Erdos249257
