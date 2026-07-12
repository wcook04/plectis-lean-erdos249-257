import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_556736177 : Nat.Prime 556736177 := by
  apply lucas_primality 556736177 (3 : ZMod 556736177)
  ·
      have fermat_0 : (3 : ZMod 556736177) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 556736177) ^ 2 = 9 := by
        calc
          (3 : ZMod 556736177) ^ 2 = (3 : ZMod 556736177) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 1 * (3 : ZMod 556736177) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 556736177) ^ 4 = 81 := by
        calc
          (3 : ZMod 556736177) ^ 4 = (3 : ZMod 556736177) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 2 * (3 : ZMod 556736177) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 556736177) ^ 8 = 6561 := by
        calc
          (3 : ZMod 556736177) ^ 8 = (3 : ZMod 556736177) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 4 * (3 : ZMod 556736177) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 556736177) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 556736177) ^ 16 = (3 : ZMod 556736177) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 8 * (3 : ZMod 556736177) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 556736177) ^ 33 = 289690770 := by
        calc
          (3 : ZMod 556736177) ^ 33 = (3 : ZMod 556736177) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 16 * (3 : ZMod 556736177) ^ 16) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 289690770 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 556736177) ^ 66 = 554007723 := by
        calc
          (3 : ZMod 556736177) ^ 66 = (3 : ZMod 556736177) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 33 * (3 : ZMod 556736177) ^ 33 := by rw [pow_add]
          _ = 554007723 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 556736177) ^ 132 = 341807449 := by
        calc
          (3 : ZMod 556736177) ^ 132 = (3 : ZMod 556736177) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 66 * (3 : ZMod 556736177) ^ 66 := by rw [pow_add]
          _ = 341807449 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 556736177) ^ 265 = 88828956 := by
        calc
          (3 : ZMod 556736177) ^ 265 = (3 : ZMod 556736177) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 132 * (3 : ZMod 556736177) ^ 132) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 88828956 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 556736177) ^ 530 = 2225149 := by
        calc
          (3 : ZMod 556736177) ^ 530 = (3 : ZMod 556736177) ^ (265 + 265) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 265 * (3 : ZMod 556736177) ^ 265 := by rw [pow_add]
          _ = 2225149 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 556736177) ^ 1061 = 143014243 := by
        calc
          (3 : ZMod 556736177) ^ 1061 = (3 : ZMod 556736177) ^ (530 + 530 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 530 * (3 : ZMod 556736177) ^ 530) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 143014243 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 556736177) ^ 2123 = 333109356 := by
        calc
          (3 : ZMod 556736177) ^ 2123 = (3 : ZMod 556736177) ^ (1061 + 1061 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 1061 * (3 : ZMod 556736177) ^ 1061) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 333109356 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 556736177) ^ 4247 = 323397170 := by
        calc
          (3 : ZMod 556736177) ^ 4247 = (3 : ZMod 556736177) ^ (2123 + 2123 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 2123 * (3 : ZMod 556736177) ^ 2123) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 323397170 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 556736177) ^ 8495 = 307113308 := by
        calc
          (3 : ZMod 556736177) ^ 8495 = (3 : ZMod 556736177) ^ (4247 + 4247 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 4247 * (3 : ZMod 556736177) ^ 4247) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 307113308 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 556736177) ^ 16990 = 270254285 := by
        calc
          (3 : ZMod 556736177) ^ 16990 = (3 : ZMod 556736177) ^ (8495 + 8495) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 8495 * (3 : ZMod 556736177) ^ 8495 := by rw [pow_add]
          _ = 270254285 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 556736177) ^ 33980 = 171858495 := by
        calc
          (3 : ZMod 556736177) ^ 33980 = (3 : ZMod 556736177) ^ (16990 + 16990) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 16990 * (3 : ZMod 556736177) ^ 16990 := by rw [pow_add]
          _ = 171858495 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 556736177) ^ 67960 = 412923973 := by
        calc
          (3 : ZMod 556736177) ^ 67960 = (3 : ZMod 556736177) ^ (33980 + 33980) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 33980 * (3 : ZMod 556736177) ^ 33980 := by rw [pow_add]
          _ = 412923973 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 556736177) ^ 135921 = 437341010 := by
        calc
          (3 : ZMod 556736177) ^ 135921 = (3 : ZMod 556736177) ^ (67960 + 67960 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 67960 * (3 : ZMod 556736177) ^ 67960) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 437341010 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 556736177) ^ 271843 = 91585500 := by
        calc
          (3 : ZMod 556736177) ^ 271843 = (3 : ZMod 556736177) ^ (135921 + 135921 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 135921 * (3 : ZMod 556736177) ^ 135921) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 91585500 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 556736177) ^ 543687 = 72384844 := by
        calc
          (3 : ZMod 556736177) ^ 543687 = (3 : ZMod 556736177) ^ (271843 + 271843 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 271843 * (3 : ZMod 556736177) ^ 271843) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 72384844 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 556736177) ^ 1087375 = 332012250 := by
        calc
          (3 : ZMod 556736177) ^ 1087375 = (3 : ZMod 556736177) ^ (543687 + 543687 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 543687 * (3 : ZMod 556736177) ^ 543687) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 332012250 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 556736177) ^ 2174750 = 114116402 := by
        calc
          (3 : ZMod 556736177) ^ 2174750 = (3 : ZMod 556736177) ^ (1087375 + 1087375) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 1087375 * (3 : ZMod 556736177) ^ 1087375 := by rw [pow_add]
          _ = 114116402 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 556736177) ^ 4349501 = 44483638 := by
        calc
          (3 : ZMod 556736177) ^ 4349501 = (3 : ZMod 556736177) ^ (2174750 + 2174750 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 2174750 * (3 : ZMod 556736177) ^ 2174750) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 44483638 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 556736177) ^ 8699002 = 17472192 := by
        calc
          (3 : ZMod 556736177) ^ 8699002 = (3 : ZMod 556736177) ^ (4349501 + 4349501) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 4349501 * (3 : ZMod 556736177) ^ 4349501 := by rw [pow_add]
          _ = 17472192 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 556736177) ^ 17398005 = 355217238 := by
        calc
          (3 : ZMod 556736177) ^ 17398005 = (3 : ZMod 556736177) ^ (8699002 + 8699002 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 8699002 * (3 : ZMod 556736177) ^ 8699002) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 355217238 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 556736177) ^ 34796011 = 463562753 := by
        calc
          (3 : ZMod 556736177) ^ 34796011 = (3 : ZMod 556736177) ^ (17398005 + 17398005 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 17398005 * (3 : ZMod 556736177) ^ 17398005) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 463562753 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 556736177) ^ 69592022 = 76147093 := by
        calc
          (3 : ZMod 556736177) ^ 69592022 = (3 : ZMod 556736177) ^ (34796011 + 34796011) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 34796011 * (3 : ZMod 556736177) ^ 34796011 := by rw [pow_add]
          _ = 76147093 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 556736177) ^ 139184044 = 325704499 := by
        calc
          (3 : ZMod 556736177) ^ 139184044 = (3 : ZMod 556736177) ^ (69592022 + 69592022) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 69592022 * (3 : ZMod 556736177) ^ 69592022 := by rw [pow_add]
          _ = 325704499 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 556736177) ^ 278368088 = 556736176 := by
        calc
          (3 : ZMod 556736177) ^ 278368088 = (3 : ZMod 556736177) ^ (139184044 + 139184044) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 139184044 * (3 : ZMod 556736177) ^ 139184044 := by rw [pow_add]
          _ = 556736176 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 556736177) ^ 556736176 = 1 := by
        calc
          (3 : ZMod 556736177) ^ 556736176 = (3 : ZMod 556736177) ^ (278368088 + 278368088) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 278368088 * (3 : ZMod 556736177) ^ 278368088 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (19, 1), (1831369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (19, 1), (1831369, 1)] : List FactorBlock).map factorBlockValue).prod = 556736177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 556736177) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 556736177) ^ 2 = 9 := by
        calc
          (3 : ZMod 556736177) ^ 2 = (3 : ZMod 556736177) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 1 * (3 : ZMod 556736177) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 556736177) ^ 4 = 81 := by
        calc
          (3 : ZMod 556736177) ^ 4 = (3 : ZMod 556736177) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 2 * (3 : ZMod 556736177) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 556736177) ^ 8 = 6561 := by
        calc
          (3 : ZMod 556736177) ^ 8 = (3 : ZMod 556736177) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 4 * (3 : ZMod 556736177) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 556736177) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 556736177) ^ 16 = (3 : ZMod 556736177) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 8 * (3 : ZMod 556736177) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 556736177) ^ 33 = 289690770 := by
        calc
          (3 : ZMod 556736177) ^ 33 = (3 : ZMod 556736177) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 16 * (3 : ZMod 556736177) ^ 16) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 289690770 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 556736177) ^ 66 = 554007723 := by
        calc
          (3 : ZMod 556736177) ^ 66 = (3 : ZMod 556736177) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 33 * (3 : ZMod 556736177) ^ 33 := by rw [pow_add]
          _ = 554007723 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 556736177) ^ 132 = 341807449 := by
        calc
          (3 : ZMod 556736177) ^ 132 = (3 : ZMod 556736177) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 66 * (3 : ZMod 556736177) ^ 66 := by rw [pow_add]
          _ = 341807449 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 556736177) ^ 265 = 88828956 := by
        calc
          (3 : ZMod 556736177) ^ 265 = (3 : ZMod 556736177) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 132 * (3 : ZMod 556736177) ^ 132) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 88828956 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 556736177) ^ 530 = 2225149 := by
        calc
          (3 : ZMod 556736177) ^ 530 = (3 : ZMod 556736177) ^ (265 + 265) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 265 * (3 : ZMod 556736177) ^ 265 := by rw [pow_add]
          _ = 2225149 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 556736177) ^ 1061 = 143014243 := by
        calc
          (3 : ZMod 556736177) ^ 1061 = (3 : ZMod 556736177) ^ (530 + 530 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 530 * (3 : ZMod 556736177) ^ 530) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 143014243 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 556736177) ^ 2123 = 333109356 := by
        calc
          (3 : ZMod 556736177) ^ 2123 = (3 : ZMod 556736177) ^ (1061 + 1061 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 1061 * (3 : ZMod 556736177) ^ 1061) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 333109356 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 556736177) ^ 4247 = 323397170 := by
        calc
          (3 : ZMod 556736177) ^ 4247 = (3 : ZMod 556736177) ^ (2123 + 2123 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 2123 * (3 : ZMod 556736177) ^ 2123) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 323397170 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 556736177) ^ 8495 = 307113308 := by
        calc
          (3 : ZMod 556736177) ^ 8495 = (3 : ZMod 556736177) ^ (4247 + 4247 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 4247 * (3 : ZMod 556736177) ^ 4247) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 307113308 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 556736177) ^ 16990 = 270254285 := by
        calc
          (3 : ZMod 556736177) ^ 16990 = (3 : ZMod 556736177) ^ (8495 + 8495) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 8495 * (3 : ZMod 556736177) ^ 8495 := by rw [pow_add]
          _ = 270254285 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 556736177) ^ 33980 = 171858495 := by
        calc
          (3 : ZMod 556736177) ^ 33980 = (3 : ZMod 556736177) ^ (16990 + 16990) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 16990 * (3 : ZMod 556736177) ^ 16990 := by rw [pow_add]
          _ = 171858495 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 556736177) ^ 67960 = 412923973 := by
        calc
          (3 : ZMod 556736177) ^ 67960 = (3 : ZMod 556736177) ^ (33980 + 33980) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 33980 * (3 : ZMod 556736177) ^ 33980 := by rw [pow_add]
          _ = 412923973 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 556736177) ^ 135921 = 437341010 := by
        calc
          (3 : ZMod 556736177) ^ 135921 = (3 : ZMod 556736177) ^ (67960 + 67960 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 67960 * (3 : ZMod 556736177) ^ 67960) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 437341010 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 556736177) ^ 271843 = 91585500 := by
        calc
          (3 : ZMod 556736177) ^ 271843 = (3 : ZMod 556736177) ^ (135921 + 135921 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 135921 * (3 : ZMod 556736177) ^ 135921) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 91585500 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 556736177) ^ 543687 = 72384844 := by
        calc
          (3 : ZMod 556736177) ^ 543687 = (3 : ZMod 556736177) ^ (271843 + 271843 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 271843 * (3 : ZMod 556736177) ^ 271843) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 72384844 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 556736177) ^ 1087375 = 332012250 := by
        calc
          (3 : ZMod 556736177) ^ 1087375 = (3 : ZMod 556736177) ^ (543687 + 543687 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 543687 * (3 : ZMod 556736177) ^ 543687) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 332012250 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 556736177) ^ 2174750 = 114116402 := by
        calc
          (3 : ZMod 556736177) ^ 2174750 = (3 : ZMod 556736177) ^ (1087375 + 1087375) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 1087375 * (3 : ZMod 556736177) ^ 1087375 := by rw [pow_add]
          _ = 114116402 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 556736177) ^ 4349501 = 44483638 := by
        calc
          (3 : ZMod 556736177) ^ 4349501 = (3 : ZMod 556736177) ^ (2174750 + 2174750 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 2174750 * (3 : ZMod 556736177) ^ 2174750) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 44483638 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 556736177) ^ 8699002 = 17472192 := by
        calc
          (3 : ZMod 556736177) ^ 8699002 = (3 : ZMod 556736177) ^ (4349501 + 4349501) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 4349501 * (3 : ZMod 556736177) ^ 4349501 := by rw [pow_add]
          _ = 17472192 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 556736177) ^ 17398005 = 355217238 := by
        calc
          (3 : ZMod 556736177) ^ 17398005 = (3 : ZMod 556736177) ^ (8699002 + 8699002 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 8699002 * (3 : ZMod 556736177) ^ 8699002) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 355217238 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 556736177) ^ 34796011 = 463562753 := by
        calc
          (3 : ZMod 556736177) ^ 34796011 = (3 : ZMod 556736177) ^ (17398005 + 17398005 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 17398005 * (3 : ZMod 556736177) ^ 17398005) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 463562753 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 556736177) ^ 69592022 = 76147093 := by
        calc
          (3 : ZMod 556736177) ^ 69592022 = (3 : ZMod 556736177) ^ (34796011 + 34796011) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 34796011 * (3 : ZMod 556736177) ^ 34796011 := by rw [pow_add]
          _ = 76147093 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 556736177) ^ 139184044 = 325704499 := by
        calc
          (3 : ZMod 556736177) ^ 139184044 = (3 : ZMod 556736177) ^ (69592022 + 69592022) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 69592022 * (3 : ZMod 556736177) ^ 69592022 := by rw [pow_add]
          _ = 325704499 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 556736177) ^ 278368088 = 556736176 := by
        calc
          (3 : ZMod 556736177) ^ 278368088 = (3 : ZMod 556736177) ^ (139184044 + 139184044) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 139184044 * (3 : ZMod 556736177) ^ 139184044 := by rw [pow_add]
          _ = 556736176 := by rw [factor_0_27]; decide
      change (3 : ZMod 556736177) ^ 278368088 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (3 : ZMod 556736177) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 556736177) ^ 3 = 27 := by
        calc
          (3 : ZMod 556736177) ^ 3 = (3 : ZMod 556736177) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 1 * (3 : ZMod 556736177) ^ 1) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 556736177) ^ 6 = 729 := by
        calc
          (3 : ZMod 556736177) ^ 6 = (3 : ZMod 556736177) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 3 * (3 : ZMod 556736177) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 556736177) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 556736177) ^ 13 = (3 : ZMod 556736177) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 6 * (3 : ZMod 556736177) ^ 6) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 556736177) ^ 27 = 538804795 := by
        calc
          (3 : ZMod 556736177) ^ 27 = (3 : ZMod 556736177) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 13 * (3 : ZMod 556736177) ^ 13) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 538804795 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 556736177) ^ 55 = 54074864 := by
        calc
          (3 : ZMod 556736177) ^ 55 = (3 : ZMod 556736177) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 27 * (3 : ZMod 556736177) ^ 27) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 54074864 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 556736177) ^ 111 = 162920226 := by
        calc
          (3 : ZMod 556736177) ^ 111 = (3 : ZMod 556736177) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 55 * (3 : ZMod 556736177) ^ 55) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 162920226 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 556736177) ^ 223 = 125145332 := by
        calc
          (3 : ZMod 556736177) ^ 223 = (3 : ZMod 556736177) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 111 * (3 : ZMod 556736177) ^ 111) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 125145332 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 556736177) ^ 447 = 173608159 := by
        calc
          (3 : ZMod 556736177) ^ 447 = (3 : ZMod 556736177) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 223 * (3 : ZMod 556736177) ^ 223) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 173608159 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 556736177) ^ 894 = 286314621 := by
        calc
          (3 : ZMod 556736177) ^ 894 = (3 : ZMod 556736177) ^ (447 + 447) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 447 * (3 : ZMod 556736177) ^ 447 := by rw [pow_add]
          _ = 286314621 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 556736177) ^ 1788 = 552185641 := by
        calc
          (3 : ZMod 556736177) ^ 1788 = (3 : ZMod 556736177) ^ (894 + 894) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 894 * (3 : ZMod 556736177) ^ 894 := by rw [pow_add]
          _ = 552185641 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 556736177) ^ 3576 = 132519958 := by
        calc
          (3 : ZMod 556736177) ^ 3576 = (3 : ZMod 556736177) ^ (1788 + 1788) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 1788 * (3 : ZMod 556736177) ^ 1788 := by rw [pow_add]
          _ = 132519958 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 556736177) ^ 7153 = 281417299 := by
        calc
          (3 : ZMod 556736177) ^ 7153 = (3 : ZMod 556736177) ^ (3576 + 3576 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 3576 * (3 : ZMod 556736177) ^ 3576) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 281417299 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 556736177) ^ 14307 = 154000098 := by
        calc
          (3 : ZMod 556736177) ^ 14307 = (3 : ZMod 556736177) ^ (7153 + 7153 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 7153 * (3 : ZMod 556736177) ^ 7153) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 154000098 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 556736177) ^ 28615 = 276828821 := by
        calc
          (3 : ZMod 556736177) ^ 28615 = (3 : ZMod 556736177) ^ (14307 + 14307 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 14307 * (3 : ZMod 556736177) ^ 14307) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 276828821 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 556736177) ^ 57230 = 292819377 := by
        calc
          (3 : ZMod 556736177) ^ 57230 = (3 : ZMod 556736177) ^ (28615 + 28615) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 28615 * (3 : ZMod 556736177) ^ 28615 := by rw [pow_add]
          _ = 292819377 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 556736177) ^ 114460 = 65827010 := by
        calc
          (3 : ZMod 556736177) ^ 114460 = (3 : ZMod 556736177) ^ (57230 + 57230) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 57230 * (3 : ZMod 556736177) ^ 57230 := by rw [pow_add]
          _ = 65827010 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 556736177) ^ 228921 = 325847259 := by
        calc
          (3 : ZMod 556736177) ^ 228921 = (3 : ZMod 556736177) ^ (114460 + 114460 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 114460 * (3 : ZMod 556736177) ^ 114460) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 325847259 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 556736177) ^ 457842 = 502408335 := by
        calc
          (3 : ZMod 556736177) ^ 457842 = (3 : ZMod 556736177) ^ (228921 + 228921) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 228921 * (3 : ZMod 556736177) ^ 228921 := by rw [pow_add]
          _ = 502408335 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 556736177) ^ 915684 = 400194721 := by
        calc
          (3 : ZMod 556736177) ^ 915684 = (3 : ZMod 556736177) ^ (457842 + 457842) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 457842 * (3 : ZMod 556736177) ^ 457842 := by rw [pow_add]
          _ = 400194721 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 556736177) ^ 1831369 = 209676661 := by
        calc
          (3 : ZMod 556736177) ^ 1831369 = (3 : ZMod 556736177) ^ (915684 + 915684 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 915684 * (3 : ZMod 556736177) ^ 915684) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 209676661 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 556736177) ^ 3662738 = 384513842 := by
        calc
          (3 : ZMod 556736177) ^ 3662738 = (3 : ZMod 556736177) ^ (1831369 + 1831369) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 1831369 * (3 : ZMod 556736177) ^ 1831369 := by rw [pow_add]
          _ = 384513842 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 556736177) ^ 7325476 = 301670068 := by
        calc
          (3 : ZMod 556736177) ^ 7325476 = (3 : ZMod 556736177) ^ (3662738 + 3662738) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 3662738 * (3 : ZMod 556736177) ^ 3662738 := by rw [pow_add]
          _ = 301670068 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 556736177) ^ 14650952 = 99687161 := by
        calc
          (3 : ZMod 556736177) ^ 14650952 = (3 : ZMod 556736177) ^ (7325476 + 7325476) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 7325476 * (3 : ZMod 556736177) ^ 7325476 := by rw [pow_add]
          _ = 99687161 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 556736177) ^ 29301904 = 311801004 := by
        calc
          (3 : ZMod 556736177) ^ 29301904 = (3 : ZMod 556736177) ^ (14650952 + 14650952) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 14650952 * (3 : ZMod 556736177) ^ 14650952 := by rw [pow_add]
          _ = 311801004 := by rw [factor_1_23]; decide
      change (3 : ZMod 556736177) ^ 29301904 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (3 : ZMod 556736177) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 556736177) ^ 2 = 9 := by
        calc
          (3 : ZMod 556736177) ^ 2 = (3 : ZMod 556736177) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 1 * (3 : ZMod 556736177) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 556736177) ^ 4 = 81 := by
        calc
          (3 : ZMod 556736177) ^ 4 = (3 : ZMod 556736177) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 2 * (3 : ZMod 556736177) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 556736177) ^ 9 = 19683 := by
        calc
          (3 : ZMod 556736177) ^ 9 = (3 : ZMod 556736177) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 4 * (3 : ZMod 556736177) ^ 4) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 556736177) ^ 19 = 48789113 := by
        calc
          (3 : ZMod 556736177) ^ 19 = (3 : ZMod 556736177) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = ((3 : ZMod 556736177) ^ 9 * (3 : ZMod 556736177) ^ 9) * (3 : ZMod 556736177) := by rw [pow_succ, pow_add]
          _ = 48789113 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 556736177) ^ 38 = 246098808 := by
        calc
          (3 : ZMod 556736177) ^ 38 = (3 : ZMod 556736177) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 19 * (3 : ZMod 556736177) ^ 19 := by rw [pow_add]
          _ = 246098808 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 556736177) ^ 76 = 341011084 := by
        calc
          (3 : ZMod 556736177) ^ 76 = (3 : ZMod 556736177) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 38 * (3 : ZMod 556736177) ^ 38 := by rw [pow_add]
          _ = 341011084 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 556736177) ^ 152 = 380431839 := by
        calc
          (3 : ZMod 556736177) ^ 152 = (3 : ZMod 556736177) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 76 * (3 : ZMod 556736177) ^ 76 := by rw [pow_add]
          _ = 380431839 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 556736177) ^ 304 = 259313225 := by
        calc
          (3 : ZMod 556736177) ^ 304 = (3 : ZMod 556736177) ^ (152 + 152) :=
            congrArg (fun n : ℕ => (3 : ZMod 556736177) ^ n) (by norm_num)
          _ = (3 : ZMod 556736177) ^ 152 * (3 : ZMod 556736177) ^ 152 := by rw [pow_add]
          _ = 259313225 := by rw [factor_2_7]; decide
      change (3 : ZMod 556736177) ^ 304 ≠ 1
      rw [factor_2_8]
      decide

#print axioms prime_lucas_556736177

end TotientTailPeriodKiller
end Erdos249257
