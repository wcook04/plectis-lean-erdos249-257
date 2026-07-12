import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_823727521 : Nat.Prime 823727521 := by
  apply lucas_primality 823727521 (26 : ZMod 823727521)
  ·
      have fermat_0 : (26 : ZMod 823727521) ^ 1 = 26 := by norm_num
      have fermat_1 : (26 : ZMod 823727521) ^ 3 = 17576 := by
        calc
          (26 : ZMod 823727521) ^ 3 = (26 : ZMod 823727521) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1 * (26 : ZMod 823727521) ^ 1) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [fermat_0]; decide
      have fermat_2 : (26 : ZMod 823727521) ^ 6 = 308915776 := by
        calc
          (26 : ZMod 823727521) ^ 6 = (26 : ZMod 823727521) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 3 * (26 : ZMod 823727521) ^ 3 := by rw [pow_add]
          _ = 308915776 := by rw [fermat_1]; decide
      have fermat_3 : (26 : ZMod 823727521) ^ 12 = 618431547 := by
        calc
          (26 : ZMod 823727521) ^ 12 = (26 : ZMod 823727521) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 6 * (26 : ZMod 823727521) ^ 6 := by rw [pow_add]
          _ = 618431547 := by rw [fermat_2]; decide
      have fermat_4 : (26 : ZMod 823727521) ^ 24 = 698790529 := by
        calc
          (26 : ZMod 823727521) ^ 24 = (26 : ZMod 823727521) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 12 * (26 : ZMod 823727521) ^ 12 := by rw [pow_add]
          _ = 698790529 := by rw [fermat_3]; decide
      have fermat_5 : (26 : ZMod 823727521) ^ 49 = 28159562 := by
        calc
          (26 : ZMod 823727521) ^ 49 = (26 : ZMod 823727521) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 24 * (26 : ZMod 823727521) ^ 24) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 28159562 := by rw [fermat_4]; decide
      have fermat_6 : (26 : ZMod 823727521) ^ 98 = 457668715 := by
        calc
          (26 : ZMod 823727521) ^ 98 = (26 : ZMod 823727521) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 49 * (26 : ZMod 823727521) ^ 49 := by rw [pow_add]
          _ = 457668715 := by rw [fermat_5]; decide
      have fermat_7 : (26 : ZMod 823727521) ^ 196 = 346446678 := by
        calc
          (26 : ZMod 823727521) ^ 196 = (26 : ZMod 823727521) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 98 * (26 : ZMod 823727521) ^ 98 := by rw [pow_add]
          _ = 346446678 := by rw [fermat_6]; decide
      have fermat_8 : (26 : ZMod 823727521) ^ 392 = 680064129 := by
        calc
          (26 : ZMod 823727521) ^ 392 = (26 : ZMod 823727521) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 196 * (26 : ZMod 823727521) ^ 196 := by rw [pow_add]
          _ = 680064129 := by rw [fermat_7]; decide
      have fermat_9 : (26 : ZMod 823727521) ^ 785 = 691250931 := by
        calc
          (26 : ZMod 823727521) ^ 785 = (26 : ZMod 823727521) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 392 * (26 : ZMod 823727521) ^ 392) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 691250931 := by rw [fermat_8]; decide
      have fermat_10 : (26 : ZMod 823727521) ^ 1571 = 784940447 := by
        calc
          (26 : ZMod 823727521) ^ 1571 = (26 : ZMod 823727521) ^ (785 + 785 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 785 * (26 : ZMod 823727521) ^ 785) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 784940447 := by rw [fermat_9]; decide
      have fermat_11 : (26 : ZMod 823727521) ^ 3142 = 110860059 := by
        calc
          (26 : ZMod 823727521) ^ 3142 = (26 : ZMod 823727521) ^ (1571 + 1571) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1571 * (26 : ZMod 823727521) ^ 1571 := by rw [pow_add]
          _ = 110860059 := by rw [fermat_10]; decide
      have fermat_12 : (26 : ZMod 823727521) ^ 6284 = 671455077 := by
        calc
          (26 : ZMod 823727521) ^ 6284 = (26 : ZMod 823727521) ^ (3142 + 3142) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 3142 * (26 : ZMod 823727521) ^ 3142 := by rw [pow_add]
          _ = 671455077 := by rw [fermat_11]; decide
      have fermat_13 : (26 : ZMod 823727521) ^ 12569 = 728798447 := by
        calc
          (26 : ZMod 823727521) ^ 12569 = (26 : ZMod 823727521) ^ (6284 + 6284 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 6284 * (26 : ZMod 823727521) ^ 6284) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 728798447 := by rw [fermat_12]; decide
      have fermat_14 : (26 : ZMod 823727521) ^ 25138 = 258136257 := by
        calc
          (26 : ZMod 823727521) ^ 25138 = (26 : ZMod 823727521) ^ (12569 + 12569) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 12569 * (26 : ZMod 823727521) ^ 12569 := by rw [pow_add]
          _ = 258136257 := by rw [fermat_13]; decide
      have fermat_15 : (26 : ZMod 823727521) ^ 50276 = 575100878 := by
        calc
          (26 : ZMod 823727521) ^ 50276 = (26 : ZMod 823727521) ^ (25138 + 25138) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 25138 * (26 : ZMod 823727521) ^ 25138 := by rw [pow_add]
          _ = 575100878 := by rw [fermat_14]; decide
      have fermat_16 : (26 : ZMod 823727521) ^ 100552 = 20888258 := by
        calc
          (26 : ZMod 823727521) ^ 100552 = (26 : ZMod 823727521) ^ (50276 + 50276) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 50276 * (26 : ZMod 823727521) ^ 50276 := by rw [pow_add]
          _ = 20888258 := by rw [fermat_15]; decide
      have fermat_17 : (26 : ZMod 823727521) ^ 201105 = 271676033 := by
        calc
          (26 : ZMod 823727521) ^ 201105 = (26 : ZMod 823727521) ^ (100552 + 100552 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 100552 * (26 : ZMod 823727521) ^ 100552) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 271676033 := by rw [fermat_16]; decide
      have fermat_18 : (26 : ZMod 823727521) ^ 402210 = 455086646 := by
        calc
          (26 : ZMod 823727521) ^ 402210 = (26 : ZMod 823727521) ^ (201105 + 201105) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 201105 * (26 : ZMod 823727521) ^ 201105 := by rw [pow_add]
          _ = 455086646 := by rw [fermat_17]; decide
      have fermat_19 : (26 : ZMod 823727521) ^ 804421 = 710832107 := by
        calc
          (26 : ZMod 823727521) ^ 804421 = (26 : ZMod 823727521) ^ (402210 + 402210 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 402210 * (26 : ZMod 823727521) ^ 402210) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 710832107 := by rw [fermat_18]; decide
      have fermat_20 : (26 : ZMod 823727521) ^ 1608842 = 20392512 := by
        calc
          (26 : ZMod 823727521) ^ 1608842 = (26 : ZMod 823727521) ^ (804421 + 804421) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 804421 * (26 : ZMod 823727521) ^ 804421 := by rw [pow_add]
          _ = 20392512 := by rw [fermat_19]; decide
      have fermat_21 : (26 : ZMod 823727521) ^ 3217685 = 400968500 := by
        calc
          (26 : ZMod 823727521) ^ 3217685 = (26 : ZMod 823727521) ^ (1608842 + 1608842 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1608842 * (26 : ZMod 823727521) ^ 1608842) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 400968500 := by rw [fermat_20]; decide
      have fermat_22 : (26 : ZMod 823727521) ^ 6435371 = 246242008 := by
        calc
          (26 : ZMod 823727521) ^ 6435371 = (26 : ZMod 823727521) ^ (3217685 + 3217685 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 3217685 * (26 : ZMod 823727521) ^ 3217685) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 246242008 := by rw [fermat_21]; decide
      have fermat_23 : (26 : ZMod 823727521) ^ 12870742 = 22898204 := by
        calc
          (26 : ZMod 823727521) ^ 12870742 = (26 : ZMod 823727521) ^ (6435371 + 6435371) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 6435371 * (26 : ZMod 823727521) ^ 6435371 := by rw [pow_add]
          _ = 22898204 := by rw [fermat_22]; decide
      have fermat_24 : (26 : ZMod 823727521) ^ 25741485 = 622385342 := by
        calc
          (26 : ZMod 823727521) ^ 25741485 = (26 : ZMod 823727521) ^ (12870742 + 12870742 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 12870742 * (26 : ZMod 823727521) ^ 12870742) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 622385342 := by rw [fermat_23]; decide
      have fermat_25 : (26 : ZMod 823727521) ^ 51482970 = 534050509 := by
        calc
          (26 : ZMod 823727521) ^ 51482970 = (26 : ZMod 823727521) ^ (25741485 + 25741485) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 25741485 * (26 : ZMod 823727521) ^ 25741485 := by rw [pow_add]
          _ = 534050509 := by rw [fermat_24]; decide
      have fermat_26 : (26 : ZMod 823727521) ^ 102965940 = 448629611 := by
        calc
          (26 : ZMod 823727521) ^ 102965940 = (26 : ZMod 823727521) ^ (51482970 + 51482970) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 51482970 * (26 : ZMod 823727521) ^ 51482970 := by rw [pow_add]
          _ = 448629611 := by rw [fermat_25]; decide
      have fermat_27 : (26 : ZMod 823727521) ^ 205931880 = 579825722 := by
        calc
          (26 : ZMod 823727521) ^ 205931880 = (26 : ZMod 823727521) ^ (102965940 + 102965940) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 102965940 * (26 : ZMod 823727521) ^ 102965940 := by rw [pow_add]
          _ = 579825722 := by rw [fermat_26]; decide
      have fermat_28 : (26 : ZMod 823727521) ^ 411863760 = 823727520 := by
        calc
          (26 : ZMod 823727521) ^ 411863760 = (26 : ZMod 823727521) ^ (205931880 + 205931880) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 205931880 * (26 : ZMod 823727521) ^ 205931880 := by rw [pow_add]
          _ = 823727520 := by rw [fermat_27]; decide
      have fermat_29 : (26 : ZMod 823727521) ^ 823727520 = 1 := by
        calc
          (26 : ZMod 823727521) ^ 823727520 = (26 : ZMod 823727521) ^ (411863760 + 411863760) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 411863760 * (26 : ZMod 823727521) ^ 411863760 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (5, 1), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (5, 1), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 823727521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (26 : ZMod 823727521) ^ 1 = 26 := by norm_num
      have factor_0_1 : (26 : ZMod 823727521) ^ 3 = 17576 := by
        calc
          (26 : ZMod 823727521) ^ 3 = (26 : ZMod 823727521) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1 * (26 : ZMod 823727521) ^ 1) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [factor_0_0]; decide
      have factor_0_2 : (26 : ZMod 823727521) ^ 6 = 308915776 := by
        calc
          (26 : ZMod 823727521) ^ 6 = (26 : ZMod 823727521) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 3 * (26 : ZMod 823727521) ^ 3 := by rw [pow_add]
          _ = 308915776 := by rw [factor_0_1]; decide
      have factor_0_3 : (26 : ZMod 823727521) ^ 12 = 618431547 := by
        calc
          (26 : ZMod 823727521) ^ 12 = (26 : ZMod 823727521) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 6 * (26 : ZMod 823727521) ^ 6 := by rw [pow_add]
          _ = 618431547 := by rw [factor_0_2]; decide
      have factor_0_4 : (26 : ZMod 823727521) ^ 24 = 698790529 := by
        calc
          (26 : ZMod 823727521) ^ 24 = (26 : ZMod 823727521) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 12 * (26 : ZMod 823727521) ^ 12 := by rw [pow_add]
          _ = 698790529 := by rw [factor_0_3]; decide
      have factor_0_5 : (26 : ZMod 823727521) ^ 49 = 28159562 := by
        calc
          (26 : ZMod 823727521) ^ 49 = (26 : ZMod 823727521) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 24 * (26 : ZMod 823727521) ^ 24) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 28159562 := by rw [factor_0_4]; decide
      have factor_0_6 : (26 : ZMod 823727521) ^ 98 = 457668715 := by
        calc
          (26 : ZMod 823727521) ^ 98 = (26 : ZMod 823727521) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 49 * (26 : ZMod 823727521) ^ 49 := by rw [pow_add]
          _ = 457668715 := by rw [factor_0_5]; decide
      have factor_0_7 : (26 : ZMod 823727521) ^ 196 = 346446678 := by
        calc
          (26 : ZMod 823727521) ^ 196 = (26 : ZMod 823727521) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 98 * (26 : ZMod 823727521) ^ 98 := by rw [pow_add]
          _ = 346446678 := by rw [factor_0_6]; decide
      have factor_0_8 : (26 : ZMod 823727521) ^ 392 = 680064129 := by
        calc
          (26 : ZMod 823727521) ^ 392 = (26 : ZMod 823727521) ^ (196 + 196) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 196 * (26 : ZMod 823727521) ^ 196 := by rw [pow_add]
          _ = 680064129 := by rw [factor_0_7]; decide
      have factor_0_9 : (26 : ZMod 823727521) ^ 785 = 691250931 := by
        calc
          (26 : ZMod 823727521) ^ 785 = (26 : ZMod 823727521) ^ (392 + 392 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 392 * (26 : ZMod 823727521) ^ 392) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 691250931 := by rw [factor_0_8]; decide
      have factor_0_10 : (26 : ZMod 823727521) ^ 1571 = 784940447 := by
        calc
          (26 : ZMod 823727521) ^ 1571 = (26 : ZMod 823727521) ^ (785 + 785 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 785 * (26 : ZMod 823727521) ^ 785) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 784940447 := by rw [factor_0_9]; decide
      have factor_0_11 : (26 : ZMod 823727521) ^ 3142 = 110860059 := by
        calc
          (26 : ZMod 823727521) ^ 3142 = (26 : ZMod 823727521) ^ (1571 + 1571) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1571 * (26 : ZMod 823727521) ^ 1571 := by rw [pow_add]
          _ = 110860059 := by rw [factor_0_10]; decide
      have factor_0_12 : (26 : ZMod 823727521) ^ 6284 = 671455077 := by
        calc
          (26 : ZMod 823727521) ^ 6284 = (26 : ZMod 823727521) ^ (3142 + 3142) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 3142 * (26 : ZMod 823727521) ^ 3142 := by rw [pow_add]
          _ = 671455077 := by rw [factor_0_11]; decide
      have factor_0_13 : (26 : ZMod 823727521) ^ 12569 = 728798447 := by
        calc
          (26 : ZMod 823727521) ^ 12569 = (26 : ZMod 823727521) ^ (6284 + 6284 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 6284 * (26 : ZMod 823727521) ^ 6284) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 728798447 := by rw [factor_0_12]; decide
      have factor_0_14 : (26 : ZMod 823727521) ^ 25138 = 258136257 := by
        calc
          (26 : ZMod 823727521) ^ 25138 = (26 : ZMod 823727521) ^ (12569 + 12569) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 12569 * (26 : ZMod 823727521) ^ 12569 := by rw [pow_add]
          _ = 258136257 := by rw [factor_0_13]; decide
      have factor_0_15 : (26 : ZMod 823727521) ^ 50276 = 575100878 := by
        calc
          (26 : ZMod 823727521) ^ 50276 = (26 : ZMod 823727521) ^ (25138 + 25138) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 25138 * (26 : ZMod 823727521) ^ 25138 := by rw [pow_add]
          _ = 575100878 := by rw [factor_0_14]; decide
      have factor_0_16 : (26 : ZMod 823727521) ^ 100552 = 20888258 := by
        calc
          (26 : ZMod 823727521) ^ 100552 = (26 : ZMod 823727521) ^ (50276 + 50276) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 50276 * (26 : ZMod 823727521) ^ 50276 := by rw [pow_add]
          _ = 20888258 := by rw [factor_0_15]; decide
      have factor_0_17 : (26 : ZMod 823727521) ^ 201105 = 271676033 := by
        calc
          (26 : ZMod 823727521) ^ 201105 = (26 : ZMod 823727521) ^ (100552 + 100552 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 100552 * (26 : ZMod 823727521) ^ 100552) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 271676033 := by rw [factor_0_16]; decide
      have factor_0_18 : (26 : ZMod 823727521) ^ 402210 = 455086646 := by
        calc
          (26 : ZMod 823727521) ^ 402210 = (26 : ZMod 823727521) ^ (201105 + 201105) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 201105 * (26 : ZMod 823727521) ^ 201105 := by rw [pow_add]
          _ = 455086646 := by rw [factor_0_17]; decide
      have factor_0_19 : (26 : ZMod 823727521) ^ 804421 = 710832107 := by
        calc
          (26 : ZMod 823727521) ^ 804421 = (26 : ZMod 823727521) ^ (402210 + 402210 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 402210 * (26 : ZMod 823727521) ^ 402210) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 710832107 := by rw [factor_0_18]; decide
      have factor_0_20 : (26 : ZMod 823727521) ^ 1608842 = 20392512 := by
        calc
          (26 : ZMod 823727521) ^ 1608842 = (26 : ZMod 823727521) ^ (804421 + 804421) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 804421 * (26 : ZMod 823727521) ^ 804421 := by rw [pow_add]
          _ = 20392512 := by rw [factor_0_19]; decide
      have factor_0_21 : (26 : ZMod 823727521) ^ 3217685 = 400968500 := by
        calc
          (26 : ZMod 823727521) ^ 3217685 = (26 : ZMod 823727521) ^ (1608842 + 1608842 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1608842 * (26 : ZMod 823727521) ^ 1608842) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 400968500 := by rw [factor_0_20]; decide
      have factor_0_22 : (26 : ZMod 823727521) ^ 6435371 = 246242008 := by
        calc
          (26 : ZMod 823727521) ^ 6435371 = (26 : ZMod 823727521) ^ (3217685 + 3217685 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 3217685 * (26 : ZMod 823727521) ^ 3217685) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 246242008 := by rw [factor_0_21]; decide
      have factor_0_23 : (26 : ZMod 823727521) ^ 12870742 = 22898204 := by
        calc
          (26 : ZMod 823727521) ^ 12870742 = (26 : ZMod 823727521) ^ (6435371 + 6435371) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 6435371 * (26 : ZMod 823727521) ^ 6435371 := by rw [pow_add]
          _ = 22898204 := by rw [factor_0_22]; decide
      have factor_0_24 : (26 : ZMod 823727521) ^ 25741485 = 622385342 := by
        calc
          (26 : ZMod 823727521) ^ 25741485 = (26 : ZMod 823727521) ^ (12870742 + 12870742 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 12870742 * (26 : ZMod 823727521) ^ 12870742) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 622385342 := by rw [factor_0_23]; decide
      have factor_0_25 : (26 : ZMod 823727521) ^ 51482970 = 534050509 := by
        calc
          (26 : ZMod 823727521) ^ 51482970 = (26 : ZMod 823727521) ^ (25741485 + 25741485) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 25741485 * (26 : ZMod 823727521) ^ 25741485 := by rw [pow_add]
          _ = 534050509 := by rw [factor_0_24]; decide
      have factor_0_26 : (26 : ZMod 823727521) ^ 102965940 = 448629611 := by
        calc
          (26 : ZMod 823727521) ^ 102965940 = (26 : ZMod 823727521) ^ (51482970 + 51482970) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 51482970 * (26 : ZMod 823727521) ^ 51482970 := by rw [pow_add]
          _ = 448629611 := by rw [factor_0_25]; decide
      have factor_0_27 : (26 : ZMod 823727521) ^ 205931880 = 579825722 := by
        calc
          (26 : ZMod 823727521) ^ 205931880 = (26 : ZMod 823727521) ^ (102965940 + 102965940) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 102965940 * (26 : ZMod 823727521) ^ 102965940 := by rw [pow_add]
          _ = 579825722 := by rw [factor_0_26]; decide
      have factor_0_28 : (26 : ZMod 823727521) ^ 411863760 = 823727520 := by
        calc
          (26 : ZMod 823727521) ^ 411863760 = (26 : ZMod 823727521) ^ (205931880 + 205931880) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 205931880 * (26 : ZMod 823727521) ^ 205931880 := by rw [pow_add]
          _ = 823727520 := by rw [factor_0_27]; decide
      change (26 : ZMod 823727521) ^ 411863760 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (26 : ZMod 823727521) ^ 1 = 26 := by norm_num
      have factor_1_1 : (26 : ZMod 823727521) ^ 2 = 676 := by
        calc
          (26 : ZMod 823727521) ^ 2 = (26 : ZMod 823727521) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1 * (26 : ZMod 823727521) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_1_0]; decide
      have factor_1_2 : (26 : ZMod 823727521) ^ 4 = 456976 := by
        calc
          (26 : ZMod 823727521) ^ 4 = (26 : ZMod 823727521) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2 * (26 : ZMod 823727521) ^ 2 := by rw [pow_add]
          _ = 456976 := by rw [factor_1_1]; decide
      have factor_1_3 : (26 : ZMod 823727521) ^ 8 = 424001763 := by
        calc
          (26 : ZMod 823727521) ^ 8 = (26 : ZMod 823727521) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 4 * (26 : ZMod 823727521) ^ 4 := by rw [pow_add]
          _ = 424001763 := by rw [factor_1_2]; decide
      have factor_1_4 : (26 : ZMod 823727521) ^ 16 = 641807108 := by
        calc
          (26 : ZMod 823727521) ^ 16 = (26 : ZMod 823727521) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 8 * (26 : ZMod 823727521) ^ 8 := by rw [pow_add]
          _ = 641807108 := by rw [factor_1_3]; decide
      have factor_1_5 : (26 : ZMod 823727521) ^ 32 = 139832604 := by
        calc
          (26 : ZMod 823727521) ^ 32 = (26 : ZMod 823727521) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 16 * (26 : ZMod 823727521) ^ 16 := by rw [pow_add]
          _ = 139832604 := by rw [factor_1_4]; decide
      have factor_1_6 : (26 : ZMod 823727521) ^ 65 = 195625860 := by
        calc
          (26 : ZMod 823727521) ^ 65 = (26 : ZMod 823727521) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 32 * (26 : ZMod 823727521) ^ 32) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 195625860 := by rw [factor_1_5]; decide
      have factor_1_7 : (26 : ZMod 823727521) ^ 130 = 104170137 := by
        calc
          (26 : ZMod 823727521) ^ 130 = (26 : ZMod 823727521) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 65 * (26 : ZMod 823727521) ^ 65 := by rw [pow_add]
          _ = 104170137 := by rw [factor_1_6]; decide
      have factor_1_8 : (26 : ZMod 823727521) ^ 261 = 411546039 := by
        calc
          (26 : ZMod 823727521) ^ 261 = (26 : ZMod 823727521) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 130 * (26 : ZMod 823727521) ^ 130) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 411546039 := by rw [factor_1_7]; decide
      have factor_1_9 : (26 : ZMod 823727521) ^ 523 = 636722473 := by
        calc
          (26 : ZMod 823727521) ^ 523 = (26 : ZMod 823727521) ^ (261 + 261 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 261 * (26 : ZMod 823727521) ^ 261) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 636722473 := by rw [factor_1_8]; decide
      have factor_1_10 : (26 : ZMod 823727521) ^ 1047 = 574927428 := by
        calc
          (26 : ZMod 823727521) ^ 1047 = (26 : ZMod 823727521) ^ (523 + 523 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 523 * (26 : ZMod 823727521) ^ 523) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 574927428 := by rw [factor_1_9]; decide
      have factor_1_11 : (26 : ZMod 823727521) ^ 2094 = 643970397 := by
        calc
          (26 : ZMod 823727521) ^ 2094 = (26 : ZMod 823727521) ^ (1047 + 1047) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1047 * (26 : ZMod 823727521) ^ 1047 := by rw [pow_add]
          _ = 643970397 := by rw [factor_1_10]; decide
      have factor_1_12 : (26 : ZMod 823727521) ^ 4189 = 808251199 := by
        calc
          (26 : ZMod 823727521) ^ 4189 = (26 : ZMod 823727521) ^ (2094 + 2094 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 2094 * (26 : ZMod 823727521) ^ 2094) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 808251199 := by rw [factor_1_11]; decide
      have factor_1_13 : (26 : ZMod 823727521) ^ 8379 = 626428524 := by
        calc
          (26 : ZMod 823727521) ^ 8379 = (26 : ZMod 823727521) ^ (4189 + 4189 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 4189 * (26 : ZMod 823727521) ^ 4189) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 626428524 := by rw [factor_1_12]; decide
      have factor_1_14 : (26 : ZMod 823727521) ^ 16758 = 286126446 := by
        calc
          (26 : ZMod 823727521) ^ 16758 = (26 : ZMod 823727521) ^ (8379 + 8379) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 8379 * (26 : ZMod 823727521) ^ 8379 := by rw [pow_add]
          _ = 286126446 := by rw [factor_1_13]; decide
      have factor_1_15 : (26 : ZMod 823727521) ^ 33517 = 246589059 := by
        calc
          (26 : ZMod 823727521) ^ 33517 = (26 : ZMod 823727521) ^ (16758 + 16758 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 16758 * (26 : ZMod 823727521) ^ 16758) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 246589059 := by rw [factor_1_14]; decide
      have factor_1_16 : (26 : ZMod 823727521) ^ 67035 = 580951546 := by
        calc
          (26 : ZMod 823727521) ^ 67035 = (26 : ZMod 823727521) ^ (33517 + 33517 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 33517 * (26 : ZMod 823727521) ^ 33517) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 580951546 := by rw [factor_1_15]; decide
      have factor_1_17 : (26 : ZMod 823727521) ^ 134070 = 374542667 := by
        calc
          (26 : ZMod 823727521) ^ 134070 = (26 : ZMod 823727521) ^ (67035 + 67035) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 67035 * (26 : ZMod 823727521) ^ 67035 := by rw [pow_add]
          _ = 374542667 := by rw [factor_1_16]; decide
      have factor_1_18 : (26 : ZMod 823727521) ^ 268140 = 708201895 := by
        calc
          (26 : ZMod 823727521) ^ 268140 = (26 : ZMod 823727521) ^ (134070 + 134070) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 134070 * (26 : ZMod 823727521) ^ 134070 := by rw [pow_add]
          _ = 708201895 := by rw [factor_1_17]; decide
      have factor_1_19 : (26 : ZMod 823727521) ^ 536280 = 228681390 := by
        calc
          (26 : ZMod 823727521) ^ 536280 = (26 : ZMod 823727521) ^ (268140 + 268140) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 268140 * (26 : ZMod 823727521) ^ 268140 := by rw [pow_add]
          _ = 228681390 := by rw [factor_1_18]; decide
      have factor_1_20 : (26 : ZMod 823727521) ^ 1072561 = 772542679 := by
        calc
          (26 : ZMod 823727521) ^ 1072561 = (26 : ZMod 823727521) ^ (536280 + 536280 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 536280 * (26 : ZMod 823727521) ^ 536280) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 772542679 := by rw [factor_1_19]; decide
      have factor_1_21 : (26 : ZMod 823727521) ^ 2145123 = 455458549 := by
        calc
          (26 : ZMod 823727521) ^ 2145123 = (26 : ZMod 823727521) ^ (1072561 + 1072561 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1072561 * (26 : ZMod 823727521) ^ 1072561) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 455458549 := by rw [factor_1_20]; decide
      have factor_1_22 : (26 : ZMod 823727521) ^ 4290247 = 166019633 := by
        calc
          (26 : ZMod 823727521) ^ 4290247 = (26 : ZMod 823727521) ^ (2145123 + 2145123 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 2145123 * (26 : ZMod 823727521) ^ 2145123) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 166019633 := by rw [factor_1_21]; decide
      have factor_1_23 : (26 : ZMod 823727521) ^ 8580495 = 183812072 := by
        calc
          (26 : ZMod 823727521) ^ 8580495 = (26 : ZMod 823727521) ^ (4290247 + 4290247 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 4290247 * (26 : ZMod 823727521) ^ 4290247) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 183812072 := by rw [factor_1_22]; decide
      have factor_1_24 : (26 : ZMod 823727521) ^ 17160990 = 779062529 := by
        calc
          (26 : ZMod 823727521) ^ 17160990 = (26 : ZMod 823727521) ^ (8580495 + 8580495) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 8580495 * (26 : ZMod 823727521) ^ 8580495 := by rw [pow_add]
          _ = 779062529 := by rw [factor_1_23]; decide
      have factor_1_25 : (26 : ZMod 823727521) ^ 34321980 = 539075794 := by
        calc
          (26 : ZMod 823727521) ^ 34321980 = (26 : ZMod 823727521) ^ (17160990 + 17160990) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 17160990 * (26 : ZMod 823727521) ^ 17160990 := by rw [pow_add]
          _ = 539075794 := by rw [factor_1_24]; decide
      have factor_1_26 : (26 : ZMod 823727521) ^ 68643960 = 631086023 := by
        calc
          (26 : ZMod 823727521) ^ 68643960 = (26 : ZMod 823727521) ^ (34321980 + 34321980) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 34321980 * (26 : ZMod 823727521) ^ 34321980 := by rw [pow_add]
          _ = 631086023 := by rw [factor_1_25]; decide
      have factor_1_27 : (26 : ZMod 823727521) ^ 137287920 = 669085073 := by
        calc
          (26 : ZMod 823727521) ^ 137287920 = (26 : ZMod 823727521) ^ (68643960 + 68643960) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 68643960 * (26 : ZMod 823727521) ^ 68643960 := by rw [pow_add]
          _ = 669085073 := by rw [factor_1_26]; decide
      have factor_1_28 : (26 : ZMod 823727521) ^ 274575840 = 669085072 := by
        calc
          (26 : ZMod 823727521) ^ 274575840 = (26 : ZMod 823727521) ^ (137287920 + 137287920) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 137287920 * (26 : ZMod 823727521) ^ 137287920 := by rw [pow_add]
          _ = 669085072 := by rw [factor_1_27]; decide
      change (26 : ZMod 823727521) ^ 274575840 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (26 : ZMod 823727521) ^ 1 = 26 := by norm_num
      have factor_2_1 : (26 : ZMod 823727521) ^ 2 = 676 := by
        calc
          (26 : ZMod 823727521) ^ 2 = (26 : ZMod 823727521) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1 * (26 : ZMod 823727521) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_2_0]; decide
      have factor_2_2 : (26 : ZMod 823727521) ^ 4 = 456976 := by
        calc
          (26 : ZMod 823727521) ^ 4 = (26 : ZMod 823727521) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2 * (26 : ZMod 823727521) ^ 2 := by rw [pow_add]
          _ = 456976 := by rw [factor_2_1]; decide
      have factor_2_3 : (26 : ZMod 823727521) ^ 9 = 315588065 := by
        calc
          (26 : ZMod 823727521) ^ 9 = (26 : ZMod 823727521) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 4 * (26 : ZMod 823727521) ^ 4) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 315588065 := by rw [factor_2_2]; decide
      have factor_2_4 : (26 : ZMod 823727521) ^ 19 = 277057634 := by
        calc
          (26 : ZMod 823727521) ^ 19 = (26 : ZMod 823727521) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 9 * (26 : ZMod 823727521) ^ 9) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 277057634 := by rw [factor_2_3]; decide
      have factor_2_5 : (26 : ZMod 823727521) ^ 39 = 744493406 := by
        calc
          (26 : ZMod 823727521) ^ 39 = (26 : ZMod 823727521) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 19 * (26 : ZMod 823727521) ^ 19) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 744493406 := by rw [factor_2_4]; decide
      have factor_2_6 : (26 : ZMod 823727521) ^ 78 = 736166599 := by
        calc
          (26 : ZMod 823727521) ^ 78 = (26 : ZMod 823727521) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 39 * (26 : ZMod 823727521) ^ 39 := by rw [pow_add]
          _ = 736166599 := by rw [factor_2_5]; decide
      have factor_2_7 : (26 : ZMod 823727521) ^ 157 = 62335018 := by
        calc
          (26 : ZMod 823727521) ^ 157 = (26 : ZMod 823727521) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 78 * (26 : ZMod 823727521) ^ 78) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 62335018 := by rw [factor_2_6]; decide
      have factor_2_8 : (26 : ZMod 823727521) ^ 314 = 779827485 := by
        calc
          (26 : ZMod 823727521) ^ 314 = (26 : ZMod 823727521) ^ (157 + 157) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 157 * (26 : ZMod 823727521) ^ 157 := by rw [pow_add]
          _ = 779827485 := by rw [factor_2_7]; decide
      have factor_2_9 : (26 : ZMod 823727521) ^ 628 = 483209192 := by
        calc
          (26 : ZMod 823727521) ^ 628 = (26 : ZMod 823727521) ^ (314 + 314) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 314 * (26 : ZMod 823727521) ^ 314 := by rw [pow_add]
          _ = 483209192 := by rw [factor_2_8]; decide
      have factor_2_10 : (26 : ZMod 823727521) ^ 1256 = 539986198 := by
        calc
          (26 : ZMod 823727521) ^ 1256 = (26 : ZMod 823727521) ^ (628 + 628) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 628 * (26 : ZMod 823727521) ^ 628 := by rw [pow_add]
          _ = 539986198 := by rw [factor_2_9]; decide
      have factor_2_11 : (26 : ZMod 823727521) ^ 2513 = 797372312 := by
        calc
          (26 : ZMod 823727521) ^ 2513 = (26 : ZMod 823727521) ^ (1256 + 1256 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1256 * (26 : ZMod 823727521) ^ 1256) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 797372312 := by rw [factor_2_10]; decide
      have factor_2_12 : (26 : ZMod 823727521) ^ 5027 = 642653640 := by
        calc
          (26 : ZMod 823727521) ^ 5027 = (26 : ZMod 823727521) ^ (2513 + 2513 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 2513 * (26 : ZMod 823727521) ^ 2513) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 642653640 := by rw [factor_2_11]; decide
      have factor_2_13 : (26 : ZMod 823727521) ^ 10055 = 518505826 := by
        calc
          (26 : ZMod 823727521) ^ 10055 = (26 : ZMod 823727521) ^ (5027 + 5027 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 5027 * (26 : ZMod 823727521) ^ 5027) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 518505826 := by rw [factor_2_12]; decide
      have factor_2_14 : (26 : ZMod 823727521) ^ 20110 = 326022151 := by
        calc
          (26 : ZMod 823727521) ^ 20110 = (26 : ZMod 823727521) ^ (10055 + 10055) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 10055 * (26 : ZMod 823727521) ^ 10055 := by rw [pow_add]
          _ = 326022151 := by rw [factor_2_13]; decide
      have factor_2_15 : (26 : ZMod 823727521) ^ 40221 = 147071566 := by
        calc
          (26 : ZMod 823727521) ^ 40221 = (26 : ZMod 823727521) ^ (20110 + 20110 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 20110 * (26 : ZMod 823727521) ^ 20110) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 147071566 := by rw [factor_2_14]; decide
      have factor_2_16 : (26 : ZMod 823727521) ^ 80442 = 368363858 := by
        calc
          (26 : ZMod 823727521) ^ 80442 = (26 : ZMod 823727521) ^ (40221 + 40221) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 40221 * (26 : ZMod 823727521) ^ 40221 := by rw [pow_add]
          _ = 368363858 := by rw [factor_2_15]; decide
      have factor_2_17 : (26 : ZMod 823727521) ^ 160884 = 809617098 := by
        calc
          (26 : ZMod 823727521) ^ 160884 = (26 : ZMod 823727521) ^ (80442 + 80442) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 80442 * (26 : ZMod 823727521) ^ 80442 := by rw [pow_add]
          _ = 809617098 := by rw [factor_2_16]; decide
      have factor_2_18 : (26 : ZMod 823727521) ^ 321768 = 34410498 := by
        calc
          (26 : ZMod 823727521) ^ 321768 = (26 : ZMod 823727521) ^ (160884 + 160884) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 160884 * (26 : ZMod 823727521) ^ 160884 := by rw [pow_add]
          _ = 34410498 := by rw [factor_2_17]; decide
      have factor_2_19 : (26 : ZMod 823727521) ^ 643537 = 223272803 := by
        calc
          (26 : ZMod 823727521) ^ 643537 = (26 : ZMod 823727521) ^ (321768 + 321768 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 321768 * (26 : ZMod 823727521) ^ 321768) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 223272803 := by rw [factor_2_18]; decide
      have factor_2_20 : (26 : ZMod 823727521) ^ 1287074 = 464568561 := by
        calc
          (26 : ZMod 823727521) ^ 1287074 = (26 : ZMod 823727521) ^ (643537 + 643537) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 643537 * (26 : ZMod 823727521) ^ 643537 := by rw [pow_add]
          _ = 464568561 := by rw [factor_2_19]; decide
      have factor_2_21 : (26 : ZMod 823727521) ^ 2574148 = 426581174 := by
        calc
          (26 : ZMod 823727521) ^ 2574148 = (26 : ZMod 823727521) ^ (1287074 + 1287074) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1287074 * (26 : ZMod 823727521) ^ 1287074 := by rw [pow_add]
          _ = 426581174 := by rw [factor_2_20]; decide
      have factor_2_22 : (26 : ZMod 823727521) ^ 5148297 = 507125541 := by
        calc
          (26 : ZMod 823727521) ^ 5148297 = (26 : ZMod 823727521) ^ (2574148 + 2574148 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 2574148 * (26 : ZMod 823727521) ^ 2574148) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 507125541 := by rw [factor_2_21]; decide
      have factor_2_23 : (26 : ZMod 823727521) ^ 10296594 = 685028903 := by
        calc
          (26 : ZMod 823727521) ^ 10296594 = (26 : ZMod 823727521) ^ (5148297 + 5148297) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 5148297 * (26 : ZMod 823727521) ^ 5148297 := by rw [pow_add]
          _ = 685028903 := by rw [factor_2_22]; decide
      have factor_2_24 : (26 : ZMod 823727521) ^ 20593188 = 468956596 := by
        calc
          (26 : ZMod 823727521) ^ 20593188 = (26 : ZMod 823727521) ^ (10296594 + 10296594) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 10296594 * (26 : ZMod 823727521) ^ 10296594 := by rw [pow_add]
          _ = 468956596 := by rw [factor_2_23]; decide
      have factor_2_25 : (26 : ZMod 823727521) ^ 41186376 = 540416097 := by
        calc
          (26 : ZMod 823727521) ^ 41186376 = (26 : ZMod 823727521) ^ (20593188 + 20593188) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 20593188 * (26 : ZMod 823727521) ^ 20593188 := by rw [pow_add]
          _ = 540416097 := by rw [factor_2_24]; decide
      have factor_2_26 : (26 : ZMod 823727521) ^ 82372752 = 762078294 := by
        calc
          (26 : ZMod 823727521) ^ 82372752 = (26 : ZMod 823727521) ^ (41186376 + 41186376) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 41186376 * (26 : ZMod 823727521) ^ 41186376 := by rw [pow_add]
          _ = 762078294 := by rw [factor_2_25]; decide
      have factor_2_27 : (26 : ZMod 823727521) ^ 164745504 = 302637352 := by
        calc
          (26 : ZMod 823727521) ^ 164745504 = (26 : ZMod 823727521) ^ (82372752 + 82372752) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 82372752 * (26 : ZMod 823727521) ^ 82372752 := by rw [pow_add]
          _ = 302637352 := by rw [factor_2_26]; decide
      change (26 : ZMod 823727521) ^ 164745504 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (26 : ZMod 823727521) ^ 1 = 26 := by norm_num
      have factor_3_1 : (26 : ZMod 823727521) ^ 3 = 17576 := by
        calc
          (26 : ZMod 823727521) ^ 3 = (26 : ZMod 823727521) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1 * (26 : ZMod 823727521) ^ 1) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 17576 := by rw [factor_3_0]; decide
      have factor_3_2 : (26 : ZMod 823727521) ^ 7 = 618262487 := by
        calc
          (26 : ZMod 823727521) ^ 7 = (26 : ZMod 823727521) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 3 * (26 : ZMod 823727521) ^ 3) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 618262487 := by rw [factor_3_1]; decide
      have factor_3_3 : (26 : ZMod 823727521) ^ 14 = 429872625 := by
        calc
          (26 : ZMod 823727521) ^ 14 = (26 : ZMod 823727521) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 7 * (26 : ZMod 823727521) ^ 7 := by rw [pow_add]
          _ = 429872625 := by rw [factor_3_2]; decide
      have factor_3_4 : (26 : ZMod 823727521) ^ 28 = 171351839 := by
        calc
          (26 : ZMod 823727521) ^ 28 = (26 : ZMod 823727521) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 14 * (26 : ZMod 823727521) ^ 14 := by rw [pow_add]
          _ = 171351839 := by rw [factor_3_3]; decide
      have factor_3_5 : (26 : ZMod 823727521) ^ 56 = 730277464 := by
        calc
          (26 : ZMod 823727521) ^ 56 = (26 : ZMod 823727521) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 28 * (26 : ZMod 823727521) ^ 28 := by rw [pow_add]
          _ = 730277464 := by rw [factor_3_4]; decide
      have factor_3_6 : (26 : ZMod 823727521) ^ 112 = 270190028 := by
        calc
          (26 : ZMod 823727521) ^ 112 = (26 : ZMod 823727521) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 56 * (26 : ZMod 823727521) ^ 56 := by rw [pow_add]
          _ = 270190028 := by rw [factor_3_5]; decide
      have factor_3_7 : (26 : ZMod 823727521) ^ 224 = 671530908 := by
        calc
          (26 : ZMod 823727521) ^ 224 = (26 : ZMod 823727521) ^ (112 + 112) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 112 * (26 : ZMod 823727521) ^ 112 := by rw [pow_add]
          _ = 671530908 := by rw [factor_3_6]; decide
      have factor_3_8 : (26 : ZMod 823727521) ^ 448 = 505519212 := by
        calc
          (26 : ZMod 823727521) ^ 448 = (26 : ZMod 823727521) ^ (224 + 224) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 224 * (26 : ZMod 823727521) ^ 224 := by rw [pow_add]
          _ = 505519212 := by rw [factor_3_7]; decide
      have factor_3_9 : (26 : ZMod 823727521) ^ 897 = 157059232 := by
        calc
          (26 : ZMod 823727521) ^ 897 = (26 : ZMod 823727521) ^ (448 + 448 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 448 * (26 : ZMod 823727521) ^ 448) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 157059232 := by rw [factor_3_8]; decide
      have factor_3_10 : (26 : ZMod 823727521) ^ 1795 = 713455921 := by
        calc
          (26 : ZMod 823727521) ^ 1795 = (26 : ZMod 823727521) ^ (897 + 897 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 897 * (26 : ZMod 823727521) ^ 897) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 713455921 := by rw [factor_3_9]; decide
      have factor_3_11 : (26 : ZMod 823727521) ^ 3591 = 537184460 := by
        calc
          (26 : ZMod 823727521) ^ 3591 = (26 : ZMod 823727521) ^ (1795 + 1795 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1795 * (26 : ZMod 823727521) ^ 1795) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 537184460 := by rw [factor_3_10]; decide
      have factor_3_12 : (26 : ZMod 823727521) ^ 7182 = 463006673 := by
        calc
          (26 : ZMod 823727521) ^ 7182 = (26 : ZMod 823727521) ^ (3591 + 3591) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 3591 * (26 : ZMod 823727521) ^ 3591 := by rw [pow_add]
          _ = 463006673 := by rw [factor_3_11]; decide
      have factor_3_13 : (26 : ZMod 823727521) ^ 14364 = 468524098 := by
        calc
          (26 : ZMod 823727521) ^ 14364 = (26 : ZMod 823727521) ^ (7182 + 7182) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 7182 * (26 : ZMod 823727521) ^ 7182 := by rw [pow_add]
          _ = 468524098 := by rw [factor_3_12]; decide
      have factor_3_14 : (26 : ZMod 823727521) ^ 28729 = 701313620 := by
        calc
          (26 : ZMod 823727521) ^ 28729 = (26 : ZMod 823727521) ^ (14364 + 14364 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 14364 * (26 : ZMod 823727521) ^ 14364) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 701313620 := by rw [factor_3_13]; decide
      have factor_3_15 : (26 : ZMod 823727521) ^ 57458 = 234850548 := by
        calc
          (26 : ZMod 823727521) ^ 57458 = (26 : ZMod 823727521) ^ (28729 + 28729) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 28729 * (26 : ZMod 823727521) ^ 28729 := by rw [pow_add]
          _ = 234850548 := by rw [factor_3_14]; decide
      have factor_3_16 : (26 : ZMod 823727521) ^ 114917 = 579855983 := by
        calc
          (26 : ZMod 823727521) ^ 114917 = (26 : ZMod 823727521) ^ (57458 + 57458 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 57458 * (26 : ZMod 823727521) ^ 57458) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 579855983 := by rw [factor_3_15]; decide
      have factor_3_17 : (26 : ZMod 823727521) ^ 229834 = 688225362 := by
        calc
          (26 : ZMod 823727521) ^ 229834 = (26 : ZMod 823727521) ^ (114917 + 114917) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 114917 * (26 : ZMod 823727521) ^ 114917 := by rw [pow_add]
          _ = 688225362 := by rw [factor_3_16]; decide
      have factor_3_18 : (26 : ZMod 823727521) ^ 459669 = 177164847 := by
        calc
          (26 : ZMod 823727521) ^ 459669 = (26 : ZMod 823727521) ^ (229834 + 229834 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 229834 * (26 : ZMod 823727521) ^ 229834) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 177164847 := by rw [factor_3_17]; decide
      have factor_3_19 : (26 : ZMod 823727521) ^ 919338 = 359237645 := by
        calc
          (26 : ZMod 823727521) ^ 919338 = (26 : ZMod 823727521) ^ (459669 + 459669) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 459669 * (26 : ZMod 823727521) ^ 459669 := by rw [pow_add]
          _ = 359237645 := by rw [factor_3_18]; decide
      have factor_3_20 : (26 : ZMod 823727521) ^ 1838677 = 460884391 := by
        calc
          (26 : ZMod 823727521) ^ 1838677 = (26 : ZMod 823727521) ^ (919338 + 919338 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 919338 * (26 : ZMod 823727521) ^ 919338) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 460884391 := by rw [factor_3_19]; decide
      have factor_3_21 : (26 : ZMod 823727521) ^ 3677355 = 390053989 := by
        calc
          (26 : ZMod 823727521) ^ 3677355 = (26 : ZMod 823727521) ^ (1838677 + 1838677 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1838677 * (26 : ZMod 823727521) ^ 1838677) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 390053989 := by rw [factor_3_20]; decide
      have factor_3_22 : (26 : ZMod 823727521) ^ 7354710 = 351311277 := by
        calc
          (26 : ZMod 823727521) ^ 7354710 = (26 : ZMod 823727521) ^ (3677355 + 3677355) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 3677355 * (26 : ZMod 823727521) ^ 3677355 := by rw [pow_add]
          _ = 351311277 := by rw [factor_3_21]; decide
      have factor_3_23 : (26 : ZMod 823727521) ^ 14709420 = 751330020 := by
        calc
          (26 : ZMod 823727521) ^ 14709420 = (26 : ZMod 823727521) ^ (7354710 + 7354710) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 7354710 * (26 : ZMod 823727521) ^ 7354710 := by rw [pow_add]
          _ = 751330020 := by rw [factor_3_22]; decide
      have factor_3_24 : (26 : ZMod 823727521) ^ 29418840 = 165461497 := by
        calc
          (26 : ZMod 823727521) ^ 29418840 = (26 : ZMod 823727521) ^ (14709420 + 14709420) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 14709420 * (26 : ZMod 823727521) ^ 14709420 := by rw [pow_add]
          _ = 165461497 := by rw [factor_3_23]; decide
      have factor_3_25 : (26 : ZMod 823727521) ^ 58837680 = 254222489 := by
        calc
          (26 : ZMod 823727521) ^ 58837680 = (26 : ZMod 823727521) ^ (29418840 + 29418840) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 29418840 * (26 : ZMod 823727521) ^ 29418840 := by rw [pow_add]
          _ = 254222489 := by rw [factor_3_24]; decide
      have factor_3_26 : (26 : ZMod 823727521) ^ 117675360 = 757145115 := by
        calc
          (26 : ZMod 823727521) ^ 117675360 = (26 : ZMod 823727521) ^ (58837680 + 58837680) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 58837680 * (26 : ZMod 823727521) ^ 58837680 := by rw [pow_add]
          _ = 757145115 := by rw [factor_3_25]; decide
      change (26 : ZMod 823727521) ^ 117675360 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (26 : ZMod 823727521) ^ 1 = 26 := by norm_num
      have factor_4_1 : (26 : ZMod 823727521) ^ 2 = 676 := by
        calc
          (26 : ZMod 823727521) ^ 2 = (26 : ZMod 823727521) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1 * (26 : ZMod 823727521) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_4_0]; decide
      have factor_4_2 : (26 : ZMod 823727521) ^ 4 = 456976 := by
        calc
          (26 : ZMod 823727521) ^ 4 = (26 : ZMod 823727521) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2 * (26 : ZMod 823727521) ^ 2 := by rw [pow_add]
          _ = 456976 := by rw [factor_4_1]; decide
      have factor_4_3 : (26 : ZMod 823727521) ^ 8 = 424001763 := by
        calc
          (26 : ZMod 823727521) ^ 8 = (26 : ZMod 823727521) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 4 * (26 : ZMod 823727521) ^ 4 := by rw [pow_add]
          _ = 424001763 := by rw [factor_4_2]; decide
      have factor_4_4 : (26 : ZMod 823727521) ^ 17 = 212434388 := by
        calc
          (26 : ZMod 823727521) ^ 17 = (26 : ZMod 823727521) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 8 * (26 : ZMod 823727521) ^ 8) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 212434388 := by rw [factor_4_3]; decide
      have factor_4_5 : (26 : ZMod 823727521) ^ 35 = 518652761 := by
        calc
          (26 : ZMod 823727521) ^ 35 = (26 : ZMod 823727521) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 17 * (26 : ZMod 823727521) ^ 17) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 518652761 := by rw [factor_4_4]; decide
      have factor_4_6 : (26 : ZMod 823727521) ^ 71 = 622296679 := by
        calc
          (26 : ZMod 823727521) ^ 71 = (26 : ZMod 823727521) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 35 * (26 : ZMod 823727521) ^ 35) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 622296679 := by rw [factor_4_5]; decide
      have factor_4_7 : (26 : ZMod 823727521) ^ 142 = 539193519 := by
        calc
          (26 : ZMod 823727521) ^ 142 = (26 : ZMod 823727521) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 71 * (26 : ZMod 823727521) ^ 71 := by rw [pow_add]
          _ = 539193519 := by rw [factor_4_6]; decide
      have factor_4_8 : (26 : ZMod 823727521) ^ 285 = 562994259 := by
        calc
          (26 : ZMod 823727521) ^ 285 = (26 : ZMod 823727521) ^ (142 + 142 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 142 * (26 : ZMod 823727521) ^ 142) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 562994259 := by rw [factor_4_7]; decide
      have factor_4_9 : (26 : ZMod 823727521) ^ 571 = 104373319 := by
        calc
          (26 : ZMod 823727521) ^ 571 = (26 : ZMod 823727521) ^ (285 + 285 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 285 * (26 : ZMod 823727521) ^ 285) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 104373319 := by rw [factor_4_8]; decide
      have factor_4_10 : (26 : ZMod 823727521) ^ 1142 = 667398450 := by
        calc
          (26 : ZMod 823727521) ^ 1142 = (26 : ZMod 823727521) ^ (571 + 571) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 571 * (26 : ZMod 823727521) ^ 571 := by rw [pow_add]
          _ = 667398450 := by rw [factor_4_9]; decide
      have factor_4_11 : (26 : ZMod 823727521) ^ 2285 = 323153323 := by
        calc
          (26 : ZMod 823727521) ^ 2285 = (26 : ZMod 823727521) ^ (1142 + 1142 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1142 * (26 : ZMod 823727521) ^ 1142) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 323153323 := by rw [factor_4_10]; decide
      have factor_4_12 : (26 : ZMod 823727521) ^ 4570 = 511526993 := by
        calc
          (26 : ZMod 823727521) ^ 4570 = (26 : ZMod 823727521) ^ (2285 + 2285) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2285 * (26 : ZMod 823727521) ^ 2285 := by rw [pow_add]
          _ = 511526993 := by rw [factor_4_11]; decide
      have factor_4_13 : (26 : ZMod 823727521) ^ 9141 = 659103223 := by
        calc
          (26 : ZMod 823727521) ^ 9141 = (26 : ZMod 823727521) ^ (4570 + 4570 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 4570 * (26 : ZMod 823727521) ^ 4570) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 659103223 := by rw [factor_4_12]; decide
      have factor_4_14 : (26 : ZMod 823727521) ^ 18282 = 160389448 := by
        calc
          (26 : ZMod 823727521) ^ 18282 = (26 : ZMod 823727521) ^ (9141 + 9141) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 9141 * (26 : ZMod 823727521) ^ 9141 := by rw [pow_add]
          _ = 160389448 := by rw [factor_4_13]; decide
      have factor_4_15 : (26 : ZMod 823727521) ^ 36564 = 134985710 := by
        calc
          (26 : ZMod 823727521) ^ 36564 = (26 : ZMod 823727521) ^ (18282 + 18282) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 18282 * (26 : ZMod 823727521) ^ 18282 := by rw [pow_add]
          _ = 134985710 := by rw [factor_4_14]; decide
      have factor_4_16 : (26 : ZMod 823727521) ^ 73129 = 294429954 := by
        calc
          (26 : ZMod 823727521) ^ 73129 = (26 : ZMod 823727521) ^ (36564 + 36564 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 36564 * (26 : ZMod 823727521) ^ 36564) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 294429954 := by rw [factor_4_15]; decide
      have factor_4_17 : (26 : ZMod 823727521) ^ 146258 = 817519342 := by
        calc
          (26 : ZMod 823727521) ^ 146258 = (26 : ZMod 823727521) ^ (73129 + 73129) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 73129 * (26 : ZMod 823727521) ^ 73129 := by rw [pow_add]
          _ = 817519342 := by rw [factor_4_16]; decide
      have factor_4_18 : (26 : ZMod 823727521) ^ 292516 = 99515972 := by
        calc
          (26 : ZMod 823727521) ^ 292516 = (26 : ZMod 823727521) ^ (146258 + 146258) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 146258 * (26 : ZMod 823727521) ^ 146258 := by rw [pow_add]
          _ = 99515972 := by rw [factor_4_17]; decide
      have factor_4_19 : (26 : ZMod 823727521) ^ 585033 = 168195310 := by
        calc
          (26 : ZMod 823727521) ^ 585033 = (26 : ZMod 823727521) ^ (292516 + 292516 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 292516 * (26 : ZMod 823727521) ^ 292516) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 168195310 := by rw [factor_4_18]; decide
      have factor_4_20 : (26 : ZMod 823727521) ^ 1170067 = 344943392 := by
        calc
          (26 : ZMod 823727521) ^ 1170067 = (26 : ZMod 823727521) ^ (585033 + 585033 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 585033 * (26 : ZMod 823727521) ^ 585033) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 344943392 := by rw [factor_4_19]; decide
      have factor_4_21 : (26 : ZMod 823727521) ^ 2340135 = 535681867 := by
        calc
          (26 : ZMod 823727521) ^ 2340135 = (26 : ZMod 823727521) ^ (1170067 + 1170067 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1170067 * (26 : ZMod 823727521) ^ 1170067) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 535681867 := by rw [factor_4_20]; decide
      have factor_4_22 : (26 : ZMod 823727521) ^ 4680270 = 741186459 := by
        calc
          (26 : ZMod 823727521) ^ 4680270 = (26 : ZMod 823727521) ^ (2340135 + 2340135) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2340135 * (26 : ZMod 823727521) ^ 2340135 := by rw [pow_add]
          _ = 741186459 := by rw [factor_4_21]; decide
      have factor_4_23 : (26 : ZMod 823727521) ^ 9360540 = 477994953 := by
        calc
          (26 : ZMod 823727521) ^ 9360540 = (26 : ZMod 823727521) ^ (4680270 + 4680270) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 4680270 * (26 : ZMod 823727521) ^ 4680270 := by rw [pow_add]
          _ = 477994953 := by rw [factor_4_22]; decide
      have factor_4_24 : (26 : ZMod 823727521) ^ 18721080 = 261046976 := by
        calc
          (26 : ZMod 823727521) ^ 18721080 = (26 : ZMod 823727521) ^ (9360540 + 9360540) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 9360540 * (26 : ZMod 823727521) ^ 9360540 := by rw [pow_add]
          _ = 261046976 := by rw [factor_4_23]; decide
      have factor_4_25 : (26 : ZMod 823727521) ^ 37442160 = 569216662 := by
        calc
          (26 : ZMod 823727521) ^ 37442160 = (26 : ZMod 823727521) ^ (18721080 + 18721080) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 18721080 * (26 : ZMod 823727521) ^ 18721080 := by rw [pow_add]
          _ = 569216662 := by rw [factor_4_24]; decide
      have factor_4_26 : (26 : ZMod 823727521) ^ 74884320 = 792400338 := by
        calc
          (26 : ZMod 823727521) ^ 74884320 = (26 : ZMod 823727521) ^ (37442160 + 37442160) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 37442160 * (26 : ZMod 823727521) ^ 37442160 := by rw [pow_add]
          _ = 792400338 := by rw [factor_4_25]; decide
      change (26 : ZMod 823727521) ^ 74884320 ≠ 1
      rw [factor_4_26]
      decide
    ·
      have factor_5_0 : (26 : ZMod 823727521) ^ 1 = 26 := by norm_num
      have factor_5_1 : (26 : ZMod 823727521) ^ 2 = 676 := by
        calc
          (26 : ZMod 823727521) ^ 2 = (26 : ZMod 823727521) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1 * (26 : ZMod 823727521) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_5_0]; decide
      have factor_5_2 : (26 : ZMod 823727521) ^ 5 = 11881376 := by
        calc
          (26 : ZMod 823727521) ^ 5 = (26 : ZMod 823727521) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 2 * (26 : ZMod 823727521) ^ 2) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 11881376 := by rw [factor_5_1]; decide
      have factor_5_3 : (26 : ZMod 823727521) ^ 11 = 815831522 := by
        calc
          (26 : ZMod 823727521) ^ 11 = (26 : ZMod 823727521) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 5 * (26 : ZMod 823727521) ^ 5) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 815831522 := by rw [factor_5_2]; decide
      have factor_5_4 : (26 : ZMod 823727521) ^ 23 = 121922042 := by
        calc
          (26 : ZMod 823727521) ^ 23 = (26 : ZMod 823727521) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 11 * (26 : ZMod 823727521) ^ 11) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 121922042 := by rw [factor_5_3]; decide
      have factor_5_5 : (26 : ZMod 823727521) ^ 46 = 776393848 := by
        calc
          (26 : ZMod 823727521) ^ 46 = (26 : ZMod 823727521) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 23 * (26 : ZMod 823727521) ^ 23 := by rw [pow_add]
          _ = 776393848 := by rw [factor_5_4]; decide
      have factor_5_6 : (26 : ZMod 823727521) ^ 92 = 345842525 := by
        calc
          (26 : ZMod 823727521) ^ 92 = (26 : ZMod 823727521) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 46 * (26 : ZMod 823727521) ^ 46 := by rw [pow_add]
          _ = 345842525 := by rw [factor_5_5]; decide
      have factor_5_7 : (26 : ZMod 823727521) ^ 184 = 553719341 := by
        calc
          (26 : ZMod 823727521) ^ 184 = (26 : ZMod 823727521) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 92 * (26 : ZMod 823727521) ^ 92 := by rw [pow_add]
          _ = 553719341 := by rw [factor_5_6]; decide
      have factor_5_8 : (26 : ZMod 823727521) ^ 369 = 429028644 := by
        calc
          (26 : ZMod 823727521) ^ 369 = (26 : ZMod 823727521) ^ (184 + 184 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 184 * (26 : ZMod 823727521) ^ 184) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 429028644 := by rw [factor_5_7]; decide
      have factor_5_9 : (26 : ZMod 823727521) ^ 739 = 144589284 := by
        calc
          (26 : ZMod 823727521) ^ 739 = (26 : ZMod 823727521) ^ (369 + 369 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 369 * (26 : ZMod 823727521) ^ 369) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 144589284 := by rw [factor_5_8]; decide
      have factor_5_10 : (26 : ZMod 823727521) ^ 1478 = 716968831 := by
        calc
          (26 : ZMod 823727521) ^ 1478 = (26 : ZMod 823727521) ^ (739 + 739) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 739 * (26 : ZMod 823727521) ^ 739 := by rw [pow_add]
          _ = 716968831 := by rw [factor_5_9]; decide
      have factor_5_11 : (26 : ZMod 823727521) ^ 2957 = 692515417 := by
        calc
          (26 : ZMod 823727521) ^ 2957 = (26 : ZMod 823727521) ^ (1478 + 1478 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1478 * (26 : ZMod 823727521) ^ 1478) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 692515417 := by rw [factor_5_10]; decide
      have factor_5_12 : (26 : ZMod 823727521) ^ 5914 = 170356193 := by
        calc
          (26 : ZMod 823727521) ^ 5914 = (26 : ZMod 823727521) ^ (2957 + 2957) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2957 * (26 : ZMod 823727521) ^ 2957 := by rw [pow_add]
          _ = 170356193 := by rw [factor_5_11]; decide
      have factor_5_13 : (26 : ZMod 823727521) ^ 11829 = 411287385 := by
        calc
          (26 : ZMod 823727521) ^ 11829 = (26 : ZMod 823727521) ^ (5914 + 5914 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 5914 * (26 : ZMod 823727521) ^ 5914) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 411287385 := by rw [factor_5_12]; decide
      have factor_5_14 : (26 : ZMod 823727521) ^ 23659 = 231720561 := by
        calc
          (26 : ZMod 823727521) ^ 23659 = (26 : ZMod 823727521) ^ (11829 + 11829 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 11829 * (26 : ZMod 823727521) ^ 11829) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 231720561 := by rw [factor_5_13]; decide
      have factor_5_15 : (26 : ZMod 823727521) ^ 47318 = 231666357 := by
        calc
          (26 : ZMod 823727521) ^ 47318 = (26 : ZMod 823727521) ^ (23659 + 23659) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 23659 * (26 : ZMod 823727521) ^ 23659 := by rw [pow_add]
          _ = 231666357 := by rw [factor_5_14]; decide
      have factor_5_16 : (26 : ZMod 823727521) ^ 94637 = 46251405 := by
        calc
          (26 : ZMod 823727521) ^ 94637 = (26 : ZMod 823727521) ^ (47318 + 47318 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 47318 * (26 : ZMod 823727521) ^ 47318) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 46251405 := by rw [factor_5_15]; decide
      have factor_5_17 : (26 : ZMod 823727521) ^ 189275 = 107308651 := by
        calc
          (26 : ZMod 823727521) ^ 189275 = (26 : ZMod 823727521) ^ (94637 + 94637 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 94637 * (26 : ZMod 823727521) ^ 94637) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 107308651 := by rw [factor_5_16]; decide
      have factor_5_18 : (26 : ZMod 823727521) ^ 378551 = 672048794 := by
        calc
          (26 : ZMod 823727521) ^ 378551 = (26 : ZMod 823727521) ^ (189275 + 189275 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 189275 * (26 : ZMod 823727521) ^ 189275) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 672048794 := by rw [factor_5_17]; decide
      have factor_5_19 : (26 : ZMod 823727521) ^ 757102 = 40347501 := by
        calc
          (26 : ZMod 823727521) ^ 757102 = (26 : ZMod 823727521) ^ (378551 + 378551) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 378551 * (26 : ZMod 823727521) ^ 378551 := by rw [pow_add]
          _ = 40347501 := by rw [factor_5_18]; decide
      have factor_5_20 : (26 : ZMod 823727521) ^ 1514205 = 464830601 := by
        calc
          (26 : ZMod 823727521) ^ 1514205 = (26 : ZMod 823727521) ^ (757102 + 757102 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 757102 * (26 : ZMod 823727521) ^ 757102) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 464830601 := by rw [factor_5_19]; decide
      have factor_5_21 : (26 : ZMod 823727521) ^ 3028410 = 199042878 := by
        calc
          (26 : ZMod 823727521) ^ 3028410 = (26 : ZMod 823727521) ^ (1514205 + 1514205) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1514205 * (26 : ZMod 823727521) ^ 1514205 := by rw [pow_add]
          _ = 199042878 := by rw [factor_5_20]; decide
      have factor_5_22 : (26 : ZMod 823727521) ^ 6056820 = 63122641 := by
        calc
          (26 : ZMod 823727521) ^ 6056820 = (26 : ZMod 823727521) ^ (3028410 + 3028410) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 3028410 * (26 : ZMod 823727521) ^ 3028410 := by rw [pow_add]
          _ = 63122641 := by rw [factor_5_21]; decide
      have factor_5_23 : (26 : ZMod 823727521) ^ 12113640 = 587890403 := by
        calc
          (26 : ZMod 823727521) ^ 12113640 = (26 : ZMod 823727521) ^ (6056820 + 6056820) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 6056820 * (26 : ZMod 823727521) ^ 6056820 := by rw [pow_add]
          _ = 587890403 := by rw [factor_5_22]; decide
      have factor_5_24 : (26 : ZMod 823727521) ^ 24227280 = 576396313 := by
        calc
          (26 : ZMod 823727521) ^ 24227280 = (26 : ZMod 823727521) ^ (12113640 + 12113640) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 12113640 * (26 : ZMod 823727521) ^ 12113640 := by rw [pow_add]
          _ = 576396313 := by rw [factor_5_23]; decide
      have factor_5_25 : (26 : ZMod 823727521) ^ 48454560 = 793004922 := by
        calc
          (26 : ZMod 823727521) ^ 48454560 = (26 : ZMod 823727521) ^ (24227280 + 24227280) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 24227280 * (26 : ZMod 823727521) ^ 24227280 := by rw [pow_add]
          _ = 793004922 := by rw [factor_5_24]; decide
      change (26 : ZMod 823727521) ^ 48454560 ≠ 1
      rw [factor_5_25]
      decide
    ·
      have factor_6_0 : (26 : ZMod 823727521) ^ 1 = 26 := by norm_num
      have factor_6_1 : (26 : ZMod 823727521) ^ 2 = 676 := by
        calc
          (26 : ZMod 823727521) ^ 2 = (26 : ZMod 823727521) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1 * (26 : ZMod 823727521) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_6_0]; decide
      have factor_6_2 : (26 : ZMod 823727521) ^ 5 = 11881376 := by
        calc
          (26 : ZMod 823727521) ^ 5 = (26 : ZMod 823727521) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 2 * (26 : ZMod 823727521) ^ 2) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 11881376 := by rw [factor_6_1]; decide
      have factor_6_3 : (26 : ZMod 823727521) ^ 10 = 791742001 := by
        calc
          (26 : ZMod 823727521) ^ 10 = (26 : ZMod 823727521) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 5 * (26 : ZMod 823727521) ^ 5 := by rw [pow_add]
          _ = 791742001 := by rw [factor_6_2]; decide
      have factor_6_4 : (26 : ZMod 823727521) ^ 20 = 613678316 := by
        calc
          (26 : ZMod 823727521) ^ 20 = (26 : ZMod 823727521) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 10 * (26 : ZMod 823727521) ^ 10 := by rw [pow_add]
          _ = 613678316 := by rw [factor_6_3]; decide
      have factor_6_5 : (26 : ZMod 823727521) ^ 41 = 803754646 := by
        calc
          (26 : ZMod 823727521) ^ 41 = (26 : ZMod 823727521) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 20 * (26 : ZMod 823727521) ^ 20) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 803754646 := by rw [factor_6_4]; decide
      have factor_6_6 : (26 : ZMod 823727521) ^ 82 = 148168224 := by
        calc
          (26 : ZMod 823727521) ^ 82 = (26 : ZMod 823727521) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 41 * (26 : ZMod 823727521) ^ 41 := by rw [pow_add]
          _ = 148168224 := by rw [factor_6_5]; decide
      have factor_6_7 : (26 : ZMod 823727521) ^ 165 = 45819810 := by
        calc
          (26 : ZMod 823727521) ^ 165 = (26 : ZMod 823727521) ^ (82 + 82 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 82 * (26 : ZMod 823727521) ^ 82) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 45819810 := by rw [factor_6_6]; decide
      have factor_6_8 : (26 : ZMod 823727521) ^ 330 = 62475375 := by
        calc
          (26 : ZMod 823727521) ^ 330 = (26 : ZMod 823727521) ^ (165 + 165) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 165 * (26 : ZMod 823727521) ^ 165 := by rw [pow_add]
          _ = 62475375 := by rw [factor_6_7]; decide
      have factor_6_9 : (26 : ZMod 823727521) ^ 661 = 226090276 := by
        calc
          (26 : ZMod 823727521) ^ 661 = (26 : ZMod 823727521) ^ (330 + 330 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 330 * (26 : ZMod 823727521) ^ 330) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 226090276 := by rw [factor_6_8]; decide
      have factor_6_10 : (26 : ZMod 823727521) ^ 1323 = 492301901 := by
        calc
          (26 : ZMod 823727521) ^ 1323 = (26 : ZMod 823727521) ^ (661 + 661 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 661 * (26 : ZMod 823727521) ^ 661) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 492301901 := by rw [factor_6_9]; decide
      have factor_6_11 : (26 : ZMod 823727521) ^ 2646 = 231373044 := by
        calc
          (26 : ZMod 823727521) ^ 2646 = (26 : ZMod 823727521) ^ (1323 + 1323) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1323 * (26 : ZMod 823727521) ^ 1323 := by rw [pow_add]
          _ = 231373044 := by rw [factor_6_10]; decide
      have factor_6_12 : (26 : ZMod 823727521) ^ 5292 = 624570384 := by
        calc
          (26 : ZMod 823727521) ^ 5292 = (26 : ZMod 823727521) ^ (2646 + 2646) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2646 * (26 : ZMod 823727521) ^ 2646 := by rw [pow_add]
          _ = 624570384 := by rw [factor_6_11]; decide
      have factor_6_13 : (26 : ZMod 823727521) ^ 10584 = 232741612 := by
        calc
          (26 : ZMod 823727521) ^ 10584 = (26 : ZMod 823727521) ^ (5292 + 5292) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 5292 * (26 : ZMod 823727521) ^ 5292 := by rw [pow_add]
          _ = 232741612 := by rw [factor_6_12]; decide
      have factor_6_14 : (26 : ZMod 823727521) ^ 21168 = 94569976 := by
        calc
          (26 : ZMod 823727521) ^ 21168 = (26 : ZMod 823727521) ^ (10584 + 10584) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 10584 * (26 : ZMod 823727521) ^ 10584 := by rw [pow_add]
          _ = 94569976 := by rw [factor_6_13]; decide
      have factor_6_15 : (26 : ZMod 823727521) ^ 42337 = 189521073 := by
        calc
          (26 : ZMod 823727521) ^ 42337 = (26 : ZMod 823727521) ^ (21168 + 21168 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 21168 * (26 : ZMod 823727521) ^ 21168) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 189521073 := by rw [factor_6_14]; decide
      have factor_6_16 : (26 : ZMod 823727521) ^ 84675 = 779670666 := by
        calc
          (26 : ZMod 823727521) ^ 84675 = (26 : ZMod 823727521) ^ (42337 + 42337 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 42337 * (26 : ZMod 823727521) ^ 42337) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 779670666 := by rw [factor_6_15]; decide
      have factor_6_17 : (26 : ZMod 823727521) ^ 169351 = 60641361 := by
        calc
          (26 : ZMod 823727521) ^ 169351 = (26 : ZMod 823727521) ^ (84675 + 84675 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 84675 * (26 : ZMod 823727521) ^ 84675) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 60641361 := by rw [factor_6_16]; decide
      have factor_6_18 : (26 : ZMod 823727521) ^ 338703 = 82079817 := by
        calc
          (26 : ZMod 823727521) ^ 338703 = (26 : ZMod 823727521) ^ (169351 + 169351 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 169351 * (26 : ZMod 823727521) ^ 169351) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 82079817 := by rw [factor_6_17]; decide
      have factor_6_19 : (26 : ZMod 823727521) ^ 677407 = 381742593 := by
        calc
          (26 : ZMod 823727521) ^ 677407 = (26 : ZMod 823727521) ^ (338703 + 338703 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 338703 * (26 : ZMod 823727521) ^ 338703) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 381742593 := by rw [factor_6_18]; decide
      have factor_6_20 : (26 : ZMod 823727521) ^ 1354815 = 454803117 := by
        calc
          (26 : ZMod 823727521) ^ 1354815 = (26 : ZMod 823727521) ^ (677407 + 677407 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 677407 * (26 : ZMod 823727521) ^ 677407) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 454803117 := by rw [factor_6_19]; decide
      have factor_6_21 : (26 : ZMod 823727521) ^ 2709630 = 105254425 := by
        calc
          (26 : ZMod 823727521) ^ 2709630 = (26 : ZMod 823727521) ^ (1354815 + 1354815) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1354815 * (26 : ZMod 823727521) ^ 1354815 := by rw [pow_add]
          _ = 105254425 := by rw [factor_6_20]; decide
      have factor_6_22 : (26 : ZMod 823727521) ^ 5419260 = 508369484 := by
        calc
          (26 : ZMod 823727521) ^ 5419260 = (26 : ZMod 823727521) ^ (2709630 + 2709630) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2709630 * (26 : ZMod 823727521) ^ 2709630 := by rw [pow_add]
          _ = 508369484 := by rw [factor_6_21]; decide
      have factor_6_23 : (26 : ZMod 823727521) ^ 10838520 = 334085659 := by
        calc
          (26 : ZMod 823727521) ^ 10838520 = (26 : ZMod 823727521) ^ (5419260 + 5419260) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 5419260 * (26 : ZMod 823727521) ^ 5419260 := by rw [pow_add]
          _ = 334085659 := by rw [factor_6_22]; decide
      have factor_6_24 : (26 : ZMod 823727521) ^ 21677040 = 193431489 := by
        calc
          (26 : ZMod 823727521) ^ 21677040 = (26 : ZMod 823727521) ^ (10838520 + 10838520) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 10838520 * (26 : ZMod 823727521) ^ 10838520 := by rw [pow_add]
          _ = 193431489 := by rw [factor_6_23]; decide
      have factor_6_25 : (26 : ZMod 823727521) ^ 43354080 = 678505209 := by
        calc
          (26 : ZMod 823727521) ^ 43354080 = (26 : ZMod 823727521) ^ (21677040 + 21677040) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 21677040 * (26 : ZMod 823727521) ^ 21677040 := by rw [pow_add]
          _ = 678505209 := by rw [factor_6_24]; decide
      change (26 : ZMod 823727521) ^ 43354080 ≠ 1
      rw [factor_6_25]
      decide
    ·
      have factor_7_0 : (26 : ZMod 823727521) ^ 1 = 26 := by norm_num
      have factor_7_1 : (26 : ZMod 823727521) ^ 2 = 676 := by
        calc
          (26 : ZMod 823727521) ^ 2 = (26 : ZMod 823727521) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1 * (26 : ZMod 823727521) ^ 1 := by rw [pow_add]
          _ = 676 := by rw [factor_7_0]; decide
      have factor_7_2 : (26 : ZMod 823727521) ^ 4 = 456976 := by
        calc
          (26 : ZMod 823727521) ^ 4 = (26 : ZMod 823727521) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2 * (26 : ZMod 823727521) ^ 2 := by rw [pow_add]
          _ = 456976 := by rw [factor_7_1]; decide
      have factor_7_3 : (26 : ZMod 823727521) ^ 8 = 424001763 := by
        calc
          (26 : ZMod 823727521) ^ 8 = (26 : ZMod 823727521) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 4 * (26 : ZMod 823727521) ^ 4 := by rw [pow_add]
          _ = 424001763 := by rw [factor_7_2]; decide
      have factor_7_4 : (26 : ZMod 823727521) ^ 17 = 212434388 := by
        calc
          (26 : ZMod 823727521) ^ 17 = (26 : ZMod 823727521) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 8 * (26 : ZMod 823727521) ^ 8) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 212434388 := by rw [factor_7_3]; decide
      have factor_7_5 : (26 : ZMod 823727521) ^ 34 = 621902910 := by
        calc
          (26 : ZMod 823727521) ^ 34 = (26 : ZMod 823727521) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 17 * (26 : ZMod 823727521) ^ 17 := by rw [pow_add]
          _ = 621902910 := by rw [factor_7_4]; decide
      have factor_7_6 : (26 : ZMod 823727521) ^ 68 = 81442706 := by
        calc
          (26 : ZMod 823727521) ^ 68 = (26 : ZMod 823727521) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 34 * (26 : ZMod 823727521) ^ 34 := by rw [pow_add]
          _ = 81442706 := by rw [factor_7_5]; decide
      have factor_7_7 : (26 : ZMod 823727521) ^ 136 = 63613800 := by
        calc
          (26 : ZMod 823727521) ^ 136 = (26 : ZMod 823727521) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 68 * (26 : ZMod 823727521) ^ 68 := by rw [pow_add]
          _ = 63613800 := by rw [factor_7_6]; decide
      have factor_7_8 : (26 : ZMod 823727521) ^ 273 = 81052856 := by
        calc
          (26 : ZMod 823727521) ^ 273 = (26 : ZMod 823727521) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 136 * (26 : ZMod 823727521) ^ 136) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 81052856 := by rw [factor_7_7]; decide
      have factor_7_9 : (26 : ZMod 823727521) ^ 546 = 757498126 := by
        calc
          (26 : ZMod 823727521) ^ 546 = (26 : ZMod 823727521) ^ (273 + 273) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 273 * (26 : ZMod 823727521) ^ 273 := by rw [pow_add]
          _ = 757498126 := by rw [factor_7_8]; decide
      have factor_7_10 : (26 : ZMod 823727521) ^ 1092 = 187291445 := by
        calc
          (26 : ZMod 823727521) ^ 1092 = (26 : ZMod 823727521) ^ (546 + 546) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 546 * (26 : ZMod 823727521) ^ 546 := by rw [pow_add]
          _ = 187291445 := by rw [factor_7_9]; decide
      have factor_7_11 : (26 : ZMod 823727521) ^ 2185 = 470593893 := by
        calc
          (26 : ZMod 823727521) ^ 2185 = (26 : ZMod 823727521) ^ (1092 + 1092 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 1092 * (26 : ZMod 823727521) ^ 1092) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 470593893 := by rw [factor_7_10]; decide
      have factor_7_12 : (26 : ZMod 823727521) ^ 4371 = 370531743 := by
        calc
          (26 : ZMod 823727521) ^ 4371 = (26 : ZMod 823727521) ^ (2185 + 2185 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 2185 * (26 : ZMod 823727521) ^ 2185) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 370531743 := by rw [factor_7_11]; decide
      have factor_7_13 : (26 : ZMod 823727521) ^ 8743 = 534722577 := by
        calc
          (26 : ZMod 823727521) ^ 8743 = (26 : ZMod 823727521) ^ (4371 + 4371 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 4371 * (26 : ZMod 823727521) ^ 4371) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 534722577 := by rw [factor_7_12]; decide
      have factor_7_14 : (26 : ZMod 823727521) ^ 17487 = 386407110 := by
        calc
          (26 : ZMod 823727521) ^ 17487 = (26 : ZMod 823727521) ^ (8743 + 8743 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 8743 * (26 : ZMod 823727521) ^ 8743) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 386407110 := by rw [factor_7_13]; decide
      have factor_7_15 : (26 : ZMod 823727521) ^ 34974 = 404608713 := by
        calc
          (26 : ZMod 823727521) ^ 34974 = (26 : ZMod 823727521) ^ (17487 + 17487) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 17487 * (26 : ZMod 823727521) ^ 17487 := by rw [pow_add]
          _ = 404608713 := by rw [factor_7_14]; decide
      have factor_7_16 : (26 : ZMod 823727521) ^ 69949 = 434295838 := by
        calc
          (26 : ZMod 823727521) ^ 69949 = (26 : ZMod 823727521) ^ (34974 + 34974 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 34974 * (26 : ZMod 823727521) ^ 34974) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 434295838 := by rw [factor_7_15]; decide
      have factor_7_17 : (26 : ZMod 823727521) ^ 139899 = 495334821 := by
        calc
          (26 : ZMod 823727521) ^ 139899 = (26 : ZMod 823727521) ^ (69949 + 69949 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 69949 * (26 : ZMod 823727521) ^ 69949) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 495334821 := by rw [factor_7_16]; decide
      have factor_7_18 : (26 : ZMod 823727521) ^ 279798 = 47708859 := by
        calc
          (26 : ZMod 823727521) ^ 279798 = (26 : ZMod 823727521) ^ (139899 + 139899) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 139899 * (26 : ZMod 823727521) ^ 139899 := by rw [pow_add]
          _ = 47708859 := by rw [factor_7_17]; decide
      have factor_7_19 : (26 : ZMod 823727521) ^ 559597 = 796696709 := by
        calc
          (26 : ZMod 823727521) ^ 559597 = (26 : ZMod 823727521) ^ (279798 + 279798 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 279798 * (26 : ZMod 823727521) ^ 279798) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 796696709 := by rw [factor_7_18]; decide
      have factor_7_20 : (26 : ZMod 823727521) ^ 1119195 = 409416201 := by
        calc
          (26 : ZMod 823727521) ^ 1119195 = (26 : ZMod 823727521) ^ (559597 + 559597 + 1) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = ((26 : ZMod 823727521) ^ 559597 * (26 : ZMod 823727521) ^ 559597) * (26 : ZMod 823727521) := by rw [pow_succ, pow_add]
          _ = 409416201 := by rw [factor_7_19]; decide
      have factor_7_21 : (26 : ZMod 823727521) ^ 2238390 = 195041448 := by
        calc
          (26 : ZMod 823727521) ^ 2238390 = (26 : ZMod 823727521) ^ (1119195 + 1119195) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 1119195 * (26 : ZMod 823727521) ^ 1119195 := by rw [pow_add]
          _ = 195041448 := by rw [factor_7_20]; decide
      have factor_7_22 : (26 : ZMod 823727521) ^ 4476780 = 350907769 := by
        calc
          (26 : ZMod 823727521) ^ 4476780 = (26 : ZMod 823727521) ^ (2238390 + 2238390) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 2238390 * (26 : ZMod 823727521) ^ 2238390 := by rw [pow_add]
          _ = 350907769 := by rw [factor_7_21]; decide
      have factor_7_23 : (26 : ZMod 823727521) ^ 8953560 = 483555358 := by
        calc
          (26 : ZMod 823727521) ^ 8953560 = (26 : ZMod 823727521) ^ (4476780 + 4476780) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 4476780 * (26 : ZMod 823727521) ^ 4476780 := by rw [pow_add]
          _ = 483555358 := by rw [factor_7_22]; decide
      have factor_7_24 : (26 : ZMod 823727521) ^ 17907120 = 11152181 := by
        calc
          (26 : ZMod 823727521) ^ 17907120 = (26 : ZMod 823727521) ^ (8953560 + 8953560) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 8953560 * (26 : ZMod 823727521) ^ 8953560 := by rw [pow_add]
          _ = 11152181 := by rw [factor_7_23]; decide
      have factor_7_25 : (26 : ZMod 823727521) ^ 35814240 = 641298576 := by
        calc
          (26 : ZMod 823727521) ^ 35814240 = (26 : ZMod 823727521) ^ (17907120 + 17907120) :=
            congrArg (fun n : ℕ => (26 : ZMod 823727521) ^ n) (by norm_num)
          _ = (26 : ZMod 823727521) ^ 17907120 * (26 : ZMod 823727521) ^ 17907120 := by rw [pow_add]
          _ = 641298576 := by rw [factor_7_24]; decide
      change (26 : ZMod 823727521) ^ 35814240 ≠ 1
      rw [factor_7_25]
      decide

#print axioms prime_lucas_823727521

end TotientTailPeriodKiller
end Erdos249257
