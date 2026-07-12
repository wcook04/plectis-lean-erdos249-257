import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_26771144401 : Nat.Prime 26771144401 := by
  apply lucas_primality 26771144401 (67 : ZMod 26771144401)
  ·
      have fermat_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have fermat_1 : (67 : ZMod 26771144401) ^ 3 = 300763 := by
        calc
          (67 : ZMod 26771144401) ^ 3 = (67 : ZMod 26771144401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 300763 := by rw [fermat_0]; decide
      have fermat_2 : (67 : ZMod 26771144401) ^ 6 = 10144948966 := by
        calc
          (67 : ZMod 26771144401) ^ 6 = (67 : ZMod 26771144401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 3 * (67 : ZMod 26771144401) ^ 3 := by rw [pow_add]
          _ = 10144948966 := by rw [fermat_1]; decide
      have fermat_3 : (67 : ZMod 26771144401) ^ 12 = 23918572929 := by
        calc
          (67 : ZMod 26771144401) ^ 12 = (67 : ZMod 26771144401) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 6 * (67 : ZMod 26771144401) ^ 6 := by rw [pow_add]
          _ = 23918572929 := by rw [fermat_2]; decide
      have fermat_4 : (67 : ZMod 26771144401) ^ 24 = 24233706796 := by
        calc
          (67 : ZMod 26771144401) ^ 24 = (67 : ZMod 26771144401) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 12 * (67 : ZMod 26771144401) ^ 12 := by rw [pow_add]
          _ = 24233706796 := by rw [fermat_3]; decide
      have fermat_5 : (67 : ZMod 26771144401) ^ 49 = 18173179900 := by
        calc
          (67 : ZMod 26771144401) ^ 49 = (67 : ZMod 26771144401) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 24 * (67 : ZMod 26771144401) ^ 24) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 18173179900 := by rw [fermat_4]; decide
      have fermat_6 : (67 : ZMod 26771144401) ^ 99 = 25765518015 := by
        calc
          (67 : ZMod 26771144401) ^ 99 = (67 : ZMod 26771144401) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 49 * (67 : ZMod 26771144401) ^ 49) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 25765518015 := by rw [fermat_5]; decide
      have fermat_7 : (67 : ZMod 26771144401) ^ 199 = 4449665399 := by
        calc
          (67 : ZMod 26771144401) ^ 199 = (67 : ZMod 26771144401) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 99 * (67 : ZMod 26771144401) ^ 99) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4449665399 := by rw [fermat_6]; decide
      have fermat_8 : (67 : ZMod 26771144401) ^ 398 = 1831375949 := by
        calc
          (67 : ZMod 26771144401) ^ 398 = (67 : ZMod 26771144401) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 199 * (67 : ZMod 26771144401) ^ 199 := by rw [pow_add]
          _ = 1831375949 := by rw [fermat_7]; decide
      have fermat_9 : (67 : ZMod 26771144401) ^ 797 = 21519335496 := by
        calc
          (67 : ZMod 26771144401) ^ 797 = (67 : ZMod 26771144401) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 398 * (67 : ZMod 26771144401) ^ 398) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 21519335496 := by rw [fermat_8]; decide
      have fermat_10 : (67 : ZMod 26771144401) ^ 1595 = 4015372521 := by
        calc
          (67 : ZMod 26771144401) ^ 1595 = (67 : ZMod 26771144401) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 797 * (67 : ZMod 26771144401) ^ 797) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4015372521 := by rw [fermat_9]; decide
      have fermat_11 : (67 : ZMod 26771144401) ^ 3191 = 14569038436 := by
        calc
          (67 : ZMod 26771144401) ^ 3191 = (67 : ZMod 26771144401) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1595 * (67 : ZMod 26771144401) ^ 1595) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 14569038436 := by rw [fermat_10]; decide
      have fermat_12 : (67 : ZMod 26771144401) ^ 6382 = 17487415323 := by
        calc
          (67 : ZMod 26771144401) ^ 6382 = (67 : ZMod 26771144401) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 3191 * (67 : ZMod 26771144401) ^ 3191 := by rw [pow_add]
          _ = 17487415323 := by rw [fermat_11]; decide
      have fermat_13 : (67 : ZMod 26771144401) ^ 12765 = 13874334530 := by
        calc
          (67 : ZMod 26771144401) ^ 12765 = (67 : ZMod 26771144401) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 6382 * (67 : ZMod 26771144401) ^ 6382) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 13874334530 := by rw [fermat_12]; decide
      have fermat_14 : (67 : ZMod 26771144401) ^ 25530 = 22172228709 := by
        calc
          (67 : ZMod 26771144401) ^ 25530 = (67 : ZMod 26771144401) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 12765 * (67 : ZMod 26771144401) ^ 12765 := by rw [pow_add]
          _ = 22172228709 := by rw [fermat_13]; decide
      have fermat_15 : (67 : ZMod 26771144401) ^ 51061 = 24100653612 := by
        calc
          (67 : ZMod 26771144401) ^ 51061 = (67 : ZMod 26771144401) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 25530 * (67 : ZMod 26771144401) ^ 25530) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 24100653612 := by rw [fermat_14]; decide
      have fermat_16 : (67 : ZMod 26771144401) ^ 102123 = 981723683 := by
        calc
          (67 : ZMod 26771144401) ^ 102123 = (67 : ZMod 26771144401) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 51061 * (67 : ZMod 26771144401) ^ 51061) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 981723683 := by rw [fermat_15]; decide
      have fermat_17 : (67 : ZMod 26771144401) ^ 204247 = 19445789431 := by
        calc
          (67 : ZMod 26771144401) ^ 204247 = (67 : ZMod 26771144401) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 102123 * (67 : ZMod 26771144401) ^ 102123) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 19445789431 := by rw [fermat_16]; decide
      have fermat_18 : (67 : ZMod 26771144401) ^ 408495 = 15831754899 := by
        calc
          (67 : ZMod 26771144401) ^ 408495 = (67 : ZMod 26771144401) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 204247 * (67 : ZMod 26771144401) ^ 204247) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 15831754899 := by rw [fermat_17]; decide
      have fermat_19 : (67 : ZMod 26771144401) ^ 816990 = 22853700657 := by
        calc
          (67 : ZMod 26771144401) ^ 816990 = (67 : ZMod 26771144401) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 408495 * (67 : ZMod 26771144401) ^ 408495 := by rw [pow_add]
          _ = 22853700657 := by rw [fermat_18]; decide
      have fermat_20 : (67 : ZMod 26771144401) ^ 1633980 = 6253763147 := by
        calc
          (67 : ZMod 26771144401) ^ 1633980 = (67 : ZMod 26771144401) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 816990 * (67 : ZMod 26771144401) ^ 816990 := by rw [pow_add]
          _ = 6253763147 := by rw [fermat_19]; decide
      have fermat_21 : (67 : ZMod 26771144401) ^ 3267961 = 24679695704 := by
        calc
          (67 : ZMod 26771144401) ^ 3267961 = (67 : ZMod 26771144401) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1633980 * (67 : ZMod 26771144401) ^ 1633980) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 24679695704 := by rw [fermat_20]; decide
      have fermat_22 : (67 : ZMod 26771144401) ^ 6535923 = 3884737827 := by
        calc
          (67 : ZMod 26771144401) ^ 6535923 = (67 : ZMod 26771144401) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 3267961 * (67 : ZMod 26771144401) ^ 3267961) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3884737827 := by rw [fermat_21]; decide
      have fermat_23 : (67 : ZMod 26771144401) ^ 13071847 = 3291987337 := by
        calc
          (67 : ZMod 26771144401) ^ 13071847 = (67 : ZMod 26771144401) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 6535923 * (67 : ZMod 26771144401) ^ 6535923) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3291987337 := by rw [fermat_22]; decide
      have fermat_24 : (67 : ZMod 26771144401) ^ 26143695 = 3585469093 := by
        calc
          (67 : ZMod 26771144401) ^ 26143695 = (67 : ZMod 26771144401) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 13071847 * (67 : ZMod 26771144401) ^ 13071847) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3585469093 := by rw [fermat_23]; decide
      have fermat_25 : (67 : ZMod 26771144401) ^ 52287391 = 26616429766 := by
        calc
          (67 : ZMod 26771144401) ^ 52287391 = (67 : ZMod 26771144401) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 26143695 * (67 : ZMod 26771144401) ^ 26143695) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 26616429766 := by rw [fermat_24]; decide
      have fermat_26 : (67 : ZMod 26771144401) ^ 104574782 = 2651361105 := by
        calc
          (67 : ZMod 26771144401) ^ 104574782 = (67 : ZMod 26771144401) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 52287391 * (67 : ZMod 26771144401) ^ 52287391 := by rw [pow_add]
          _ = 2651361105 := by rw [fermat_25]; decide
      have fermat_27 : (67 : ZMod 26771144401) ^ 209149565 = 5071940344 := by
        calc
          (67 : ZMod 26771144401) ^ 209149565 = (67 : ZMod 26771144401) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 104574782 * (67 : ZMod 26771144401) ^ 104574782) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 5071940344 := by rw [fermat_26]; decide
      have fermat_28 : (67 : ZMod 26771144401) ^ 418299131 = 4676435715 := by
        calc
          (67 : ZMod 26771144401) ^ 418299131 = (67 : ZMod 26771144401) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 209149565 * (67 : ZMod 26771144401) ^ 209149565) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4676435715 := by rw [fermat_27]; decide
      have fermat_29 : (67 : ZMod 26771144401) ^ 836598262 = 570923914 := by
        calc
          (67 : ZMod 26771144401) ^ 836598262 = (67 : ZMod 26771144401) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 418299131 * (67 : ZMod 26771144401) ^ 418299131 := by rw [pow_add]
          _ = 570923914 := by rw [fermat_28]; decide
      have fermat_30 : (67 : ZMod 26771144401) ^ 1673196525 = 22019539110 := by
        calc
          (67 : ZMod 26771144401) ^ 1673196525 = (67 : ZMod 26771144401) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 836598262 * (67 : ZMod 26771144401) ^ 836598262) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22019539110 := by rw [fermat_29]; decide
      have fermat_31 : (67 : ZMod 26771144401) ^ 3346393050 = 21461500369 := by
        calc
          (67 : ZMod 26771144401) ^ 3346393050 = (67 : ZMod 26771144401) ^ (1673196525 + 1673196525) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1673196525 * (67 : ZMod 26771144401) ^ 1673196525 := by rw [pow_add]
          _ = 21461500369 := by rw [fermat_30]; decide
      have fermat_32 : (67 : ZMod 26771144401) ^ 6692786100 = 18021023736 := by
        calc
          (67 : ZMod 26771144401) ^ 6692786100 = (67 : ZMod 26771144401) ^ (3346393050 + 3346393050) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 3346393050 * (67 : ZMod 26771144401) ^ 3346393050 := by rw [pow_add]
          _ = 18021023736 := by rw [fermat_31]; decide
      have fermat_33 : (67 : ZMod 26771144401) ^ 13385572200 = 26771144400 := by
        calc
          (67 : ZMod 26771144401) ^ 13385572200 = (67 : ZMod 26771144401) ^ (6692786100 + 6692786100) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 6692786100 * (67 : ZMod 26771144401) ^ 6692786100 := by rw [pow_add]
          _ = 26771144400 := by rw [fermat_32]; decide
      have fermat_34 : (67 : ZMod 26771144401) ^ 26771144400 = 1 := by
        calc
          (67 : ZMod 26771144401) ^ 26771144400 = (67 : ZMod 26771144401) ^ (13385572200 + 13385572200) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 13385572200 * (67 : ZMod 26771144401) ^ 13385572200 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 26771144401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have factor_0_1 : (67 : ZMod 26771144401) ^ 3 = 300763 := by
        calc
          (67 : ZMod 26771144401) ^ 3 = (67 : ZMod 26771144401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 300763 := by rw [factor_0_0]; decide
      have factor_0_2 : (67 : ZMod 26771144401) ^ 6 = 10144948966 := by
        calc
          (67 : ZMod 26771144401) ^ 6 = (67 : ZMod 26771144401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 3 * (67 : ZMod 26771144401) ^ 3 := by rw [pow_add]
          _ = 10144948966 := by rw [factor_0_1]; decide
      have factor_0_3 : (67 : ZMod 26771144401) ^ 12 = 23918572929 := by
        calc
          (67 : ZMod 26771144401) ^ 12 = (67 : ZMod 26771144401) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 6 * (67 : ZMod 26771144401) ^ 6 := by rw [pow_add]
          _ = 23918572929 := by rw [factor_0_2]; decide
      have factor_0_4 : (67 : ZMod 26771144401) ^ 24 = 24233706796 := by
        calc
          (67 : ZMod 26771144401) ^ 24 = (67 : ZMod 26771144401) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 12 * (67 : ZMod 26771144401) ^ 12 := by rw [pow_add]
          _ = 24233706796 := by rw [factor_0_3]; decide
      have factor_0_5 : (67 : ZMod 26771144401) ^ 49 = 18173179900 := by
        calc
          (67 : ZMod 26771144401) ^ 49 = (67 : ZMod 26771144401) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 24 * (67 : ZMod 26771144401) ^ 24) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 18173179900 := by rw [factor_0_4]; decide
      have factor_0_6 : (67 : ZMod 26771144401) ^ 99 = 25765518015 := by
        calc
          (67 : ZMod 26771144401) ^ 99 = (67 : ZMod 26771144401) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 49 * (67 : ZMod 26771144401) ^ 49) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 25765518015 := by rw [factor_0_5]; decide
      have factor_0_7 : (67 : ZMod 26771144401) ^ 199 = 4449665399 := by
        calc
          (67 : ZMod 26771144401) ^ 199 = (67 : ZMod 26771144401) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 99 * (67 : ZMod 26771144401) ^ 99) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4449665399 := by rw [factor_0_6]; decide
      have factor_0_8 : (67 : ZMod 26771144401) ^ 398 = 1831375949 := by
        calc
          (67 : ZMod 26771144401) ^ 398 = (67 : ZMod 26771144401) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 199 * (67 : ZMod 26771144401) ^ 199 := by rw [pow_add]
          _ = 1831375949 := by rw [factor_0_7]; decide
      have factor_0_9 : (67 : ZMod 26771144401) ^ 797 = 21519335496 := by
        calc
          (67 : ZMod 26771144401) ^ 797 = (67 : ZMod 26771144401) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 398 * (67 : ZMod 26771144401) ^ 398) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 21519335496 := by rw [factor_0_8]; decide
      have factor_0_10 : (67 : ZMod 26771144401) ^ 1595 = 4015372521 := by
        calc
          (67 : ZMod 26771144401) ^ 1595 = (67 : ZMod 26771144401) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 797 * (67 : ZMod 26771144401) ^ 797) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4015372521 := by rw [factor_0_9]; decide
      have factor_0_11 : (67 : ZMod 26771144401) ^ 3191 = 14569038436 := by
        calc
          (67 : ZMod 26771144401) ^ 3191 = (67 : ZMod 26771144401) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1595 * (67 : ZMod 26771144401) ^ 1595) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 14569038436 := by rw [factor_0_10]; decide
      have factor_0_12 : (67 : ZMod 26771144401) ^ 6382 = 17487415323 := by
        calc
          (67 : ZMod 26771144401) ^ 6382 = (67 : ZMod 26771144401) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 3191 * (67 : ZMod 26771144401) ^ 3191 := by rw [pow_add]
          _ = 17487415323 := by rw [factor_0_11]; decide
      have factor_0_13 : (67 : ZMod 26771144401) ^ 12765 = 13874334530 := by
        calc
          (67 : ZMod 26771144401) ^ 12765 = (67 : ZMod 26771144401) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 6382 * (67 : ZMod 26771144401) ^ 6382) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 13874334530 := by rw [factor_0_12]; decide
      have factor_0_14 : (67 : ZMod 26771144401) ^ 25530 = 22172228709 := by
        calc
          (67 : ZMod 26771144401) ^ 25530 = (67 : ZMod 26771144401) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 12765 * (67 : ZMod 26771144401) ^ 12765 := by rw [pow_add]
          _ = 22172228709 := by rw [factor_0_13]; decide
      have factor_0_15 : (67 : ZMod 26771144401) ^ 51061 = 24100653612 := by
        calc
          (67 : ZMod 26771144401) ^ 51061 = (67 : ZMod 26771144401) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 25530 * (67 : ZMod 26771144401) ^ 25530) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 24100653612 := by rw [factor_0_14]; decide
      have factor_0_16 : (67 : ZMod 26771144401) ^ 102123 = 981723683 := by
        calc
          (67 : ZMod 26771144401) ^ 102123 = (67 : ZMod 26771144401) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 51061 * (67 : ZMod 26771144401) ^ 51061) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 981723683 := by rw [factor_0_15]; decide
      have factor_0_17 : (67 : ZMod 26771144401) ^ 204247 = 19445789431 := by
        calc
          (67 : ZMod 26771144401) ^ 204247 = (67 : ZMod 26771144401) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 102123 * (67 : ZMod 26771144401) ^ 102123) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 19445789431 := by rw [factor_0_16]; decide
      have factor_0_18 : (67 : ZMod 26771144401) ^ 408495 = 15831754899 := by
        calc
          (67 : ZMod 26771144401) ^ 408495 = (67 : ZMod 26771144401) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 204247 * (67 : ZMod 26771144401) ^ 204247) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 15831754899 := by rw [factor_0_17]; decide
      have factor_0_19 : (67 : ZMod 26771144401) ^ 816990 = 22853700657 := by
        calc
          (67 : ZMod 26771144401) ^ 816990 = (67 : ZMod 26771144401) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 408495 * (67 : ZMod 26771144401) ^ 408495 := by rw [pow_add]
          _ = 22853700657 := by rw [factor_0_18]; decide
      have factor_0_20 : (67 : ZMod 26771144401) ^ 1633980 = 6253763147 := by
        calc
          (67 : ZMod 26771144401) ^ 1633980 = (67 : ZMod 26771144401) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 816990 * (67 : ZMod 26771144401) ^ 816990 := by rw [pow_add]
          _ = 6253763147 := by rw [factor_0_19]; decide
      have factor_0_21 : (67 : ZMod 26771144401) ^ 3267961 = 24679695704 := by
        calc
          (67 : ZMod 26771144401) ^ 3267961 = (67 : ZMod 26771144401) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1633980 * (67 : ZMod 26771144401) ^ 1633980) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 24679695704 := by rw [factor_0_20]; decide
      have factor_0_22 : (67 : ZMod 26771144401) ^ 6535923 = 3884737827 := by
        calc
          (67 : ZMod 26771144401) ^ 6535923 = (67 : ZMod 26771144401) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 3267961 * (67 : ZMod 26771144401) ^ 3267961) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3884737827 := by rw [factor_0_21]; decide
      have factor_0_23 : (67 : ZMod 26771144401) ^ 13071847 = 3291987337 := by
        calc
          (67 : ZMod 26771144401) ^ 13071847 = (67 : ZMod 26771144401) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 6535923 * (67 : ZMod 26771144401) ^ 6535923) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3291987337 := by rw [factor_0_22]; decide
      have factor_0_24 : (67 : ZMod 26771144401) ^ 26143695 = 3585469093 := by
        calc
          (67 : ZMod 26771144401) ^ 26143695 = (67 : ZMod 26771144401) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 13071847 * (67 : ZMod 26771144401) ^ 13071847) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3585469093 := by rw [factor_0_23]; decide
      have factor_0_25 : (67 : ZMod 26771144401) ^ 52287391 = 26616429766 := by
        calc
          (67 : ZMod 26771144401) ^ 52287391 = (67 : ZMod 26771144401) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 26143695 * (67 : ZMod 26771144401) ^ 26143695) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 26616429766 := by rw [factor_0_24]; decide
      have factor_0_26 : (67 : ZMod 26771144401) ^ 104574782 = 2651361105 := by
        calc
          (67 : ZMod 26771144401) ^ 104574782 = (67 : ZMod 26771144401) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 52287391 * (67 : ZMod 26771144401) ^ 52287391 := by rw [pow_add]
          _ = 2651361105 := by rw [factor_0_25]; decide
      have factor_0_27 : (67 : ZMod 26771144401) ^ 209149565 = 5071940344 := by
        calc
          (67 : ZMod 26771144401) ^ 209149565 = (67 : ZMod 26771144401) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 104574782 * (67 : ZMod 26771144401) ^ 104574782) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 5071940344 := by rw [factor_0_26]; decide
      have factor_0_28 : (67 : ZMod 26771144401) ^ 418299131 = 4676435715 := by
        calc
          (67 : ZMod 26771144401) ^ 418299131 = (67 : ZMod 26771144401) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 209149565 * (67 : ZMod 26771144401) ^ 209149565) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4676435715 := by rw [factor_0_27]; decide
      have factor_0_29 : (67 : ZMod 26771144401) ^ 836598262 = 570923914 := by
        calc
          (67 : ZMod 26771144401) ^ 836598262 = (67 : ZMod 26771144401) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 418299131 * (67 : ZMod 26771144401) ^ 418299131 := by rw [pow_add]
          _ = 570923914 := by rw [factor_0_28]; decide
      have factor_0_30 : (67 : ZMod 26771144401) ^ 1673196525 = 22019539110 := by
        calc
          (67 : ZMod 26771144401) ^ 1673196525 = (67 : ZMod 26771144401) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 836598262 * (67 : ZMod 26771144401) ^ 836598262) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22019539110 := by rw [factor_0_29]; decide
      have factor_0_31 : (67 : ZMod 26771144401) ^ 3346393050 = 21461500369 := by
        calc
          (67 : ZMod 26771144401) ^ 3346393050 = (67 : ZMod 26771144401) ^ (1673196525 + 1673196525) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1673196525 * (67 : ZMod 26771144401) ^ 1673196525 := by rw [pow_add]
          _ = 21461500369 := by rw [factor_0_30]; decide
      have factor_0_32 : (67 : ZMod 26771144401) ^ 6692786100 = 18021023736 := by
        calc
          (67 : ZMod 26771144401) ^ 6692786100 = (67 : ZMod 26771144401) ^ (3346393050 + 3346393050) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 3346393050 * (67 : ZMod 26771144401) ^ 3346393050 := by rw [pow_add]
          _ = 18021023736 := by rw [factor_0_31]; decide
      have factor_0_33 : (67 : ZMod 26771144401) ^ 13385572200 = 26771144400 := by
        calc
          (67 : ZMod 26771144401) ^ 13385572200 = (67 : ZMod 26771144401) ^ (6692786100 + 6692786100) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 6692786100 * (67 : ZMod 26771144401) ^ 6692786100 := by rw [pow_add]
          _ = 26771144400 := by rw [factor_0_32]; decide
      change (67 : ZMod 26771144401) ^ 13385572200 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have factor_1_1 : (67 : ZMod 26771144401) ^ 2 = 4489 := by
        calc
          (67 : ZMod 26771144401) ^ 2 = (67 : ZMod 26771144401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1 := by rw [pow_add]
          _ = 4489 := by rw [factor_1_0]; decide
      have factor_1_2 : (67 : ZMod 26771144401) ^ 4 = 20151121 := by
        calc
          (67 : ZMod 26771144401) ^ 4 = (67 : ZMod 26771144401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2 * (67 : ZMod 26771144401) ^ 2 := by rw [pow_add]
          _ = 20151121 := by rw [factor_1_1]; decide
      have factor_1_3 : (67 : ZMod 26771144401) ^ 8 = 2959282273 := by
        calc
          (67 : ZMod 26771144401) ^ 8 = (67 : ZMod 26771144401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 4 * (67 : ZMod 26771144401) ^ 4 := by rw [pow_add]
          _ = 2959282273 := by rw [factor_1_2]; decide
      have factor_1_4 : (67 : ZMod 26771144401) ^ 16 = 6483807870 := by
        calc
          (67 : ZMod 26771144401) ^ 16 = (67 : ZMod 26771144401) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 8 * (67 : ZMod 26771144401) ^ 8 := by rw [pow_add]
          _ = 6483807870 := by rw [factor_1_3]; decide
      have factor_1_5 : (67 : ZMod 26771144401) ^ 33 = 8384207202 := by
        calc
          (67 : ZMod 26771144401) ^ 33 = (67 : ZMod 26771144401) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 16 * (67 : ZMod 26771144401) ^ 16) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 8384207202 := by rw [factor_1_4]; decide
      have factor_1_6 : (67 : ZMod 26771144401) ^ 66 = 8090433667 := by
        calc
          (67 : ZMod 26771144401) ^ 66 = (67 : ZMod 26771144401) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 33 * (67 : ZMod 26771144401) ^ 33 := by rw [pow_add]
          _ = 8090433667 := by rw [factor_1_5]; decide
      have factor_1_7 : (67 : ZMod 26771144401) ^ 132 = 18738307259 := by
        calc
          (67 : ZMod 26771144401) ^ 132 = (67 : ZMod 26771144401) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 66 * (67 : ZMod 26771144401) ^ 66 := by rw [pow_add]
          _ = 18738307259 := by rw [factor_1_6]; decide
      have factor_1_8 : (67 : ZMod 26771144401) ^ 265 = 3783027033 := by
        calc
          (67 : ZMod 26771144401) ^ 265 = (67 : ZMod 26771144401) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 132 * (67 : ZMod 26771144401) ^ 132) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3783027033 := by rw [factor_1_7]; decide
      have factor_1_9 : (67 : ZMod 26771144401) ^ 531 = 9806161534 := by
        calc
          (67 : ZMod 26771144401) ^ 531 = (67 : ZMod 26771144401) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 265 * (67 : ZMod 26771144401) ^ 265) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 9806161534 := by rw [factor_1_8]; decide
      have factor_1_10 : (67 : ZMod 26771144401) ^ 1063 = 11425080786 := by
        calc
          (67 : ZMod 26771144401) ^ 1063 = (67 : ZMod 26771144401) ^ (531 + 531 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 531 * (67 : ZMod 26771144401) ^ 531) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 11425080786 := by rw [factor_1_9]; decide
      have factor_1_11 : (67 : ZMod 26771144401) ^ 2127 = 3094423343 := by
        calc
          (67 : ZMod 26771144401) ^ 2127 = (67 : ZMod 26771144401) ^ (1063 + 1063 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1063 * (67 : ZMod 26771144401) ^ 1063) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3094423343 := by rw [factor_1_10]; decide
      have factor_1_12 : (67 : ZMod 26771144401) ^ 4255 = 25592249170 := by
        calc
          (67 : ZMod 26771144401) ^ 4255 = (67 : ZMod 26771144401) ^ (2127 + 2127 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 2127 * (67 : ZMod 26771144401) ^ 2127) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 25592249170 := by rw [factor_1_11]; decide
      have factor_1_13 : (67 : ZMod 26771144401) ^ 8510 = 14549501882 := by
        calc
          (67 : ZMod 26771144401) ^ 8510 = (67 : ZMod 26771144401) ^ (4255 + 4255) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 4255 * (67 : ZMod 26771144401) ^ 4255 := by rw [pow_add]
          _ = 14549501882 := by rw [factor_1_12]; decide
      have factor_1_14 : (67 : ZMod 26771144401) ^ 17020 = 4829109944 := by
        calc
          (67 : ZMod 26771144401) ^ 17020 = (67 : ZMod 26771144401) ^ (8510 + 8510) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 8510 * (67 : ZMod 26771144401) ^ 8510 := by rw [pow_add]
          _ = 4829109944 := by rw [factor_1_13]; decide
      have factor_1_15 : (67 : ZMod 26771144401) ^ 34041 = 6487341614 := by
        calc
          (67 : ZMod 26771144401) ^ 34041 = (67 : ZMod 26771144401) ^ (17020 + 17020 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 17020 * (67 : ZMod 26771144401) ^ 17020) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 6487341614 := by rw [factor_1_14]; decide
      have factor_1_16 : (67 : ZMod 26771144401) ^ 68082 = 22223568913 := by
        calc
          (67 : ZMod 26771144401) ^ 68082 = (67 : ZMod 26771144401) ^ (34041 + 34041) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 34041 * (67 : ZMod 26771144401) ^ 34041 := by rw [pow_add]
          _ = 22223568913 := by rw [factor_1_15]; decide
      have factor_1_17 : (67 : ZMod 26771144401) ^ 136165 = 21816519943 := by
        calc
          (67 : ZMod 26771144401) ^ 136165 = (67 : ZMod 26771144401) ^ (68082 + 68082 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 68082 * (67 : ZMod 26771144401) ^ 68082) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 21816519943 := by rw [factor_1_16]; decide
      have factor_1_18 : (67 : ZMod 26771144401) ^ 272330 = 6307570588 := by
        calc
          (67 : ZMod 26771144401) ^ 272330 = (67 : ZMod 26771144401) ^ (136165 + 136165) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 136165 * (67 : ZMod 26771144401) ^ 136165 := by rw [pow_add]
          _ = 6307570588 := by rw [factor_1_17]; decide
      have factor_1_19 : (67 : ZMod 26771144401) ^ 544660 = 8203032430 := by
        calc
          (67 : ZMod 26771144401) ^ 544660 = (67 : ZMod 26771144401) ^ (272330 + 272330) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 272330 * (67 : ZMod 26771144401) ^ 272330 := by rw [pow_add]
          _ = 8203032430 := by rw [factor_1_18]; decide
      have factor_1_20 : (67 : ZMod 26771144401) ^ 1089320 = 3074266959 := by
        calc
          (67 : ZMod 26771144401) ^ 1089320 = (67 : ZMod 26771144401) ^ (544660 + 544660) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 544660 * (67 : ZMod 26771144401) ^ 544660 := by rw [pow_add]
          _ = 3074266959 := by rw [factor_1_19]; decide
      have factor_1_21 : (67 : ZMod 26771144401) ^ 2178641 = 9723946589 := by
        calc
          (67 : ZMod 26771144401) ^ 2178641 = (67 : ZMod 26771144401) ^ (1089320 + 1089320 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1089320 * (67 : ZMod 26771144401) ^ 1089320) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 9723946589 := by rw [factor_1_20]; decide
      have factor_1_22 : (67 : ZMod 26771144401) ^ 4357282 = 7410150870 := by
        calc
          (67 : ZMod 26771144401) ^ 4357282 = (67 : ZMod 26771144401) ^ (2178641 + 2178641) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2178641 * (67 : ZMod 26771144401) ^ 2178641 := by rw [pow_add]
          _ = 7410150870 := by rw [factor_1_21]; decide
      have factor_1_23 : (67 : ZMod 26771144401) ^ 8714565 = 9887428100 := by
        calc
          (67 : ZMod 26771144401) ^ 8714565 = (67 : ZMod 26771144401) ^ (4357282 + 4357282 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 4357282 * (67 : ZMod 26771144401) ^ 4357282) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 9887428100 := by rw [factor_1_22]; decide
      have factor_1_24 : (67 : ZMod 26771144401) ^ 17429130 = 19816708113 := by
        calc
          (67 : ZMod 26771144401) ^ 17429130 = (67 : ZMod 26771144401) ^ (8714565 + 8714565) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 8714565 * (67 : ZMod 26771144401) ^ 8714565 := by rw [pow_add]
          _ = 19816708113 := by rw [factor_1_23]; decide
      have factor_1_25 : (67 : ZMod 26771144401) ^ 34858260 = 15574368064 := by
        calc
          (67 : ZMod 26771144401) ^ 34858260 = (67 : ZMod 26771144401) ^ (17429130 + 17429130) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 17429130 * (67 : ZMod 26771144401) ^ 17429130 := by rw [pow_add]
          _ = 15574368064 := by rw [factor_1_24]; decide
      have factor_1_26 : (67 : ZMod 26771144401) ^ 69716521 = 4044429704 := by
        calc
          (67 : ZMod 26771144401) ^ 69716521 = (67 : ZMod 26771144401) ^ (34858260 + 34858260 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 34858260 * (67 : ZMod 26771144401) ^ 34858260) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4044429704 := by rw [factor_1_25]; decide
      have factor_1_27 : (67 : ZMod 26771144401) ^ 139433043 = 4148472815 := by
        calc
          (67 : ZMod 26771144401) ^ 139433043 = (67 : ZMod 26771144401) ^ (69716521 + 69716521 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 69716521 * (67 : ZMod 26771144401) ^ 69716521) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4148472815 := by rw [factor_1_26]; decide
      have factor_1_28 : (67 : ZMod 26771144401) ^ 278866087 = 3929838988 := by
        calc
          (67 : ZMod 26771144401) ^ 278866087 = (67 : ZMod 26771144401) ^ (139433043 + 139433043 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 139433043 * (67 : ZMod 26771144401) ^ 139433043) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3929838988 := by rw [factor_1_27]; decide
      have factor_1_29 : (67 : ZMod 26771144401) ^ 557732175 = 13491538203 := by
        calc
          (67 : ZMod 26771144401) ^ 557732175 = (67 : ZMod 26771144401) ^ (278866087 + 278866087 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 278866087 * (67 : ZMod 26771144401) ^ 278866087) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 13491538203 := by rw [factor_1_28]; decide
      have factor_1_30 : (67 : ZMod 26771144401) ^ 1115464350 = 5270066070 := by
        calc
          (67 : ZMod 26771144401) ^ 1115464350 = (67 : ZMod 26771144401) ^ (557732175 + 557732175) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 557732175 * (67 : ZMod 26771144401) ^ 557732175 := by rw [pow_add]
          _ = 5270066070 := by rw [factor_1_29]; decide
      have factor_1_31 : (67 : ZMod 26771144401) ^ 2230928700 = 452854858 := by
        calc
          (67 : ZMod 26771144401) ^ 2230928700 = (67 : ZMod 26771144401) ^ (1115464350 + 1115464350) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1115464350 * (67 : ZMod 26771144401) ^ 1115464350 := by rw [pow_add]
          _ = 452854858 := by rw [factor_1_30]; decide
      have factor_1_32 : (67 : ZMod 26771144401) ^ 4461857400 = 8471646170 := by
        calc
          (67 : ZMod 26771144401) ^ 4461857400 = (67 : ZMod 26771144401) ^ (2230928700 + 2230928700) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2230928700 * (67 : ZMod 26771144401) ^ 2230928700 := by rw [pow_add]
          _ = 8471646170 := by rw [factor_1_31]; decide
      have factor_1_33 : (67 : ZMod 26771144401) ^ 8923714800 = 8471646169 := by
        calc
          (67 : ZMod 26771144401) ^ 8923714800 = (67 : ZMod 26771144401) ^ (4461857400 + 4461857400) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 4461857400 * (67 : ZMod 26771144401) ^ 4461857400 := by rw [pow_add]
          _ = 8471646169 := by rw [factor_1_32]; decide
      change (67 : ZMod 26771144401) ^ 8923714800 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have factor_2_1 : (67 : ZMod 26771144401) ^ 2 = 4489 := by
        calc
          (67 : ZMod 26771144401) ^ 2 = (67 : ZMod 26771144401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1 := by rw [pow_add]
          _ = 4489 := by rw [factor_2_0]; decide
      have factor_2_2 : (67 : ZMod 26771144401) ^ 4 = 20151121 := by
        calc
          (67 : ZMod 26771144401) ^ 4 = (67 : ZMod 26771144401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2 * (67 : ZMod 26771144401) ^ 2 := by rw [pow_add]
          _ = 20151121 := by rw [factor_2_1]; decide
      have factor_2_3 : (67 : ZMod 26771144401) ^ 9 = 10873901484 := by
        calc
          (67 : ZMod 26771144401) ^ 9 = (67 : ZMod 26771144401) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 4 * (67 : ZMod 26771144401) ^ 4) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10873901484 := by rw [factor_2_2]; decide
      have factor_2_4 : (67 : ZMod 26771144401) ^ 19 = 25805947168 := by
        calc
          (67 : ZMod 26771144401) ^ 19 = (67 : ZMod 26771144401) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 9 * (67 : ZMod 26771144401) ^ 9) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 25805947168 := by rw [factor_2_3]; decide
      have factor_2_5 : (67 : ZMod 26771144401) ^ 39 = 10961317961 := by
        calc
          (67 : ZMod 26771144401) ^ 39 = (67 : ZMod 26771144401) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 19 * (67 : ZMod 26771144401) ^ 19) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10961317961 := by rw [factor_2_4]; decide
      have factor_2_6 : (67 : ZMod 26771144401) ^ 79 = 2835751182 := by
        calc
          (67 : ZMod 26771144401) ^ 79 = (67 : ZMod 26771144401) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 39 * (67 : ZMod 26771144401) ^ 39) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 2835751182 := by rw [factor_2_5]; decide
      have factor_2_7 : (67 : ZMod 26771144401) ^ 159 = 12949201566 := by
        calc
          (67 : ZMod 26771144401) ^ 159 = (67 : ZMod 26771144401) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 79 * (67 : ZMod 26771144401) ^ 79) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 12949201566 := by rw [factor_2_6]; decide
      have factor_2_8 : (67 : ZMod 26771144401) ^ 319 = 7546627806 := by
        calc
          (67 : ZMod 26771144401) ^ 319 = (67 : ZMod 26771144401) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 159 * (67 : ZMod 26771144401) ^ 159) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 7546627806 := by rw [factor_2_7]; decide
      have factor_2_9 : (67 : ZMod 26771144401) ^ 638 = 11795185741 := by
        calc
          (67 : ZMod 26771144401) ^ 638 = (67 : ZMod 26771144401) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 319 * (67 : ZMod 26771144401) ^ 319 := by rw [pow_add]
          _ = 11795185741 := by rw [factor_2_8]; decide
      have factor_2_10 : (67 : ZMod 26771144401) ^ 1276 = 7941320563 := by
        calc
          (67 : ZMod 26771144401) ^ 1276 = (67 : ZMod 26771144401) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 638 * (67 : ZMod 26771144401) ^ 638 := by rw [pow_add]
          _ = 7941320563 := by rw [factor_2_9]; decide
      have factor_2_11 : (67 : ZMod 26771144401) ^ 2553 = 10563863349 := by
        calc
          (67 : ZMod 26771144401) ^ 2553 = (67 : ZMod 26771144401) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1276 * (67 : ZMod 26771144401) ^ 1276) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10563863349 := by rw [factor_2_10]; decide
      have factor_2_12 : (67 : ZMod 26771144401) ^ 5106 = 3922676053 := by
        calc
          (67 : ZMod 26771144401) ^ 5106 = (67 : ZMod 26771144401) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2553 * (67 : ZMod 26771144401) ^ 2553 := by rw [pow_add]
          _ = 3922676053 := by rw [factor_2_11]; decide
      have factor_2_13 : (67 : ZMod 26771144401) ^ 10212 = 2411288501 := by
        calc
          (67 : ZMod 26771144401) ^ 10212 = (67 : ZMod 26771144401) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 5106 * (67 : ZMod 26771144401) ^ 5106 := by rw [pow_add]
          _ = 2411288501 := by rw [factor_2_12]; decide
      have factor_2_14 : (67 : ZMod 26771144401) ^ 20424 = 8806132008 := by
        calc
          (67 : ZMod 26771144401) ^ 20424 = (67 : ZMod 26771144401) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 10212 * (67 : ZMod 26771144401) ^ 10212 := by rw [pow_add]
          _ = 8806132008 := by rw [factor_2_13]; decide
      have factor_2_15 : (67 : ZMod 26771144401) ^ 40849 = 19122723334 := by
        calc
          (67 : ZMod 26771144401) ^ 40849 = (67 : ZMod 26771144401) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 20424 * (67 : ZMod 26771144401) ^ 20424) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 19122723334 := by rw [factor_2_14]; decide
      have factor_2_16 : (67 : ZMod 26771144401) ^ 81699 = 8932839462 := by
        calc
          (67 : ZMod 26771144401) ^ 81699 = (67 : ZMod 26771144401) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 40849 * (67 : ZMod 26771144401) ^ 40849) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 8932839462 := by rw [factor_2_15]; decide
      have factor_2_17 : (67 : ZMod 26771144401) ^ 163398 = 24988016827 := by
        calc
          (67 : ZMod 26771144401) ^ 163398 = (67 : ZMod 26771144401) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 81699 * (67 : ZMod 26771144401) ^ 81699 := by rw [pow_add]
          _ = 24988016827 := by rw [factor_2_16]; decide
      have factor_2_18 : (67 : ZMod 26771144401) ^ 326796 = 17906383500 := by
        calc
          (67 : ZMod 26771144401) ^ 326796 = (67 : ZMod 26771144401) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 163398 * (67 : ZMod 26771144401) ^ 163398 := by rw [pow_add]
          _ = 17906383500 := by rw [factor_2_17]; decide
      have factor_2_19 : (67 : ZMod 26771144401) ^ 653592 = 13297602976 := by
        calc
          (67 : ZMod 26771144401) ^ 653592 = (67 : ZMod 26771144401) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 326796 * (67 : ZMod 26771144401) ^ 326796 := by rw [pow_add]
          _ = 13297602976 := by rw [factor_2_18]; decide
      have factor_2_20 : (67 : ZMod 26771144401) ^ 1307184 = 3681214636 := by
        calc
          (67 : ZMod 26771144401) ^ 1307184 = (67 : ZMod 26771144401) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 653592 * (67 : ZMod 26771144401) ^ 653592 := by rw [pow_add]
          _ = 3681214636 := by rw [factor_2_19]; decide
      have factor_2_21 : (67 : ZMod 26771144401) ^ 2614369 = 20107720453 := by
        calc
          (67 : ZMod 26771144401) ^ 2614369 = (67 : ZMod 26771144401) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1307184 * (67 : ZMod 26771144401) ^ 1307184) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 20107720453 := by rw [factor_2_20]; decide
      have factor_2_22 : (67 : ZMod 26771144401) ^ 5228739 = 24988256027 := by
        calc
          (67 : ZMod 26771144401) ^ 5228739 = (67 : ZMod 26771144401) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 2614369 * (67 : ZMod 26771144401) ^ 2614369) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 24988256027 := by rw [factor_2_21]; decide
      have factor_2_23 : (67 : ZMod 26771144401) ^ 10457478 = 9094526562 := by
        calc
          (67 : ZMod 26771144401) ^ 10457478 = (67 : ZMod 26771144401) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 5228739 * (67 : ZMod 26771144401) ^ 5228739 := by rw [pow_add]
          _ = 9094526562 := by rw [factor_2_22]; decide
      have factor_2_24 : (67 : ZMod 26771144401) ^ 20914956 = 16139091082 := by
        calc
          (67 : ZMod 26771144401) ^ 20914956 = (67 : ZMod 26771144401) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 10457478 * (67 : ZMod 26771144401) ^ 10457478 := by rw [pow_add]
          _ = 16139091082 := by rw [factor_2_23]; decide
      have factor_2_25 : (67 : ZMod 26771144401) ^ 41829913 = 20512033841 := by
        calc
          (67 : ZMod 26771144401) ^ 41829913 = (67 : ZMod 26771144401) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 20914956 * (67 : ZMod 26771144401) ^ 20914956) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 20512033841 := by rw [factor_2_24]; decide
      have factor_2_26 : (67 : ZMod 26771144401) ^ 83659826 = 8454208377 := by
        calc
          (67 : ZMod 26771144401) ^ 83659826 = (67 : ZMod 26771144401) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 41829913 * (67 : ZMod 26771144401) ^ 41829913 := by rw [pow_add]
          _ = 8454208377 := by rw [factor_2_25]; decide
      have factor_2_27 : (67 : ZMod 26771144401) ^ 167319652 = 25235557912 := by
        calc
          (67 : ZMod 26771144401) ^ 167319652 = (67 : ZMod 26771144401) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 83659826 * (67 : ZMod 26771144401) ^ 83659826 := by rw [pow_add]
          _ = 25235557912 := by rw [factor_2_26]; decide
      have factor_2_28 : (67 : ZMod 26771144401) ^ 334639305 = 3531370778 := by
        calc
          (67 : ZMod 26771144401) ^ 334639305 = (67 : ZMod 26771144401) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 167319652 * (67 : ZMod 26771144401) ^ 167319652) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 3531370778 := by rw [factor_2_27]; decide
      have factor_2_29 : (67 : ZMod 26771144401) ^ 669278610 = 4231334000 := by
        calc
          (67 : ZMod 26771144401) ^ 669278610 = (67 : ZMod 26771144401) ^ (334639305 + 334639305) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 334639305 * (67 : ZMod 26771144401) ^ 334639305 := by rw [pow_add]
          _ = 4231334000 := by rw [factor_2_28]; decide
      have factor_2_30 : (67 : ZMod 26771144401) ^ 1338557220 = 12238470022 := by
        calc
          (67 : ZMod 26771144401) ^ 1338557220 = (67 : ZMod 26771144401) ^ (669278610 + 669278610) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 669278610 * (67 : ZMod 26771144401) ^ 669278610 := by rw [pow_add]
          _ = 12238470022 := by rw [factor_2_29]; decide
      have factor_2_31 : (67 : ZMod 26771144401) ^ 2677114440 = 24787966207 := by
        calc
          (67 : ZMod 26771144401) ^ 2677114440 = (67 : ZMod 26771144401) ^ (1338557220 + 1338557220) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1338557220 * (67 : ZMod 26771144401) ^ 1338557220 := by rw [pow_add]
          _ = 24787966207 := by rw [factor_2_30]; decide
      have factor_2_32 : (67 : ZMod 26771144401) ^ 5354228880 = 22161201084 := by
        calc
          (67 : ZMod 26771144401) ^ 5354228880 = (67 : ZMod 26771144401) ^ (2677114440 + 2677114440) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2677114440 * (67 : ZMod 26771144401) ^ 2677114440 := by rw [pow_add]
          _ = 22161201084 := by rw [factor_2_31]; decide
      change (67 : ZMod 26771144401) ^ 5354228880 ≠ 1
      rw [factor_2_32]
      decide
    ·
      have factor_3_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have factor_3_1 : (67 : ZMod 26771144401) ^ 3 = 300763 := by
        calc
          (67 : ZMod 26771144401) ^ 3 = (67 : ZMod 26771144401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 300763 := by rw [factor_3_0]; decide
      have factor_3_2 : (67 : ZMod 26771144401) ^ 7 = 10432970697 := by
        calc
          (67 : ZMod 26771144401) ^ 7 = (67 : ZMod 26771144401) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 3 * (67 : ZMod 26771144401) ^ 3) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10432970697 := by rw [factor_3_1]; decide
      have factor_3_3 : (67 : ZMod 26771144401) ^ 14 = 18184830271 := by
        calc
          (67 : ZMod 26771144401) ^ 14 = (67 : ZMod 26771144401) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 7 * (67 : ZMod 26771144401) ^ 7 := by rw [pow_add]
          _ = 18184830271 := by rw [factor_3_2]; decide
      have factor_3_4 : (67 : ZMod 26771144401) ^ 28 = 4318994770 := by
        calc
          (67 : ZMod 26771144401) ^ 28 = (67 : ZMod 26771144401) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 14 * (67 : ZMod 26771144401) ^ 14 := by rw [pow_add]
          _ = 4318994770 := by rw [factor_3_3]; decide
      have factor_3_5 : (67 : ZMod 26771144401) ^ 56 = 7752064099 := by
        calc
          (67 : ZMod 26771144401) ^ 56 = (67 : ZMod 26771144401) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 28 * (67 : ZMod 26771144401) ^ 28 := by rw [pow_add]
          _ = 7752064099 := by rw [factor_3_4]; decide
      have factor_3_6 : (67 : ZMod 26771144401) ^ 113 = 2275932242 := by
        calc
          (67 : ZMod 26771144401) ^ 113 = (67 : ZMod 26771144401) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 56 * (67 : ZMod 26771144401) ^ 56) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 2275932242 := by rw [factor_3_5]; decide
      have factor_3_7 : (67 : ZMod 26771144401) ^ 227 = 9798576507 := by
        calc
          (67 : ZMod 26771144401) ^ 227 = (67 : ZMod 26771144401) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 113 * (67 : ZMod 26771144401) ^ 113) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 9798576507 := by rw [factor_3_6]; decide
      have factor_3_8 : (67 : ZMod 26771144401) ^ 455 = 4302154487 := by
        calc
          (67 : ZMod 26771144401) ^ 455 = (67 : ZMod 26771144401) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 227 * (67 : ZMod 26771144401) ^ 227) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4302154487 := by rw [factor_3_7]; decide
      have factor_3_9 : (67 : ZMod 26771144401) ^ 911 = 5908756737 := by
        calc
          (67 : ZMod 26771144401) ^ 911 = (67 : ZMod 26771144401) ^ (455 + 455 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 455 * (67 : ZMod 26771144401) ^ 455) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 5908756737 := by rw [factor_3_8]; decide
      have factor_3_10 : (67 : ZMod 26771144401) ^ 1823 = 8728090897 := by
        calc
          (67 : ZMod 26771144401) ^ 1823 = (67 : ZMod 26771144401) ^ (911 + 911 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 911 * (67 : ZMod 26771144401) ^ 911) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 8728090897 := by rw [factor_3_9]; decide
      have factor_3_11 : (67 : ZMod 26771144401) ^ 3647 = 2267554378 := by
        calc
          (67 : ZMod 26771144401) ^ 3647 = (67 : ZMod 26771144401) ^ (1823 + 1823 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1823 * (67 : ZMod 26771144401) ^ 1823) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 2267554378 := by rw [factor_3_10]; decide
      have factor_3_12 : (67 : ZMod 26771144401) ^ 7294 = 9440728972 := by
        calc
          (67 : ZMod 26771144401) ^ 7294 = (67 : ZMod 26771144401) ^ (3647 + 3647) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 3647 * (67 : ZMod 26771144401) ^ 3647 := by rw [pow_add]
          _ = 9440728972 := by rw [factor_3_11]; decide
      have factor_3_13 : (67 : ZMod 26771144401) ^ 14589 = 16155548228 := by
        calc
          (67 : ZMod 26771144401) ^ 14589 = (67 : ZMod 26771144401) ^ (7294 + 7294 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 7294 * (67 : ZMod 26771144401) ^ 7294) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 16155548228 := by rw [factor_3_12]; decide
      have factor_3_14 : (67 : ZMod 26771144401) ^ 29178 = 745371984 := by
        calc
          (67 : ZMod 26771144401) ^ 29178 = (67 : ZMod 26771144401) ^ (14589 + 14589) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 14589 * (67 : ZMod 26771144401) ^ 14589 := by rw [pow_add]
          _ = 745371984 := by rw [factor_3_13]; decide
      have factor_3_15 : (67 : ZMod 26771144401) ^ 58356 = 3240839737 := by
        calc
          (67 : ZMod 26771144401) ^ 58356 = (67 : ZMod 26771144401) ^ (29178 + 29178) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 29178 * (67 : ZMod 26771144401) ^ 29178 := by rw [pow_add]
          _ = 3240839737 := by rw [factor_3_14]; decide
      have factor_3_16 : (67 : ZMod 26771144401) ^ 116712 = 20472278991 := by
        calc
          (67 : ZMod 26771144401) ^ 116712 = (67 : ZMod 26771144401) ^ (58356 + 58356) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 58356 * (67 : ZMod 26771144401) ^ 58356 := by rw [pow_add]
          _ = 20472278991 := by rw [factor_3_15]; decide
      have factor_3_17 : (67 : ZMod 26771144401) ^ 233425 = 10753118730 := by
        calc
          (67 : ZMod 26771144401) ^ 233425 = (67 : ZMod 26771144401) ^ (116712 + 116712 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 116712 * (67 : ZMod 26771144401) ^ 116712) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10753118730 := by rw [factor_3_16]; decide
      have factor_3_18 : (67 : ZMod 26771144401) ^ 466851 = 14959468871 := by
        calc
          (67 : ZMod 26771144401) ^ 466851 = (67 : ZMod 26771144401) ^ (233425 + 233425 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 233425 * (67 : ZMod 26771144401) ^ 233425) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 14959468871 := by rw [factor_3_17]; decide
      have factor_3_19 : (67 : ZMod 26771144401) ^ 933703 = 8546351417 := by
        calc
          (67 : ZMod 26771144401) ^ 933703 = (67 : ZMod 26771144401) ^ (466851 + 466851 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 466851 * (67 : ZMod 26771144401) ^ 466851) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 8546351417 := by rw [factor_3_18]; decide
      have factor_3_20 : (67 : ZMod 26771144401) ^ 1867406 = 23125149802 := by
        calc
          (67 : ZMod 26771144401) ^ 1867406 = (67 : ZMod 26771144401) ^ (933703 + 933703) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 933703 * (67 : ZMod 26771144401) ^ 933703 := by rw [pow_add]
          _ = 23125149802 := by rw [factor_3_19]; decide
      have factor_3_21 : (67 : ZMod 26771144401) ^ 3734813 = 22397546134 := by
        calc
          (67 : ZMod 26771144401) ^ 3734813 = (67 : ZMod 26771144401) ^ (1867406 + 1867406 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1867406 * (67 : ZMod 26771144401) ^ 1867406) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22397546134 := by rw [factor_3_20]; decide
      have factor_3_22 : (67 : ZMod 26771144401) ^ 7469627 = 2479364325 := by
        calc
          (67 : ZMod 26771144401) ^ 7469627 = (67 : ZMod 26771144401) ^ (3734813 + 3734813 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 3734813 * (67 : ZMod 26771144401) ^ 3734813) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 2479364325 := by rw [factor_3_21]; decide
      have factor_3_23 : (67 : ZMod 26771144401) ^ 14939254 = 15247211886 := by
        calc
          (67 : ZMod 26771144401) ^ 14939254 = (67 : ZMod 26771144401) ^ (7469627 + 7469627) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 7469627 * (67 : ZMod 26771144401) ^ 7469627 := by rw [pow_add]
          _ = 15247211886 := by rw [factor_3_22]; decide
      have factor_3_24 : (67 : ZMod 26771144401) ^ 29878509 = 22033239219 := by
        calc
          (67 : ZMod 26771144401) ^ 29878509 = (67 : ZMod 26771144401) ^ (14939254 + 14939254 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 14939254 * (67 : ZMod 26771144401) ^ 14939254) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22033239219 := by rw [factor_3_23]; decide
      have factor_3_25 : (67 : ZMod 26771144401) ^ 59757018 = 10079826260 := by
        calc
          (67 : ZMod 26771144401) ^ 59757018 = (67 : ZMod 26771144401) ^ (29878509 + 29878509) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 29878509 * (67 : ZMod 26771144401) ^ 29878509 := by rw [pow_add]
          _ = 10079826260 := by rw [factor_3_24]; decide
      have factor_3_26 : (67 : ZMod 26771144401) ^ 119514037 = 18890200068 := by
        calc
          (67 : ZMod 26771144401) ^ 119514037 = (67 : ZMod 26771144401) ^ (59757018 + 59757018 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 59757018 * (67 : ZMod 26771144401) ^ 59757018) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 18890200068 := by rw [factor_3_25]; decide
      have factor_3_27 : (67 : ZMod 26771144401) ^ 239028075 = 19490593924 := by
        calc
          (67 : ZMod 26771144401) ^ 239028075 = (67 : ZMod 26771144401) ^ (119514037 + 119514037 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 119514037 * (67 : ZMod 26771144401) ^ 119514037) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 19490593924 := by rw [factor_3_26]; decide
      have factor_3_28 : (67 : ZMod 26771144401) ^ 478056150 = 26380918364 := by
        calc
          (67 : ZMod 26771144401) ^ 478056150 = (67 : ZMod 26771144401) ^ (239028075 + 239028075) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 239028075 * (67 : ZMod 26771144401) ^ 239028075 := by rw [pow_add]
          _ = 26380918364 := by rw [factor_3_27]; decide
      have factor_3_29 : (67 : ZMod 26771144401) ^ 956112300 = 2450574091 := by
        calc
          (67 : ZMod 26771144401) ^ 956112300 = (67 : ZMod 26771144401) ^ (478056150 + 478056150) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 478056150 * (67 : ZMod 26771144401) ^ 478056150 := by rw [pow_add]
          _ = 2450574091 := by rw [factor_3_28]; decide
      have factor_3_30 : (67 : ZMod 26771144401) ^ 1912224600 = 10099850698 := by
        calc
          (67 : ZMod 26771144401) ^ 1912224600 = (67 : ZMod 26771144401) ^ (956112300 + 956112300) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 956112300 * (67 : ZMod 26771144401) ^ 956112300 := by rw [pow_add]
          _ = 10099850698 := by rw [factor_3_29]; decide
      have factor_3_31 : (67 : ZMod 26771144401) ^ 3824449200 = 7264169062 := by
        calc
          (67 : ZMod 26771144401) ^ 3824449200 = (67 : ZMod 26771144401) ^ (1912224600 + 1912224600) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1912224600 * (67 : ZMod 26771144401) ^ 1912224600 := by rw [pow_add]
          _ = 7264169062 := by rw [factor_3_30]; decide
      change (67 : ZMod 26771144401) ^ 3824449200 ≠ 1
      rw [factor_3_31]
      decide
    ·
      have factor_4_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have factor_4_1 : (67 : ZMod 26771144401) ^ 2 = 4489 := by
        calc
          (67 : ZMod 26771144401) ^ 2 = (67 : ZMod 26771144401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1 := by rw [pow_add]
          _ = 4489 := by rw [factor_4_0]; decide
      have factor_4_2 : (67 : ZMod 26771144401) ^ 4 = 20151121 := by
        calc
          (67 : ZMod 26771144401) ^ 4 = (67 : ZMod 26771144401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2 * (67 : ZMod 26771144401) ^ 2 := by rw [pow_add]
          _ = 20151121 := by rw [factor_4_1]; decide
      have factor_4_3 : (67 : ZMod 26771144401) ^ 9 = 10873901484 := by
        calc
          (67 : ZMod 26771144401) ^ 9 = (67 : ZMod 26771144401) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 4 * (67 : ZMod 26771144401) ^ 4) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10873901484 := by rw [factor_4_2]; decide
      have factor_4_4 : (67 : ZMod 26771144401) ^ 18 = 5579564543 := by
        calc
          (67 : ZMod 26771144401) ^ 18 = (67 : ZMod 26771144401) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 9 * (67 : ZMod 26771144401) ^ 9 := by rw [pow_add]
          _ = 5579564543 := by rw [factor_4_3]; decide
      have factor_4_5 : (67 : ZMod 26771144401) ^ 36 = 4906131733 := by
        calc
          (67 : ZMod 26771144401) ^ 36 = (67 : ZMod 26771144401) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 18 * (67 : ZMod 26771144401) ^ 18 := by rw [pow_add]
          _ = 4906131733 := by rw [factor_4_4]; decide
      have factor_4_6 : (67 : ZMod 26771144401) ^ 72 = 5455373693 := by
        calc
          (67 : ZMod 26771144401) ^ 72 = (67 : ZMod 26771144401) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 36 * (67 : ZMod 26771144401) ^ 36 := by rw [pow_add]
          _ = 5455373693 := by rw [factor_4_5]; decide
      have factor_4_7 : (67 : ZMod 26771144401) ^ 145 = 17865572656 := by
        calc
          (67 : ZMod 26771144401) ^ 145 = (67 : ZMod 26771144401) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 72 * (67 : ZMod 26771144401) ^ 72) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 17865572656 := by rw [factor_4_6]; decide
      have factor_4_8 : (67 : ZMod 26771144401) ^ 290 = 16261846500 := by
        calc
          (67 : ZMod 26771144401) ^ 290 = (67 : ZMod 26771144401) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 145 * (67 : ZMod 26771144401) ^ 145 := by rw [pow_add]
          _ = 16261846500 := by rw [factor_4_7]; decide
      have factor_4_9 : (67 : ZMod 26771144401) ^ 580 = 3762350565 := by
        calc
          (67 : ZMod 26771144401) ^ 580 = (67 : ZMod 26771144401) ^ (290 + 290) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 290 * (67 : ZMod 26771144401) ^ 290 := by rw [pow_add]
          _ = 3762350565 := by rw [factor_4_8]; decide
      have factor_4_10 : (67 : ZMod 26771144401) ^ 1160 = 5742810562 := by
        calc
          (67 : ZMod 26771144401) ^ 1160 = (67 : ZMod 26771144401) ^ (580 + 580) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 580 * (67 : ZMod 26771144401) ^ 580 := by rw [pow_add]
          _ = 5742810562 := by rw [factor_4_9]; decide
      have factor_4_11 : (67 : ZMod 26771144401) ^ 2320 = 10738001154 := by
        calc
          (67 : ZMod 26771144401) ^ 2320 = (67 : ZMod 26771144401) ^ (1160 + 1160) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1160 * (67 : ZMod 26771144401) ^ 1160 := by rw [pow_add]
          _ = 10738001154 := by rw [factor_4_10]; decide
      have factor_4_12 : (67 : ZMod 26771144401) ^ 4641 = 23317535915 := by
        calc
          (67 : ZMod 26771144401) ^ 4641 = (67 : ZMod 26771144401) ^ (2320 + 2320 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 2320 * (67 : ZMod 26771144401) ^ 2320) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 23317535915 := by rw [factor_4_11]; decide
      have factor_4_13 : (67 : ZMod 26771144401) ^ 9283 = 10443789937 := by
        calc
          (67 : ZMod 26771144401) ^ 9283 = (67 : ZMod 26771144401) ^ (4641 + 4641 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 4641 * (67 : ZMod 26771144401) ^ 4641) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10443789937 := by rw [factor_4_12]; decide
      have factor_4_14 : (67 : ZMod 26771144401) ^ 18567 = 10109348279 := by
        calc
          (67 : ZMod 26771144401) ^ 18567 = (67 : ZMod 26771144401) ^ (9283 + 9283 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 9283 * (67 : ZMod 26771144401) ^ 9283) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10109348279 := by rw [factor_4_13]; decide
      have factor_4_15 : (67 : ZMod 26771144401) ^ 37135 = 21380285947 := by
        calc
          (67 : ZMod 26771144401) ^ 37135 = (67 : ZMod 26771144401) ^ (18567 + 18567 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 18567 * (67 : ZMod 26771144401) ^ 18567) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 21380285947 := by rw [factor_4_14]; decide
      have factor_4_16 : (67 : ZMod 26771144401) ^ 74271 = 5346111470 := by
        calc
          (67 : ZMod 26771144401) ^ 74271 = (67 : ZMod 26771144401) ^ (37135 + 37135 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 37135 * (67 : ZMod 26771144401) ^ 37135) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 5346111470 := by rw [factor_4_15]; decide
      have factor_4_17 : (67 : ZMod 26771144401) ^ 148543 = 20025675391 := by
        calc
          (67 : ZMod 26771144401) ^ 148543 = (67 : ZMod 26771144401) ^ (74271 + 74271 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 74271 * (67 : ZMod 26771144401) ^ 74271) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 20025675391 := by rw [factor_4_16]; decide
      have factor_4_18 : (67 : ZMod 26771144401) ^ 297087 = 6612725043 := by
        calc
          (67 : ZMod 26771144401) ^ 297087 = (67 : ZMod 26771144401) ^ (148543 + 148543 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 148543 * (67 : ZMod 26771144401) ^ 148543) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 6612725043 := by rw [factor_4_17]; decide
      have factor_4_19 : (67 : ZMod 26771144401) ^ 594174 = 23038720825 := by
        calc
          (67 : ZMod 26771144401) ^ 594174 = (67 : ZMod 26771144401) ^ (297087 + 297087) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 297087 * (67 : ZMod 26771144401) ^ 297087 := by rw [pow_add]
          _ = 23038720825 := by rw [factor_4_18]; decide
      have factor_4_20 : (67 : ZMod 26771144401) ^ 1188349 = 21124683016 := by
        calc
          (67 : ZMod 26771144401) ^ 1188349 = (67 : ZMod 26771144401) ^ (594174 + 594174 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 594174 * (67 : ZMod 26771144401) ^ 594174) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 21124683016 := by rw [factor_4_19]; decide
      have factor_4_21 : (67 : ZMod 26771144401) ^ 2376699 = 15249886037 := by
        calc
          (67 : ZMod 26771144401) ^ 2376699 = (67 : ZMod 26771144401) ^ (1188349 + 1188349 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1188349 * (67 : ZMod 26771144401) ^ 1188349) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 15249886037 := by rw [factor_4_20]; decide
      have factor_4_22 : (67 : ZMod 26771144401) ^ 4753399 = 15174339038 := by
        calc
          (67 : ZMod 26771144401) ^ 4753399 = (67 : ZMod 26771144401) ^ (2376699 + 2376699 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 2376699 * (67 : ZMod 26771144401) ^ 2376699) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 15174339038 := by rw [factor_4_21]; decide
      have factor_4_23 : (67 : ZMod 26771144401) ^ 9506798 = 15006611321 := by
        calc
          (67 : ZMod 26771144401) ^ 9506798 = (67 : ZMod 26771144401) ^ (4753399 + 4753399) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 4753399 * (67 : ZMod 26771144401) ^ 4753399 := by rw [pow_add]
          _ = 15006611321 := by rw [factor_4_22]; decide
      have factor_4_24 : (67 : ZMod 26771144401) ^ 19013596 = 18136669497 := by
        calc
          (67 : ZMod 26771144401) ^ 19013596 = (67 : ZMod 26771144401) ^ (9506798 + 9506798) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 9506798 * (67 : ZMod 26771144401) ^ 9506798 := by rw [pow_add]
          _ = 18136669497 := by rw [factor_4_23]; decide
      have factor_4_25 : (67 : ZMod 26771144401) ^ 38027193 = 10012511973 := by
        calc
          (67 : ZMod 26771144401) ^ 38027193 = (67 : ZMod 26771144401) ^ (19013596 + 19013596 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 19013596 * (67 : ZMod 26771144401) ^ 19013596) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10012511973 := by rw [factor_4_24]; decide
      have factor_4_26 : (67 : ZMod 26771144401) ^ 76054387 = 5983113791 := by
        calc
          (67 : ZMod 26771144401) ^ 76054387 = (67 : ZMod 26771144401) ^ (38027193 + 38027193 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 38027193 * (67 : ZMod 26771144401) ^ 38027193) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 5983113791 := by rw [factor_4_25]; decide
      have factor_4_27 : (67 : ZMod 26771144401) ^ 152108775 = 15718482920 := by
        calc
          (67 : ZMod 26771144401) ^ 152108775 = (67 : ZMod 26771144401) ^ (76054387 + 76054387 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 76054387 * (67 : ZMod 26771144401) ^ 76054387) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 15718482920 := by rw [factor_4_26]; decide
      have factor_4_28 : (67 : ZMod 26771144401) ^ 304217550 = 10210046162 := by
        calc
          (67 : ZMod 26771144401) ^ 304217550 = (67 : ZMod 26771144401) ^ (152108775 + 152108775) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 152108775 * (67 : ZMod 26771144401) ^ 152108775 := by rw [pow_add]
          _ = 10210046162 := by rw [factor_4_27]; decide
      have factor_4_29 : (67 : ZMod 26771144401) ^ 608435100 = 26122941645 := by
        calc
          (67 : ZMod 26771144401) ^ 608435100 = (67 : ZMod 26771144401) ^ (304217550 + 304217550) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 304217550 * (67 : ZMod 26771144401) ^ 304217550 := by rw [pow_add]
          _ = 26122941645 := by rw [factor_4_28]; decide
      have factor_4_30 : (67 : ZMod 26771144401) ^ 1216870200 = 19502379172 := by
        calc
          (67 : ZMod 26771144401) ^ 1216870200 = (67 : ZMod 26771144401) ^ (608435100 + 608435100) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 608435100 * (67 : ZMod 26771144401) ^ 608435100 := by rw [pow_add]
          _ = 19502379172 := by rw [factor_4_29]; decide
      have factor_4_31 : (67 : ZMod 26771144401) ^ 2433740400 = 11692565805 := by
        calc
          (67 : ZMod 26771144401) ^ 2433740400 = (67 : ZMod 26771144401) ^ (1216870200 + 1216870200) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1216870200 * (67 : ZMod 26771144401) ^ 1216870200 := by rw [pow_add]
          _ = 11692565805 := by rw [factor_4_30]; decide
      change (67 : ZMod 26771144401) ^ 2433740400 ≠ 1
      rw [factor_4_31]
      decide
    ·
      have factor_5_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have factor_5_1 : (67 : ZMod 26771144401) ^ 3 = 300763 := by
        calc
          (67 : ZMod 26771144401) ^ 3 = (67 : ZMod 26771144401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 300763 := by rw [factor_5_0]; decide
      have factor_5_2 : (67 : ZMod 26771144401) ^ 7 = 10432970697 := by
        calc
          (67 : ZMod 26771144401) ^ 7 = (67 : ZMod 26771144401) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 3 * (67 : ZMod 26771144401) ^ 3) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 10432970697 := by rw [factor_5_1]; decide
      have factor_5_3 : (67 : ZMod 26771144401) ^ 15 = 13682130112 := by
        calc
          (67 : ZMod 26771144401) ^ 15 = (67 : ZMod 26771144401) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 7 * (67 : ZMod 26771144401) ^ 7) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 13682130112 := by rw [factor_5_2]; decide
      have factor_5_4 : (67 : ZMod 26771144401) ^ 30 = 5658976206 := by
        calc
          (67 : ZMod 26771144401) ^ 30 = (67 : ZMod 26771144401) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 15 * (67 : ZMod 26771144401) ^ 15 := by rw [pow_add]
          _ = 5658976206 := by rw [factor_5_3]; decide
      have factor_5_5 : (67 : ZMod 26771144401) ^ 61 = 18641531500 := by
        calc
          (67 : ZMod 26771144401) ^ 61 = (67 : ZMod 26771144401) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 30 * (67 : ZMod 26771144401) ^ 30) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 18641531500 := by rw [factor_5_4]; decide
      have factor_5_6 : (67 : ZMod 26771144401) ^ 122 = 10164764336 := by
        calc
          (67 : ZMod 26771144401) ^ 122 = (67 : ZMod 26771144401) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 61 * (67 : ZMod 26771144401) ^ 61 := by rw [pow_add]
          _ = 10164764336 := by rw [factor_5_5]; decide
      have factor_5_7 : (67 : ZMod 26771144401) ^ 245 = 1991977905 := by
        calc
          (67 : ZMod 26771144401) ^ 245 = (67 : ZMod 26771144401) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 122 * (67 : ZMod 26771144401) ^ 122) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 1991977905 := by rw [factor_5_6]; decide
      have factor_5_8 : (67 : ZMod 26771144401) ^ 490 = 25663310234 := by
        calc
          (67 : ZMod 26771144401) ^ 490 = (67 : ZMod 26771144401) ^ (245 + 245) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 245 * (67 : ZMod 26771144401) ^ 245 := by rw [pow_add]
          _ = 25663310234 := by rw [factor_5_7]; decide
      have factor_5_9 : (67 : ZMod 26771144401) ^ 981 = 17815038469 := by
        calc
          (67 : ZMod 26771144401) ^ 981 = (67 : ZMod 26771144401) ^ (490 + 490 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 490 * (67 : ZMod 26771144401) ^ 490) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 17815038469 := by rw [factor_5_8]; decide
      have factor_5_10 : (67 : ZMod 26771144401) ^ 1963 = 7358383329 := by
        calc
          (67 : ZMod 26771144401) ^ 1963 = (67 : ZMod 26771144401) ^ (981 + 981 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 981 * (67 : ZMod 26771144401) ^ 981) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 7358383329 := by rw [factor_5_9]; decide
      have factor_5_11 : (67 : ZMod 26771144401) ^ 3927 = 20690075243 := by
        calc
          (67 : ZMod 26771144401) ^ 3927 = (67 : ZMod 26771144401) ^ (1963 + 1963 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1963 * (67 : ZMod 26771144401) ^ 1963) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 20690075243 := by rw [factor_5_10]; decide
      have factor_5_12 : (67 : ZMod 26771144401) ^ 7855 = 23396032598 := by
        calc
          (67 : ZMod 26771144401) ^ 7855 = (67 : ZMod 26771144401) ^ (3927 + 3927 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 3927 * (67 : ZMod 26771144401) ^ 3927) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 23396032598 := by rw [factor_5_11]; decide
      have factor_5_13 : (67 : ZMod 26771144401) ^ 15711 = 22266525559 := by
        calc
          (67 : ZMod 26771144401) ^ 15711 = (67 : ZMod 26771144401) ^ (7855 + 7855 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 7855 * (67 : ZMod 26771144401) ^ 7855) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22266525559 := by rw [factor_5_12]; decide
      have factor_5_14 : (67 : ZMod 26771144401) ^ 31422 = 17459145548 := by
        calc
          (67 : ZMod 26771144401) ^ 31422 = (67 : ZMod 26771144401) ^ (15711 + 15711) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 15711 * (67 : ZMod 26771144401) ^ 15711 := by rw [pow_add]
          _ = 17459145548 := by rw [factor_5_13]; decide
      have factor_5_15 : (67 : ZMod 26771144401) ^ 62845 = 2737735921 := by
        calc
          (67 : ZMod 26771144401) ^ 62845 = (67 : ZMod 26771144401) ^ (31422 + 31422 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 31422 * (67 : ZMod 26771144401) ^ 31422) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 2737735921 := by rw [factor_5_14]; decide
      have factor_5_16 : (67 : ZMod 26771144401) ^ 125690 = 13727668028 := by
        calc
          (67 : ZMod 26771144401) ^ 125690 = (67 : ZMod 26771144401) ^ (62845 + 62845) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 62845 * (67 : ZMod 26771144401) ^ 62845 := by rw [pow_add]
          _ = 13727668028 := by rw [factor_5_15]; decide
      have factor_5_17 : (67 : ZMod 26771144401) ^ 251381 = 13536305727 := by
        calc
          (67 : ZMod 26771144401) ^ 251381 = (67 : ZMod 26771144401) ^ (125690 + 125690 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 125690 * (67 : ZMod 26771144401) ^ 125690) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 13536305727 := by rw [factor_5_16]; decide
      have factor_5_18 : (67 : ZMod 26771144401) ^ 502763 = 11911477337 := by
        calc
          (67 : ZMod 26771144401) ^ 502763 = (67 : ZMod 26771144401) ^ (251381 + 251381 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 251381 * (67 : ZMod 26771144401) ^ 251381) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 11911477337 := by rw [factor_5_17]; decide
      have factor_5_19 : (67 : ZMod 26771144401) ^ 1005526 = 15800766504 := by
        calc
          (67 : ZMod 26771144401) ^ 1005526 = (67 : ZMod 26771144401) ^ (502763 + 502763) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 502763 * (67 : ZMod 26771144401) ^ 502763 := by rw [pow_add]
          _ = 15800766504 := by rw [factor_5_18]; decide
      have factor_5_20 : (67 : ZMod 26771144401) ^ 2011053 = 13861479649 := by
        calc
          (67 : ZMod 26771144401) ^ 2011053 = (67 : ZMod 26771144401) ^ (1005526 + 1005526 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1005526 * (67 : ZMod 26771144401) ^ 1005526) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 13861479649 := by rw [factor_5_19]; decide
      have factor_5_21 : (67 : ZMod 26771144401) ^ 4022107 = 22492284246 := by
        calc
          (67 : ZMod 26771144401) ^ 4022107 = (67 : ZMod 26771144401) ^ (2011053 + 2011053 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 2011053 * (67 : ZMod 26771144401) ^ 2011053) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22492284246 := by rw [factor_5_20]; decide
      have factor_5_22 : (67 : ZMod 26771144401) ^ 8044214 = 2158594508 := by
        calc
          (67 : ZMod 26771144401) ^ 8044214 = (67 : ZMod 26771144401) ^ (4022107 + 4022107) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 4022107 * (67 : ZMod 26771144401) ^ 4022107 := by rw [pow_add]
          _ = 2158594508 := by rw [factor_5_21]; decide
      have factor_5_23 : (67 : ZMod 26771144401) ^ 16088428 = 11306987995 := by
        calc
          (67 : ZMod 26771144401) ^ 16088428 = (67 : ZMod 26771144401) ^ (8044214 + 8044214) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 8044214 * (67 : ZMod 26771144401) ^ 8044214 := by rw [pow_add]
          _ = 11306987995 := by rw [factor_5_22]; decide
      have factor_5_24 : (67 : ZMod 26771144401) ^ 32176856 = 20620089220 := by
        calc
          (67 : ZMod 26771144401) ^ 32176856 = (67 : ZMod 26771144401) ^ (16088428 + 16088428) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 16088428 * (67 : ZMod 26771144401) ^ 16088428 := by rw [pow_add]
          _ = 20620089220 := by rw [factor_5_23]; decide
      have factor_5_25 : (67 : ZMod 26771144401) ^ 64353712 = 21306797431 := by
        calc
          (67 : ZMod 26771144401) ^ 64353712 = (67 : ZMod 26771144401) ^ (32176856 + 32176856) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 32176856 * (67 : ZMod 26771144401) ^ 32176856 := by rw [pow_add]
          _ = 21306797431 := by rw [factor_5_24]; decide
      have factor_5_26 : (67 : ZMod 26771144401) ^ 128707425 = 25225916840 := by
        calc
          (67 : ZMod 26771144401) ^ 128707425 = (67 : ZMod 26771144401) ^ (64353712 + 64353712 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 64353712 * (67 : ZMod 26771144401) ^ 64353712) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 25225916840 := by rw [factor_5_25]; decide
      have factor_5_27 : (67 : ZMod 26771144401) ^ 257414850 = 21138823554 := by
        calc
          (67 : ZMod 26771144401) ^ 257414850 = (67 : ZMod 26771144401) ^ (128707425 + 128707425) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 128707425 * (67 : ZMod 26771144401) ^ 128707425 := by rw [pow_add]
          _ = 21138823554 := by rw [factor_5_26]; decide
      have factor_5_28 : (67 : ZMod 26771144401) ^ 514829700 = 18956373297 := by
        calc
          (67 : ZMod 26771144401) ^ 514829700 = (67 : ZMod 26771144401) ^ (257414850 + 257414850) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 257414850 * (67 : ZMod 26771144401) ^ 257414850 := by rw [pow_add]
          _ = 18956373297 := by rw [factor_5_27]; decide
      have factor_5_29 : (67 : ZMod 26771144401) ^ 1029659400 = 6300997532 := by
        calc
          (67 : ZMod 26771144401) ^ 1029659400 = (67 : ZMod 26771144401) ^ (514829700 + 514829700) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 514829700 * (67 : ZMod 26771144401) ^ 514829700 := by rw [pow_add]
          _ = 6300997532 := by rw [factor_5_28]; decide
      have factor_5_30 : (67 : ZMod 26771144401) ^ 2059318800 = 7692142262 := by
        calc
          (67 : ZMod 26771144401) ^ 2059318800 = (67 : ZMod 26771144401) ^ (1029659400 + 1029659400) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1029659400 * (67 : ZMod 26771144401) ^ 1029659400 := by rw [pow_add]
          _ = 7692142262 := by rw [factor_5_29]; decide
      change (67 : ZMod 26771144401) ^ 2059318800 ≠ 1
      rw [factor_5_30]
      decide
    ·
      have factor_6_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have factor_6_1 : (67 : ZMod 26771144401) ^ 2 = 4489 := by
        calc
          (67 : ZMod 26771144401) ^ 2 = (67 : ZMod 26771144401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1 := by rw [pow_add]
          _ = 4489 := by rw [factor_6_0]; decide
      have factor_6_2 : (67 : ZMod 26771144401) ^ 5 = 1350125107 := by
        calc
          (67 : ZMod 26771144401) ^ 5 = (67 : ZMod 26771144401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 2 * (67 : ZMod 26771144401) ^ 2) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 1350125107 := by rw [factor_6_1]; decide
      have factor_6_3 : (67 : ZMod 26771144401) ^ 11 = 9147518653 := by
        calc
          (67 : ZMod 26771144401) ^ 11 = (67 : ZMod 26771144401) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 5 * (67 : ZMod 26771144401) ^ 5) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 9147518653 := by rw [factor_6_2]; decide
      have factor_6_4 : (67 : ZMod 26771144401) ^ 23 = 19141455129 := by
        calc
          (67 : ZMod 26771144401) ^ 23 = (67 : ZMod 26771144401) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 11 * (67 : ZMod 26771144401) ^ 11) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 19141455129 := by rw [factor_6_3]; decide
      have factor_6_5 : (67 : ZMod 26771144401) ^ 46 = 9389716903 := by
        calc
          (67 : ZMod 26771144401) ^ 46 = (67 : ZMod 26771144401) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 23 * (67 : ZMod 26771144401) ^ 23 := by rw [pow_add]
          _ = 9389716903 := by rw [factor_6_4]; decide
      have factor_6_6 : (67 : ZMod 26771144401) ^ 93 = 5982831345 := by
        calc
          (67 : ZMod 26771144401) ^ 93 = (67 : ZMod 26771144401) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 46 * (67 : ZMod 26771144401) ^ 46) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 5982831345 := by rw [factor_6_5]; decide
      have factor_6_7 : (67 : ZMod 26771144401) ^ 187 = 593539408 := by
        calc
          (67 : ZMod 26771144401) ^ 187 = (67 : ZMod 26771144401) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 93 * (67 : ZMod 26771144401) ^ 93) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 593539408 := by rw [factor_6_6]; decide
      have factor_6_8 : (67 : ZMod 26771144401) ^ 375 = 13583805619 := by
        calc
          (67 : ZMod 26771144401) ^ 375 = (67 : ZMod 26771144401) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 187 * (67 : ZMod 26771144401) ^ 187) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 13583805619 := by rw [factor_6_7]; decide
      have factor_6_9 : (67 : ZMod 26771144401) ^ 750 = 2098947375 := by
        calc
          (67 : ZMod 26771144401) ^ 750 = (67 : ZMod 26771144401) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 375 * (67 : ZMod 26771144401) ^ 375 := by rw [pow_add]
          _ = 2098947375 := by rw [factor_6_8]; decide
      have factor_6_10 : (67 : ZMod 26771144401) ^ 1501 = 22641260150 := by
        calc
          (67 : ZMod 26771144401) ^ 1501 = (67 : ZMod 26771144401) ^ (750 + 750 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 750 * (67 : ZMod 26771144401) ^ 750) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22641260150 := by rw [factor_6_9]; decide
      have factor_6_11 : (67 : ZMod 26771144401) ^ 3003 = 22324177367 := by
        calc
          (67 : ZMod 26771144401) ^ 3003 = (67 : ZMod 26771144401) ^ (1501 + 1501 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1501 * (67 : ZMod 26771144401) ^ 1501) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22324177367 := by rw [factor_6_10]; decide
      have factor_6_12 : (67 : ZMod 26771144401) ^ 6007 = 20988493757 := by
        calc
          (67 : ZMod 26771144401) ^ 6007 = (67 : ZMod 26771144401) ^ (3003 + 3003 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 3003 * (67 : ZMod 26771144401) ^ 3003) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 20988493757 := by rw [factor_6_11]; decide
      have factor_6_13 : (67 : ZMod 26771144401) ^ 12014 = 7899958171 := by
        calc
          (67 : ZMod 26771144401) ^ 12014 = (67 : ZMod 26771144401) ^ (6007 + 6007) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 6007 * (67 : ZMod 26771144401) ^ 6007 := by rw [pow_add]
          _ = 7899958171 := by rw [factor_6_12]; decide
      have factor_6_14 : (67 : ZMod 26771144401) ^ 24029 = 2690413752 := by
        calc
          (67 : ZMod 26771144401) ^ 24029 = (67 : ZMod 26771144401) ^ (12014 + 12014 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 12014 * (67 : ZMod 26771144401) ^ 12014) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 2690413752 := by rw [factor_6_13]; decide
      have factor_6_15 : (67 : ZMod 26771144401) ^ 48058 = 5186702391 := by
        calc
          (67 : ZMod 26771144401) ^ 48058 = (67 : ZMod 26771144401) ^ (24029 + 24029) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 24029 * (67 : ZMod 26771144401) ^ 24029 := by rw [pow_add]
          _ = 5186702391 := by rw [factor_6_14]; decide
      have factor_6_16 : (67 : ZMod 26771144401) ^ 96116 = 6555667366 := by
        calc
          (67 : ZMod 26771144401) ^ 96116 = (67 : ZMod 26771144401) ^ (48058 + 48058) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 48058 * (67 : ZMod 26771144401) ^ 48058 := by rw [pow_add]
          _ = 6555667366 := by rw [factor_6_15]; decide
      have factor_6_17 : (67 : ZMod 26771144401) ^ 192233 = 18773661739 := by
        calc
          (67 : ZMod 26771144401) ^ 192233 = (67 : ZMod 26771144401) ^ (96116 + 96116 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 96116 * (67 : ZMod 26771144401) ^ 96116) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 18773661739 := by rw [factor_6_16]; decide
      have factor_6_18 : (67 : ZMod 26771144401) ^ 384466 = 19324073616 := by
        calc
          (67 : ZMod 26771144401) ^ 384466 = (67 : ZMod 26771144401) ^ (192233 + 192233) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 192233 * (67 : ZMod 26771144401) ^ 192233 := by rw [pow_add]
          _ = 19324073616 := by rw [factor_6_17]; decide
      have factor_6_19 : (67 : ZMod 26771144401) ^ 768932 = 3575583170 := by
        calc
          (67 : ZMod 26771144401) ^ 768932 = (67 : ZMod 26771144401) ^ (384466 + 384466) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 384466 * (67 : ZMod 26771144401) ^ 384466 := by rw [pow_add]
          _ = 3575583170 := by rw [factor_6_18]; decide
      have factor_6_20 : (67 : ZMod 26771144401) ^ 1537864 = 26555291323 := by
        calc
          (67 : ZMod 26771144401) ^ 1537864 = (67 : ZMod 26771144401) ^ (768932 + 768932) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 768932 * (67 : ZMod 26771144401) ^ 768932 := by rw [pow_add]
          _ = 26555291323 := by rw [factor_6_19]; decide
      have factor_6_21 : (67 : ZMod 26771144401) ^ 3075728 = 24795429283 := by
        calc
          (67 : ZMod 26771144401) ^ 3075728 = (67 : ZMod 26771144401) ^ (1537864 + 1537864) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1537864 * (67 : ZMod 26771144401) ^ 1537864 := by rw [pow_add]
          _ = 24795429283 := by rw [factor_6_20]; decide
      have factor_6_22 : (67 : ZMod 26771144401) ^ 6151457 = 8495880888 := by
        calc
          (67 : ZMod 26771144401) ^ 6151457 = (67 : ZMod 26771144401) ^ (3075728 + 3075728 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 3075728 * (67 : ZMod 26771144401) ^ 3075728) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 8495880888 := by rw [factor_6_21]; decide
      have factor_6_23 : (67 : ZMod 26771144401) ^ 12302915 = 15029371316 := by
        calc
          (67 : ZMod 26771144401) ^ 12302915 = (67 : ZMod 26771144401) ^ (6151457 + 6151457 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 6151457 * (67 : ZMod 26771144401) ^ 6151457) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 15029371316 := by rw [factor_6_22]; decide
      have factor_6_24 : (67 : ZMod 26771144401) ^ 24605831 = 22147632506 := by
        calc
          (67 : ZMod 26771144401) ^ 24605831 = (67 : ZMod 26771144401) ^ (12302915 + 12302915 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 12302915 * (67 : ZMod 26771144401) ^ 12302915) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22147632506 := by rw [factor_6_23]; decide
      have factor_6_25 : (67 : ZMod 26771144401) ^ 49211662 = 22077169962 := by
        calc
          (67 : ZMod 26771144401) ^ 49211662 = (67 : ZMod 26771144401) ^ (24605831 + 24605831) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 24605831 * (67 : ZMod 26771144401) ^ 24605831 := by rw [pow_add]
          _ = 22077169962 := by rw [factor_6_24]; decide
      have factor_6_26 : (67 : ZMod 26771144401) ^ 98423325 = 6598739822 := by
        calc
          (67 : ZMod 26771144401) ^ 98423325 = (67 : ZMod 26771144401) ^ (49211662 + 49211662 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 49211662 * (67 : ZMod 26771144401) ^ 49211662) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 6598739822 := by rw [factor_6_25]; decide
      have factor_6_27 : (67 : ZMod 26771144401) ^ 196846650 = 23321133117 := by
        calc
          (67 : ZMod 26771144401) ^ 196846650 = (67 : ZMod 26771144401) ^ (98423325 + 98423325) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 98423325 * (67 : ZMod 26771144401) ^ 98423325 := by rw [pow_add]
          _ = 23321133117 := by rw [factor_6_26]; decide
      have factor_6_28 : (67 : ZMod 26771144401) ^ 393693300 = 3191401510 := by
        calc
          (67 : ZMod 26771144401) ^ 393693300 = (67 : ZMod 26771144401) ^ (196846650 + 196846650) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 196846650 * (67 : ZMod 26771144401) ^ 196846650 := by rw [pow_add]
          _ = 3191401510 := by rw [factor_6_27]; decide
      have factor_6_29 : (67 : ZMod 26771144401) ^ 787386600 = 20177467931 := by
        calc
          (67 : ZMod 26771144401) ^ 787386600 = (67 : ZMod 26771144401) ^ (393693300 + 393693300) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 393693300 * (67 : ZMod 26771144401) ^ 393693300 := by rw [pow_add]
          _ = 20177467931 := by rw [factor_6_28]; decide
      have factor_6_30 : (67 : ZMod 26771144401) ^ 1574773200 = 9458346676 := by
        calc
          (67 : ZMod 26771144401) ^ 1574773200 = (67 : ZMod 26771144401) ^ (787386600 + 787386600) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 787386600 * (67 : ZMod 26771144401) ^ 787386600 := by rw [pow_add]
          _ = 9458346676 := by rw [factor_6_29]; decide
      change (67 : ZMod 26771144401) ^ 1574773200 ≠ 1
      rw [factor_6_30]
      decide
    ·
      have factor_7_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have factor_7_1 : (67 : ZMod 26771144401) ^ 2 = 4489 := by
        calc
          (67 : ZMod 26771144401) ^ 2 = (67 : ZMod 26771144401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1 := by rw [pow_add]
          _ = 4489 := by rw [factor_7_0]; decide
      have factor_7_2 : (67 : ZMod 26771144401) ^ 5 = 1350125107 := by
        calc
          (67 : ZMod 26771144401) ^ 5 = (67 : ZMod 26771144401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 2 * (67 : ZMod 26771144401) ^ 2) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 1350125107 := by rw [factor_7_1]; decide
      have factor_7_3 : (67 : ZMod 26771144401) ^ 10 = 5730500601 := by
        calc
          (67 : ZMod 26771144401) ^ 10 = (67 : ZMod 26771144401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 5 * (67 : ZMod 26771144401) ^ 5 := by rw [pow_add]
          _ = 5730500601 := by rw [factor_7_2]; decide
      have factor_7_4 : (67 : ZMod 26771144401) ^ 20 = 15645218592 := by
        calc
          (67 : ZMod 26771144401) ^ 20 = (67 : ZMod 26771144401) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 10 * (67 : ZMod 26771144401) ^ 10 := by rw [pow_add]
          _ = 15645218592 := by rw [factor_7_3]; decide
      have factor_7_5 : (67 : ZMod 26771144401) ^ 41 = 26764062292 := by
        calc
          (67 : ZMod 26771144401) ^ 41 = (67 : ZMod 26771144401) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 20 * (67 : ZMod 26771144401) ^ 20) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 26764062292 := by rw [factor_7_4]; decide
      have factor_7_6 : (67 : ZMod 26771144401) ^ 83 = 22047552502 := by
        calc
          (67 : ZMod 26771144401) ^ 83 = (67 : ZMod 26771144401) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 41 * (67 : ZMod 26771144401) ^ 41) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22047552502 := by rw [factor_7_5]; decide
      have factor_7_7 : (67 : ZMod 26771144401) ^ 167 = 976655991 := by
        calc
          (67 : ZMod 26771144401) ^ 167 = (67 : ZMod 26771144401) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 83 * (67 : ZMod 26771144401) ^ 83) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 976655991 := by rw [factor_7_6]; decide
      have factor_7_8 : (67 : ZMod 26771144401) ^ 335 = 5357318000 := by
        calc
          (67 : ZMod 26771144401) ^ 335 = (67 : ZMod 26771144401) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 167 * (67 : ZMod 26771144401) ^ 167) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 5357318000 := by rw [factor_7_7]; decide
      have factor_7_9 : (67 : ZMod 26771144401) ^ 671 = 18392477913 := by
        calc
          (67 : ZMod 26771144401) ^ 671 = (67 : ZMod 26771144401) ^ (335 + 335 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 335 * (67 : ZMod 26771144401) ^ 335) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 18392477913 := by rw [factor_7_8]; decide
      have factor_7_10 : (67 : ZMod 26771144401) ^ 1343 = 25922942647 := by
        calc
          (67 : ZMod 26771144401) ^ 1343 = (67 : ZMod 26771144401) ^ (671 + 671 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 671 * (67 : ZMod 26771144401) ^ 671) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 25922942647 := by rw [factor_7_9]; decide
      have factor_7_11 : (67 : ZMod 26771144401) ^ 2687 = 1256581174 := by
        calc
          (67 : ZMod 26771144401) ^ 2687 = (67 : ZMod 26771144401) ^ (1343 + 1343 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1343 * (67 : ZMod 26771144401) ^ 1343) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 1256581174 := by rw [factor_7_10]; decide
      have factor_7_12 : (67 : ZMod 26771144401) ^ 5374 = 16871127001 := by
        calc
          (67 : ZMod 26771144401) ^ 5374 = (67 : ZMod 26771144401) ^ (2687 + 2687) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2687 * (67 : ZMod 26771144401) ^ 2687 := by rw [pow_add]
          _ = 16871127001 := by rw [factor_7_11]; decide
      have factor_7_13 : (67 : ZMod 26771144401) ^ 10749 = 11123537437 := by
        calc
          (67 : ZMod 26771144401) ^ 10749 = (67 : ZMod 26771144401) ^ (5374 + 5374 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 5374 * (67 : ZMod 26771144401) ^ 5374) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 11123537437 := by rw [factor_7_12]; decide
      have factor_7_14 : (67 : ZMod 26771144401) ^ 21499 = 12534432569 := by
        calc
          (67 : ZMod 26771144401) ^ 21499 = (67 : ZMod 26771144401) ^ (10749 + 10749 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 10749 * (67 : ZMod 26771144401) ^ 10749) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 12534432569 := by rw [factor_7_13]; decide
      have factor_7_15 : (67 : ZMod 26771144401) ^ 42999 = 7998066188 := by
        calc
          (67 : ZMod 26771144401) ^ 42999 = (67 : ZMod 26771144401) ^ (21499 + 21499 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 21499 * (67 : ZMod 26771144401) ^ 21499) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 7998066188 := by rw [factor_7_14]; decide
      have factor_7_16 : (67 : ZMod 26771144401) ^ 85998 = 24924621264 := by
        calc
          (67 : ZMod 26771144401) ^ 85998 = (67 : ZMod 26771144401) ^ (42999 + 42999) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 42999 * (67 : ZMod 26771144401) ^ 42999 := by rw [pow_add]
          _ = 24924621264 := by rw [factor_7_15]; decide
      have factor_7_17 : (67 : ZMod 26771144401) ^ 171997 = 22038431661 := by
        calc
          (67 : ZMod 26771144401) ^ 171997 = (67 : ZMod 26771144401) ^ (85998 + 85998 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 85998 * (67 : ZMod 26771144401) ^ 85998) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 22038431661 := by rw [factor_7_16]; decide
      have factor_7_18 : (67 : ZMod 26771144401) ^ 343995 = 5320677684 := by
        calc
          (67 : ZMod 26771144401) ^ 343995 = (67 : ZMod 26771144401) ^ (171997 + 171997 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 171997 * (67 : ZMod 26771144401) ^ 171997) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 5320677684 := by rw [factor_7_17]; decide
      have factor_7_19 : (67 : ZMod 26771144401) ^ 687991 = 20420931776 := by
        calc
          (67 : ZMod 26771144401) ^ 687991 = (67 : ZMod 26771144401) ^ (343995 + 343995 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 343995 * (67 : ZMod 26771144401) ^ 343995) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 20420931776 := by rw [factor_7_18]; decide
      have factor_7_20 : (67 : ZMod 26771144401) ^ 1375983 = 18286173217 := by
        calc
          (67 : ZMod 26771144401) ^ 1375983 = (67 : ZMod 26771144401) ^ (687991 + 687991 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 687991 * (67 : ZMod 26771144401) ^ 687991) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 18286173217 := by rw [factor_7_19]; decide
      have factor_7_21 : (67 : ZMod 26771144401) ^ 2751967 = 25103356996 := by
        calc
          (67 : ZMod 26771144401) ^ 2751967 = (67 : ZMod 26771144401) ^ (1375983 + 1375983 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 1375983 * (67 : ZMod 26771144401) ^ 1375983) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 25103356996 := by rw [factor_7_20]; decide
      have factor_7_22 : (67 : ZMod 26771144401) ^ 5503935 = 12507088182 := by
        calc
          (67 : ZMod 26771144401) ^ 5503935 = (67 : ZMod 26771144401) ^ (2751967 + 2751967 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 2751967 * (67 : ZMod 26771144401) ^ 2751967) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 12507088182 := by rw [factor_7_21]; decide
      have factor_7_23 : (67 : ZMod 26771144401) ^ 11007871 = 12687540447 := by
        calc
          (67 : ZMod 26771144401) ^ 11007871 = (67 : ZMod 26771144401) ^ (5503935 + 5503935 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 5503935 * (67 : ZMod 26771144401) ^ 5503935) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 12687540447 := by rw [factor_7_22]; decide
      have factor_7_24 : (67 : ZMod 26771144401) ^ 22015743 = 16603444183 := by
        calc
          (67 : ZMod 26771144401) ^ 22015743 = (67 : ZMod 26771144401) ^ (11007871 + 11007871 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 11007871 * (67 : ZMod 26771144401) ^ 11007871) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 16603444183 := by rw [factor_7_23]; decide
      have factor_7_25 : (67 : ZMod 26771144401) ^ 44031487 = 21270328836 := by
        calc
          (67 : ZMod 26771144401) ^ 44031487 = (67 : ZMod 26771144401) ^ (22015743 + 22015743 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 22015743 * (67 : ZMod 26771144401) ^ 22015743) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 21270328836 := by rw [factor_7_24]; decide
      have factor_7_26 : (67 : ZMod 26771144401) ^ 88062975 = 14489979286 := by
        calc
          (67 : ZMod 26771144401) ^ 88062975 = (67 : ZMod 26771144401) ^ (44031487 + 44031487 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 44031487 * (67 : ZMod 26771144401) ^ 44031487) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 14489979286 := by rw [factor_7_25]; decide
      have factor_7_27 : (67 : ZMod 26771144401) ^ 176125950 = 7044437801 := by
        calc
          (67 : ZMod 26771144401) ^ 176125950 = (67 : ZMod 26771144401) ^ (88062975 + 88062975) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 88062975 * (67 : ZMod 26771144401) ^ 88062975 := by rw [pow_add]
          _ = 7044437801 := by rw [factor_7_26]; decide
      have factor_7_28 : (67 : ZMod 26771144401) ^ 352251900 = 15996351314 := by
        calc
          (67 : ZMod 26771144401) ^ 352251900 = (67 : ZMod 26771144401) ^ (176125950 + 176125950) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 176125950 * (67 : ZMod 26771144401) ^ 176125950 := by rw [pow_add]
          _ = 15996351314 := by rw [factor_7_27]; decide
      have factor_7_29 : (67 : ZMod 26771144401) ^ 704503800 = 14329239834 := by
        calc
          (67 : ZMod 26771144401) ^ 704503800 = (67 : ZMod 26771144401) ^ (352251900 + 352251900) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 352251900 * (67 : ZMod 26771144401) ^ 352251900 := by rw [pow_add]
          _ = 14329239834 := by rw [factor_7_28]; decide
      have factor_7_30 : (67 : ZMod 26771144401) ^ 1409007600 = 21567373675 := by
        calc
          (67 : ZMod 26771144401) ^ 1409007600 = (67 : ZMod 26771144401) ^ (704503800 + 704503800) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 704503800 * (67 : ZMod 26771144401) ^ 704503800 := by rw [pow_add]
          _ = 21567373675 := by rw [factor_7_29]; decide
      change (67 : ZMod 26771144401) ^ 1409007600 ≠ 1
      rw [factor_7_30]
      decide
    ·
      have factor_8_0 : (67 : ZMod 26771144401) ^ 1 = 67 := by norm_num
      have factor_8_1 : (67 : ZMod 26771144401) ^ 2 = 4489 := by
        calc
          (67 : ZMod 26771144401) ^ 2 = (67 : ZMod 26771144401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1 * (67 : ZMod 26771144401) ^ 1 := by rw [pow_add]
          _ = 4489 := by rw [factor_8_0]; decide
      have factor_8_2 : (67 : ZMod 26771144401) ^ 4 = 20151121 := by
        calc
          (67 : ZMod 26771144401) ^ 4 = (67 : ZMod 26771144401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2 * (67 : ZMod 26771144401) ^ 2 := by rw [pow_add]
          _ = 20151121 := by rw [factor_8_1]; decide
      have factor_8_3 : (67 : ZMod 26771144401) ^ 8 = 2959282273 := by
        calc
          (67 : ZMod 26771144401) ^ 8 = (67 : ZMod 26771144401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 4 * (67 : ZMod 26771144401) ^ 4 := by rw [pow_add]
          _ = 2959282273 := by rw [factor_8_2]; decide
      have factor_8_4 : (67 : ZMod 26771144401) ^ 17 = 6076816874 := by
        calc
          (67 : ZMod 26771144401) ^ 17 = (67 : ZMod 26771144401) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 8 * (67 : ZMod 26771144401) ^ 8) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 6076816874 := by rw [factor_8_3]; decide
      have factor_8_5 : (67 : ZMod 26771144401) ^ 34 = 26318994514 := by
        calc
          (67 : ZMod 26771144401) ^ 34 = (67 : ZMod 26771144401) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 17 * (67 : ZMod 26771144401) ^ 17 := by rw [pow_add]
          _ = 26318994514 := by rw [factor_8_4]; decide
      have factor_8_6 : (67 : ZMod 26771144401) ^ 69 = 20244092229 := by
        calc
          (67 : ZMod 26771144401) ^ 69 = (67 : ZMod 26771144401) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 34 * (67 : ZMod 26771144401) ^ 34) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 20244092229 := by rw [factor_8_5]; decide
      have factor_8_7 : (67 : ZMod 26771144401) ^ 138 = 3721665603 := by
        calc
          (67 : ZMod 26771144401) ^ 138 = (67 : ZMod 26771144401) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 69 * (67 : ZMod 26771144401) ^ 69 := by rw [pow_add]
          _ = 3721665603 := by rw [factor_8_6]; decide
      have factor_8_8 : (67 : ZMod 26771144401) ^ 277 = 18464259939 := by
        calc
          (67 : ZMod 26771144401) ^ 277 = (67 : ZMod 26771144401) ^ (138 + 138 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 138 * (67 : ZMod 26771144401) ^ 138) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 18464259939 := by rw [factor_8_7]; decide
      have factor_8_9 : (67 : ZMod 26771144401) ^ 555 = 9896429426 := by
        calc
          (67 : ZMod 26771144401) ^ 555 = (67 : ZMod 26771144401) ^ (277 + 277 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 277 * (67 : ZMod 26771144401) ^ 277) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 9896429426 := by rw [factor_8_8]; decide
      have factor_8_10 : (67 : ZMod 26771144401) ^ 1110 = 14440090015 := by
        calc
          (67 : ZMod 26771144401) ^ 1110 = (67 : ZMod 26771144401) ^ (555 + 555) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 555 * (67 : ZMod 26771144401) ^ 555 := by rw [pow_add]
          _ = 14440090015 := by rw [factor_8_9]; decide
      have factor_8_11 : (67 : ZMod 26771144401) ^ 2220 = 11749023958 := by
        calc
          (67 : ZMod 26771144401) ^ 2220 = (67 : ZMod 26771144401) ^ (1110 + 1110) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1110 * (67 : ZMod 26771144401) ^ 1110 := by rw [pow_add]
          _ = 11749023958 := by rw [factor_8_10]; decide
      have factor_8_12 : (67 : ZMod 26771144401) ^ 4440 = 21659538390 := by
        calc
          (67 : ZMod 26771144401) ^ 4440 = (67 : ZMod 26771144401) ^ (2220 + 2220) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 2220 * (67 : ZMod 26771144401) ^ 2220 := by rw [pow_add]
          _ = 21659538390 := by rw [factor_8_11]; decide
      have factor_8_13 : (67 : ZMod 26771144401) ^ 8880 = 1574591438 := by
        calc
          (67 : ZMod 26771144401) ^ 8880 = (67 : ZMod 26771144401) ^ (4440 + 4440) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 4440 * (67 : ZMod 26771144401) ^ 4440 := by rw [pow_add]
          _ = 1574591438 := by rw [factor_8_12]; decide
      have factor_8_14 : (67 : ZMod 26771144401) ^ 17760 = 3024121509 := by
        calc
          (67 : ZMod 26771144401) ^ 17760 = (67 : ZMod 26771144401) ^ (8880 + 8880) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 8880 * (67 : ZMod 26771144401) ^ 8880 := by rw [pow_add]
          _ = 3024121509 := by rw [factor_8_13]; decide
      have factor_8_15 : (67 : ZMod 26771144401) ^ 35521 = 14112839717 := by
        calc
          (67 : ZMod 26771144401) ^ 35521 = (67 : ZMod 26771144401) ^ (17760 + 17760 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 17760 * (67 : ZMod 26771144401) ^ 17760) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 14112839717 := by rw [factor_8_14]; decide
      have factor_8_16 : (67 : ZMod 26771144401) ^ 71042 = 25280991053 := by
        calc
          (67 : ZMod 26771144401) ^ 71042 = (67 : ZMod 26771144401) ^ (35521 + 35521) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 35521 * (67 : ZMod 26771144401) ^ 35521 := by rw [pow_add]
          _ = 25280991053 := by rw [factor_8_15]; decide
      have factor_8_17 : (67 : ZMod 26771144401) ^ 142085 = 9698395432 := by
        calc
          (67 : ZMod 26771144401) ^ 142085 = (67 : ZMod 26771144401) ^ (71042 + 71042 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 71042 * (67 : ZMod 26771144401) ^ 71042) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 9698395432 := by rw [factor_8_16]; decide
      have factor_8_18 : (67 : ZMod 26771144401) ^ 284170 = 13357886620 := by
        calc
          (67 : ZMod 26771144401) ^ 284170 = (67 : ZMod 26771144401) ^ (142085 + 142085) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 142085 * (67 : ZMod 26771144401) ^ 142085 := by rw [pow_add]
          _ = 13357886620 := by rw [factor_8_17]; decide
      have factor_8_19 : (67 : ZMod 26771144401) ^ 568341 = 2645886883 := by
        calc
          (67 : ZMod 26771144401) ^ 568341 = (67 : ZMod 26771144401) ^ (284170 + 284170 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 284170 * (67 : ZMod 26771144401) ^ 284170) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 2645886883 := by rw [factor_8_18]; decide
      have factor_8_20 : (67 : ZMod 26771144401) ^ 1136682 = 10411458131 := by
        calc
          (67 : ZMod 26771144401) ^ 1136682 = (67 : ZMod 26771144401) ^ (568341 + 568341) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 568341 * (67 : ZMod 26771144401) ^ 568341 := by rw [pow_add]
          _ = 10411458131 := by rw [factor_8_19]; decide
      have factor_8_21 : (67 : ZMod 26771144401) ^ 2273364 = 17887526841 := by
        calc
          (67 : ZMod 26771144401) ^ 2273364 = (67 : ZMod 26771144401) ^ (1136682 + 1136682) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 1136682 * (67 : ZMod 26771144401) ^ 1136682 := by rw [pow_add]
          _ = 17887526841 := by rw [factor_8_20]; decide
      have factor_8_22 : (67 : ZMod 26771144401) ^ 4546729 = 9741211057 := by
        calc
          (67 : ZMod 26771144401) ^ 4546729 = (67 : ZMod 26771144401) ^ (2273364 + 2273364 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 2273364 * (67 : ZMod 26771144401) ^ 2273364) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 9741211057 := by rw [factor_8_21]; decide
      have factor_8_23 : (67 : ZMod 26771144401) ^ 9093459 = 17475639716 := by
        calc
          (67 : ZMod 26771144401) ^ 9093459 = (67 : ZMod 26771144401) ^ (4546729 + 4546729 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 4546729 * (67 : ZMod 26771144401) ^ 4546729) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 17475639716 := by rw [factor_8_22]; decide
      have factor_8_24 : (67 : ZMod 26771144401) ^ 18186918 = 6692469192 := by
        calc
          (67 : ZMod 26771144401) ^ 18186918 = (67 : ZMod 26771144401) ^ (9093459 + 9093459) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 9093459 * (67 : ZMod 26771144401) ^ 9093459 := by rw [pow_add]
          _ = 6692469192 := by rw [factor_8_23]; decide
      have factor_8_25 : (67 : ZMod 26771144401) ^ 36373837 = 4289373284 := by
        calc
          (67 : ZMod 26771144401) ^ 36373837 = (67 : ZMod 26771144401) ^ (18186918 + 18186918 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 18186918 * (67 : ZMod 26771144401) ^ 18186918) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 4289373284 := by rw [factor_8_24]; decide
      have factor_8_26 : (67 : ZMod 26771144401) ^ 72747675 = 18509156218 := by
        calc
          (67 : ZMod 26771144401) ^ 72747675 = (67 : ZMod 26771144401) ^ (36373837 + 36373837 + 1) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = ((67 : ZMod 26771144401) ^ 36373837 * (67 : ZMod 26771144401) ^ 36373837) * (67 : ZMod 26771144401) := by rw [pow_succ, pow_add]
          _ = 18509156218 := by rw [factor_8_25]; decide
      have factor_8_27 : (67 : ZMod 26771144401) ^ 145495350 = 23573609672 := by
        calc
          (67 : ZMod 26771144401) ^ 145495350 = (67 : ZMod 26771144401) ^ (72747675 + 72747675) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 72747675 * (67 : ZMod 26771144401) ^ 72747675 := by rw [pow_add]
          _ = 23573609672 := by rw [factor_8_26]; decide
      have factor_8_28 : (67 : ZMod 26771144401) ^ 290990700 = 1875413978 := by
        calc
          (67 : ZMod 26771144401) ^ 290990700 = (67 : ZMod 26771144401) ^ (145495350 + 145495350) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 145495350 * (67 : ZMod 26771144401) ^ 145495350 := by rw [pow_add]
          _ = 1875413978 := by rw [factor_8_27]; decide
      have factor_8_29 : (67 : ZMod 26771144401) ^ 581981400 = 4111290658 := by
        calc
          (67 : ZMod 26771144401) ^ 581981400 = (67 : ZMod 26771144401) ^ (290990700 + 290990700) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 290990700 * (67 : ZMod 26771144401) ^ 290990700 := by rw [pow_add]
          _ = 4111290658 := by rw [factor_8_28]; decide
      have factor_8_30 : (67 : ZMod 26771144401) ^ 1163962800 = 14535538192 := by
        calc
          (67 : ZMod 26771144401) ^ 1163962800 = (67 : ZMod 26771144401) ^ (581981400 + 581981400) :=
            congrArg (fun n : ℕ => (67 : ZMod 26771144401) ^ n) (by norm_num)
          _ = (67 : ZMod 26771144401) ^ 581981400 * (67 : ZMod 26771144401) ^ 581981400 := by rw [pow_add]
          _ = 14535538192 := by rw [factor_8_29]; decide
      change (67 : ZMod 26771144401) ^ 1163962800 ≠ 1
      rw [factor_8_30]
      decide

#print axioms prime_lucas_26771144401

end TotientTailPeriodKiller
end Erdos249257
