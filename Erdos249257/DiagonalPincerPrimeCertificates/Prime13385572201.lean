import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_13385572201 : Nat.Prime 13385572201 := by
  apply lucas_primality 13385572201 (37 : ZMod 13385572201)
  ·
      have fermat_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have fermat_1 : (37 : ZMod 13385572201) ^ 3 = 50653 := by
        calc
          (37 : ZMod 13385572201) ^ 3 = (37 : ZMod 13385572201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [fermat_0]; decide
      have fermat_2 : (37 : ZMod 13385572201) ^ 6 = 2565726409 := by
        calc
          (37 : ZMod 13385572201) ^ 6 = (37 : ZMod 13385572201) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 3 * (37 : ZMod 13385572201) ^ 3 := by rw [pow_add]
          _ = 2565726409 := by rw [fermat_1]; decide
      have fermat_3 : (37 : ZMod 13385572201) ^ 12 = 13333842691 := by
        calc
          (37 : ZMod 13385572201) ^ 12 = (37 : ZMod 13385572201) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 6 * (37 : ZMod 13385572201) ^ 6 := by rw [pow_add]
          _ = 13333842691 := by rw [fermat_2]; decide
      have fermat_4 : (37 : ZMod 13385572201) ^ 24 = 5694993788 := by
        calc
          (37 : ZMod 13385572201) ^ 24 = (37 : ZMod 13385572201) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 12 * (37 : ZMod 13385572201) ^ 12 := by rw [pow_add]
          _ = 5694993788 := by rw [fermat_3]; decide
      have fermat_5 : (37 : ZMod 13385572201) ^ 49 = 10306565592 := by
        calc
          (37 : ZMod 13385572201) ^ 49 = (37 : ZMod 13385572201) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 24 * (37 : ZMod 13385572201) ^ 24) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 10306565592 := by rw [fermat_4]; decide
      have fermat_6 : (37 : ZMod 13385572201) ^ 99 = 1782368689 := by
        calc
          (37 : ZMod 13385572201) ^ 99 = (37 : ZMod 13385572201) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 49 * (37 : ZMod 13385572201) ^ 49) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1782368689 := by rw [fermat_5]; decide
      have fermat_7 : (37 : ZMod 13385572201) ^ 199 = 11887744101 := by
        calc
          (37 : ZMod 13385572201) ^ 199 = (37 : ZMod 13385572201) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 99 * (37 : ZMod 13385572201) ^ 99) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 11887744101 := by rw [fermat_6]; decide
      have fermat_8 : (37 : ZMod 13385572201) ^ 398 = 1002994186 := by
        calc
          (37 : ZMod 13385572201) ^ 398 = (37 : ZMod 13385572201) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 199 * (37 : ZMod 13385572201) ^ 199 := by rw [pow_add]
          _ = 1002994186 := by rw [fermat_7]; decide
      have fermat_9 : (37 : ZMod 13385572201) ^ 797 = 7567300976 := by
        calc
          (37 : ZMod 13385572201) ^ 797 = (37 : ZMod 13385572201) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 398 * (37 : ZMod 13385572201) ^ 398) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7567300976 := by rw [fermat_8]; decide
      have fermat_10 : (37 : ZMod 13385572201) ^ 1595 = 1005997679 := by
        calc
          (37 : ZMod 13385572201) ^ 1595 = (37 : ZMod 13385572201) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 797 * (37 : ZMod 13385572201) ^ 797) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1005997679 := by rw [fermat_9]; decide
      have fermat_11 : (37 : ZMod 13385572201) ^ 3191 = 4128601657 := by
        calc
          (37 : ZMod 13385572201) ^ 3191 = (37 : ZMod 13385572201) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1595 * (37 : ZMod 13385572201) ^ 1595) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4128601657 := by rw [fermat_10]; decide
      have fermat_12 : (37 : ZMod 13385572201) ^ 6382 = 1399138997 := by
        calc
          (37 : ZMod 13385572201) ^ 6382 = (37 : ZMod 13385572201) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 3191 * (37 : ZMod 13385572201) ^ 3191 := by rw [pow_add]
          _ = 1399138997 := by rw [fermat_11]; decide
      have fermat_13 : (37 : ZMod 13385572201) ^ 12765 = 5697509146 := by
        calc
          (37 : ZMod 13385572201) ^ 12765 = (37 : ZMod 13385572201) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 6382 * (37 : ZMod 13385572201) ^ 6382) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5697509146 := by rw [fermat_12]; decide
      have fermat_14 : (37 : ZMod 13385572201) ^ 25530 = 5418299343 := by
        calc
          (37 : ZMod 13385572201) ^ 25530 = (37 : ZMod 13385572201) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 12765 * (37 : ZMod 13385572201) ^ 12765 := by rw [pow_add]
          _ = 5418299343 := by rw [fermat_13]; decide
      have fermat_15 : (37 : ZMod 13385572201) ^ 51061 = 5990353305 := by
        calc
          (37 : ZMod 13385572201) ^ 51061 = (37 : ZMod 13385572201) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 25530 * (37 : ZMod 13385572201) ^ 25530) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5990353305 := by rw [fermat_14]; decide
      have fermat_16 : (37 : ZMod 13385572201) ^ 102123 = 5946953009 := by
        calc
          (37 : ZMod 13385572201) ^ 102123 = (37 : ZMod 13385572201) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 51061 * (37 : ZMod 13385572201) ^ 51061) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5946953009 := by rw [fermat_15]; decide
      have fermat_17 : (37 : ZMod 13385572201) ^ 204247 = 3293680249 := by
        calc
          (37 : ZMod 13385572201) ^ 204247 = (37 : ZMod 13385572201) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 102123 * (37 : ZMod 13385572201) ^ 102123) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3293680249 := by rw [fermat_16]; decide
      have fermat_18 : (37 : ZMod 13385572201) ^ 408495 = 9711713 := by
        calc
          (37 : ZMod 13385572201) ^ 408495 = (37 : ZMod 13385572201) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 204247 * (37 : ZMod 13385572201) ^ 204247) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9711713 := by rw [fermat_17]; decide
      have fermat_19 : (37 : ZMod 13385572201) ^ 816990 = 2627666123 := by
        calc
          (37 : ZMod 13385572201) ^ 816990 = (37 : ZMod 13385572201) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 408495 * (37 : ZMod 13385572201) ^ 408495 := by rw [pow_add]
          _ = 2627666123 := by rw [fermat_18]; decide
      have fermat_20 : (37 : ZMod 13385572201) ^ 1633980 = 9127218899 := by
        calc
          (37 : ZMod 13385572201) ^ 1633980 = (37 : ZMod 13385572201) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 816990 * (37 : ZMod 13385572201) ^ 816990 := by rw [pow_add]
          _ = 9127218899 := by rw [fermat_19]; decide
      have fermat_21 : (37 : ZMod 13385572201) ^ 3267961 = 13190707985 := by
        calc
          (37 : ZMod 13385572201) ^ 3267961 = (37 : ZMod 13385572201) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1633980 * (37 : ZMod 13385572201) ^ 1633980) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 13190707985 := by rw [fermat_20]; decide
      have fermat_22 : (37 : ZMod 13385572201) ^ 6535923 = 9191124228 := by
        calc
          (37 : ZMod 13385572201) ^ 6535923 = (37 : ZMod 13385572201) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 3267961 * (37 : ZMod 13385572201) ^ 3267961) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9191124228 := by rw [fermat_21]; decide
      have fermat_23 : (37 : ZMod 13385572201) ^ 13071847 = 7567257441 := by
        calc
          (37 : ZMod 13385572201) ^ 13071847 = (37 : ZMod 13385572201) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 6535923 * (37 : ZMod 13385572201) ^ 6535923) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7567257441 := by rw [fermat_22]; decide
      have fermat_24 : (37 : ZMod 13385572201) ^ 26143695 = 4135340429 := by
        calc
          (37 : ZMod 13385572201) ^ 26143695 = (37 : ZMod 13385572201) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 13071847 * (37 : ZMod 13385572201) ^ 13071847) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4135340429 := by rw [fermat_23]; decide
      have fermat_25 : (37 : ZMod 13385572201) ^ 52287391 = 9640373008 := by
        calc
          (37 : ZMod 13385572201) ^ 52287391 = (37 : ZMod 13385572201) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 26143695 * (37 : ZMod 13385572201) ^ 26143695) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9640373008 := by rw [fermat_24]; decide
      have fermat_26 : (37 : ZMod 13385572201) ^ 104574782 = 455312592 := by
        calc
          (37 : ZMod 13385572201) ^ 104574782 = (37 : ZMod 13385572201) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 52287391 * (37 : ZMod 13385572201) ^ 52287391 := by rw [pow_add]
          _ = 455312592 := by rw [fermat_25]; decide
      have fermat_27 : (37 : ZMod 13385572201) ^ 209149565 = 4731872067 := by
        calc
          (37 : ZMod 13385572201) ^ 209149565 = (37 : ZMod 13385572201) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 104574782 * (37 : ZMod 13385572201) ^ 104574782) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4731872067 := by rw [fermat_26]; decide
      have fermat_28 : (37 : ZMod 13385572201) ^ 418299131 = 5975943210 := by
        calc
          (37 : ZMod 13385572201) ^ 418299131 = (37 : ZMod 13385572201) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 209149565 * (37 : ZMod 13385572201) ^ 209149565) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5975943210 := by rw [fermat_27]; decide
      have fermat_29 : (37 : ZMod 13385572201) ^ 836598262 = 2271381967 := by
        calc
          (37 : ZMod 13385572201) ^ 836598262 = (37 : ZMod 13385572201) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 418299131 * (37 : ZMod 13385572201) ^ 418299131 := by rw [pow_add]
          _ = 2271381967 := by rw [fermat_28]; decide
      have fermat_30 : (37 : ZMod 13385572201) ^ 1673196525 = 1156349945 := by
        calc
          (37 : ZMod 13385572201) ^ 1673196525 = (37 : ZMod 13385572201) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 836598262 * (37 : ZMod 13385572201) ^ 836598262) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1156349945 := by rw [fermat_29]; decide
      have fermat_31 : (37 : ZMod 13385572201) ^ 3346393050 = 5827414314 := by
        calc
          (37 : ZMod 13385572201) ^ 3346393050 = (37 : ZMod 13385572201) ^ (1673196525 + 1673196525) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1673196525 * (37 : ZMod 13385572201) ^ 1673196525 := by rw [pow_add]
          _ = 5827414314 := by rw [fermat_30]; decide
      have fermat_32 : (37 : ZMod 13385572201) ^ 6692786100 = 13385572200 := by
        calc
          (37 : ZMod 13385572201) ^ 6692786100 = (37 : ZMod 13385572201) ^ (3346393050 + 3346393050) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 3346393050 * (37 : ZMod 13385572201) ^ 3346393050 := by rw [pow_add]
          _ = 13385572200 := by rw [fermat_31]; decide
      have fermat_33 : (37 : ZMod 13385572201) ^ 13385572200 = 1 := by
        calc
          (37 : ZMod 13385572201) ^ 13385572200 = (37 : ZMod 13385572201) ^ (6692786100 + 6692786100) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 6692786100 * (37 : ZMod 13385572201) ^ 6692786100 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 13385572201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have factor_0_1 : (37 : ZMod 13385572201) ^ 3 = 50653 := by
        calc
          (37 : ZMod 13385572201) ^ 3 = (37 : ZMod 13385572201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_0_0]; decide
      have factor_0_2 : (37 : ZMod 13385572201) ^ 6 = 2565726409 := by
        calc
          (37 : ZMod 13385572201) ^ 6 = (37 : ZMod 13385572201) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 3 * (37 : ZMod 13385572201) ^ 3 := by rw [pow_add]
          _ = 2565726409 := by rw [factor_0_1]; decide
      have factor_0_3 : (37 : ZMod 13385572201) ^ 12 = 13333842691 := by
        calc
          (37 : ZMod 13385572201) ^ 12 = (37 : ZMod 13385572201) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 6 * (37 : ZMod 13385572201) ^ 6 := by rw [pow_add]
          _ = 13333842691 := by rw [factor_0_2]; decide
      have factor_0_4 : (37 : ZMod 13385572201) ^ 24 = 5694993788 := by
        calc
          (37 : ZMod 13385572201) ^ 24 = (37 : ZMod 13385572201) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 12 * (37 : ZMod 13385572201) ^ 12 := by rw [pow_add]
          _ = 5694993788 := by rw [factor_0_3]; decide
      have factor_0_5 : (37 : ZMod 13385572201) ^ 49 = 10306565592 := by
        calc
          (37 : ZMod 13385572201) ^ 49 = (37 : ZMod 13385572201) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 24 * (37 : ZMod 13385572201) ^ 24) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 10306565592 := by rw [factor_0_4]; decide
      have factor_0_6 : (37 : ZMod 13385572201) ^ 99 = 1782368689 := by
        calc
          (37 : ZMod 13385572201) ^ 99 = (37 : ZMod 13385572201) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 49 * (37 : ZMod 13385572201) ^ 49) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1782368689 := by rw [factor_0_5]; decide
      have factor_0_7 : (37 : ZMod 13385572201) ^ 199 = 11887744101 := by
        calc
          (37 : ZMod 13385572201) ^ 199 = (37 : ZMod 13385572201) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 99 * (37 : ZMod 13385572201) ^ 99) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 11887744101 := by rw [factor_0_6]; decide
      have factor_0_8 : (37 : ZMod 13385572201) ^ 398 = 1002994186 := by
        calc
          (37 : ZMod 13385572201) ^ 398 = (37 : ZMod 13385572201) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 199 * (37 : ZMod 13385572201) ^ 199 := by rw [pow_add]
          _ = 1002994186 := by rw [factor_0_7]; decide
      have factor_0_9 : (37 : ZMod 13385572201) ^ 797 = 7567300976 := by
        calc
          (37 : ZMod 13385572201) ^ 797 = (37 : ZMod 13385572201) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 398 * (37 : ZMod 13385572201) ^ 398) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7567300976 := by rw [factor_0_8]; decide
      have factor_0_10 : (37 : ZMod 13385572201) ^ 1595 = 1005997679 := by
        calc
          (37 : ZMod 13385572201) ^ 1595 = (37 : ZMod 13385572201) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 797 * (37 : ZMod 13385572201) ^ 797) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1005997679 := by rw [factor_0_9]; decide
      have factor_0_11 : (37 : ZMod 13385572201) ^ 3191 = 4128601657 := by
        calc
          (37 : ZMod 13385572201) ^ 3191 = (37 : ZMod 13385572201) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1595 * (37 : ZMod 13385572201) ^ 1595) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4128601657 := by rw [factor_0_10]; decide
      have factor_0_12 : (37 : ZMod 13385572201) ^ 6382 = 1399138997 := by
        calc
          (37 : ZMod 13385572201) ^ 6382 = (37 : ZMod 13385572201) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 3191 * (37 : ZMod 13385572201) ^ 3191 := by rw [pow_add]
          _ = 1399138997 := by rw [factor_0_11]; decide
      have factor_0_13 : (37 : ZMod 13385572201) ^ 12765 = 5697509146 := by
        calc
          (37 : ZMod 13385572201) ^ 12765 = (37 : ZMod 13385572201) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 6382 * (37 : ZMod 13385572201) ^ 6382) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5697509146 := by rw [factor_0_12]; decide
      have factor_0_14 : (37 : ZMod 13385572201) ^ 25530 = 5418299343 := by
        calc
          (37 : ZMod 13385572201) ^ 25530 = (37 : ZMod 13385572201) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 12765 * (37 : ZMod 13385572201) ^ 12765 := by rw [pow_add]
          _ = 5418299343 := by rw [factor_0_13]; decide
      have factor_0_15 : (37 : ZMod 13385572201) ^ 51061 = 5990353305 := by
        calc
          (37 : ZMod 13385572201) ^ 51061 = (37 : ZMod 13385572201) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 25530 * (37 : ZMod 13385572201) ^ 25530) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5990353305 := by rw [factor_0_14]; decide
      have factor_0_16 : (37 : ZMod 13385572201) ^ 102123 = 5946953009 := by
        calc
          (37 : ZMod 13385572201) ^ 102123 = (37 : ZMod 13385572201) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 51061 * (37 : ZMod 13385572201) ^ 51061) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5946953009 := by rw [factor_0_15]; decide
      have factor_0_17 : (37 : ZMod 13385572201) ^ 204247 = 3293680249 := by
        calc
          (37 : ZMod 13385572201) ^ 204247 = (37 : ZMod 13385572201) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 102123 * (37 : ZMod 13385572201) ^ 102123) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3293680249 := by rw [factor_0_16]; decide
      have factor_0_18 : (37 : ZMod 13385572201) ^ 408495 = 9711713 := by
        calc
          (37 : ZMod 13385572201) ^ 408495 = (37 : ZMod 13385572201) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 204247 * (37 : ZMod 13385572201) ^ 204247) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9711713 := by rw [factor_0_17]; decide
      have factor_0_19 : (37 : ZMod 13385572201) ^ 816990 = 2627666123 := by
        calc
          (37 : ZMod 13385572201) ^ 816990 = (37 : ZMod 13385572201) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 408495 * (37 : ZMod 13385572201) ^ 408495 := by rw [pow_add]
          _ = 2627666123 := by rw [factor_0_18]; decide
      have factor_0_20 : (37 : ZMod 13385572201) ^ 1633980 = 9127218899 := by
        calc
          (37 : ZMod 13385572201) ^ 1633980 = (37 : ZMod 13385572201) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 816990 * (37 : ZMod 13385572201) ^ 816990 := by rw [pow_add]
          _ = 9127218899 := by rw [factor_0_19]; decide
      have factor_0_21 : (37 : ZMod 13385572201) ^ 3267961 = 13190707985 := by
        calc
          (37 : ZMod 13385572201) ^ 3267961 = (37 : ZMod 13385572201) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1633980 * (37 : ZMod 13385572201) ^ 1633980) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 13190707985 := by rw [factor_0_20]; decide
      have factor_0_22 : (37 : ZMod 13385572201) ^ 6535923 = 9191124228 := by
        calc
          (37 : ZMod 13385572201) ^ 6535923 = (37 : ZMod 13385572201) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 3267961 * (37 : ZMod 13385572201) ^ 3267961) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9191124228 := by rw [factor_0_21]; decide
      have factor_0_23 : (37 : ZMod 13385572201) ^ 13071847 = 7567257441 := by
        calc
          (37 : ZMod 13385572201) ^ 13071847 = (37 : ZMod 13385572201) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 6535923 * (37 : ZMod 13385572201) ^ 6535923) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7567257441 := by rw [factor_0_22]; decide
      have factor_0_24 : (37 : ZMod 13385572201) ^ 26143695 = 4135340429 := by
        calc
          (37 : ZMod 13385572201) ^ 26143695 = (37 : ZMod 13385572201) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 13071847 * (37 : ZMod 13385572201) ^ 13071847) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4135340429 := by rw [factor_0_23]; decide
      have factor_0_25 : (37 : ZMod 13385572201) ^ 52287391 = 9640373008 := by
        calc
          (37 : ZMod 13385572201) ^ 52287391 = (37 : ZMod 13385572201) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 26143695 * (37 : ZMod 13385572201) ^ 26143695) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9640373008 := by rw [factor_0_24]; decide
      have factor_0_26 : (37 : ZMod 13385572201) ^ 104574782 = 455312592 := by
        calc
          (37 : ZMod 13385572201) ^ 104574782 = (37 : ZMod 13385572201) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 52287391 * (37 : ZMod 13385572201) ^ 52287391 := by rw [pow_add]
          _ = 455312592 := by rw [factor_0_25]; decide
      have factor_0_27 : (37 : ZMod 13385572201) ^ 209149565 = 4731872067 := by
        calc
          (37 : ZMod 13385572201) ^ 209149565 = (37 : ZMod 13385572201) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 104574782 * (37 : ZMod 13385572201) ^ 104574782) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4731872067 := by rw [factor_0_26]; decide
      have factor_0_28 : (37 : ZMod 13385572201) ^ 418299131 = 5975943210 := by
        calc
          (37 : ZMod 13385572201) ^ 418299131 = (37 : ZMod 13385572201) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 209149565 * (37 : ZMod 13385572201) ^ 209149565) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5975943210 := by rw [factor_0_27]; decide
      have factor_0_29 : (37 : ZMod 13385572201) ^ 836598262 = 2271381967 := by
        calc
          (37 : ZMod 13385572201) ^ 836598262 = (37 : ZMod 13385572201) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 418299131 * (37 : ZMod 13385572201) ^ 418299131 := by rw [pow_add]
          _ = 2271381967 := by rw [factor_0_28]; decide
      have factor_0_30 : (37 : ZMod 13385572201) ^ 1673196525 = 1156349945 := by
        calc
          (37 : ZMod 13385572201) ^ 1673196525 = (37 : ZMod 13385572201) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 836598262 * (37 : ZMod 13385572201) ^ 836598262) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1156349945 := by rw [factor_0_29]; decide
      have factor_0_31 : (37 : ZMod 13385572201) ^ 3346393050 = 5827414314 := by
        calc
          (37 : ZMod 13385572201) ^ 3346393050 = (37 : ZMod 13385572201) ^ (1673196525 + 1673196525) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1673196525 * (37 : ZMod 13385572201) ^ 1673196525 := by rw [pow_add]
          _ = 5827414314 := by rw [factor_0_30]; decide
      have factor_0_32 : (37 : ZMod 13385572201) ^ 6692786100 = 13385572200 := by
        calc
          (37 : ZMod 13385572201) ^ 6692786100 = (37 : ZMod 13385572201) ^ (3346393050 + 3346393050) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 3346393050 * (37 : ZMod 13385572201) ^ 3346393050 := by rw [pow_add]
          _ = 13385572200 := by rw [factor_0_31]; decide
      change (37 : ZMod 13385572201) ^ 6692786100 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have factor_1_1 : (37 : ZMod 13385572201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 13385572201) ^ 2 = (37 : ZMod 13385572201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_1_0]; decide
      have factor_1_2 : (37 : ZMod 13385572201) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 13385572201) ^ 4 = (37 : ZMod 13385572201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 2 * (37 : ZMod 13385572201) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_1_1]; decide
      have factor_1_3 : (37 : ZMod 13385572201) ^ 8 = 5459537259 := by
        calc
          (37 : ZMod 13385572201) ^ 8 = (37 : ZMod 13385572201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 4 * (37 : ZMod 13385572201) ^ 4 := by rw [pow_add]
          _ = 5459537259 := by rw [factor_1_2]; decide
      have factor_1_4 : (37 : ZMod 13385572201) ^ 16 = 2269260733 := by
        calc
          (37 : ZMod 13385572201) ^ 16 = (37 : ZMod 13385572201) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 8 * (37 : ZMod 13385572201) ^ 8 := by rw [pow_add]
          _ = 2269260733 := by rw [factor_1_3]; decide
      have factor_1_5 : (37 : ZMod 13385572201) ^ 33 = 3691825185 := by
        calc
          (37 : ZMod 13385572201) ^ 33 = (37 : ZMod 13385572201) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 16 * (37 : ZMod 13385572201) ^ 16) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3691825185 := by rw [factor_1_4]; decide
      have factor_1_6 : (37 : ZMod 13385572201) ^ 66 = 4585092369 := by
        calc
          (37 : ZMod 13385572201) ^ 66 = (37 : ZMod 13385572201) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 33 * (37 : ZMod 13385572201) ^ 33 := by rw [pow_add]
          _ = 4585092369 := by rw [factor_1_5]; decide
      have factor_1_7 : (37 : ZMod 13385572201) ^ 132 = 748472146 := by
        calc
          (37 : ZMod 13385572201) ^ 132 = (37 : ZMod 13385572201) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 66 * (37 : ZMod 13385572201) ^ 66 := by rw [pow_add]
          _ = 748472146 := by rw [factor_1_6]; decide
      have factor_1_8 : (37 : ZMod 13385572201) ^ 265 = 1827822166 := by
        calc
          (37 : ZMod 13385572201) ^ 265 = (37 : ZMod 13385572201) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 132 * (37 : ZMod 13385572201) ^ 132) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1827822166 := by rw [factor_1_7]; decide
      have factor_1_9 : (37 : ZMod 13385572201) ^ 531 = 13251494275 := by
        calc
          (37 : ZMod 13385572201) ^ 531 = (37 : ZMod 13385572201) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 265 * (37 : ZMod 13385572201) ^ 265) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 13251494275 := by rw [factor_1_8]; decide
      have factor_1_10 : (37 : ZMod 13385572201) ^ 1063 = 7711898628 := by
        calc
          (37 : ZMod 13385572201) ^ 1063 = (37 : ZMod 13385572201) ^ (531 + 531 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 531 * (37 : ZMod 13385572201) ^ 531) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7711898628 := by rw [factor_1_9]; decide
      have factor_1_11 : (37 : ZMod 13385572201) ^ 2127 = 3837315137 := by
        calc
          (37 : ZMod 13385572201) ^ 2127 = (37 : ZMod 13385572201) ^ (1063 + 1063 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1063 * (37 : ZMod 13385572201) ^ 1063) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3837315137 := by rw [factor_1_10]; decide
      have factor_1_12 : (37 : ZMod 13385572201) ^ 4255 = 4902715286 := by
        calc
          (37 : ZMod 13385572201) ^ 4255 = (37 : ZMod 13385572201) ^ (2127 + 2127 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 2127 * (37 : ZMod 13385572201) ^ 2127) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4902715286 := by rw [factor_1_11]; decide
      have factor_1_13 : (37 : ZMod 13385572201) ^ 8510 = 7711841951 := by
        calc
          (37 : ZMod 13385572201) ^ 8510 = (37 : ZMod 13385572201) ^ (4255 + 4255) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 4255 * (37 : ZMod 13385572201) ^ 4255 := by rw [pow_add]
          _ = 7711841951 := by rw [factor_1_12]; decide
      have factor_1_14 : (37 : ZMod 13385572201) ^ 17020 = 5387457047 := by
        calc
          (37 : ZMod 13385572201) ^ 17020 = (37 : ZMod 13385572201) ^ (8510 + 8510) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 8510 * (37 : ZMod 13385572201) ^ 8510 := by rw [pow_add]
          _ = 5387457047 := by rw [factor_1_13]; decide
      have factor_1_15 : (37 : ZMod 13385572201) ^ 34041 = 2340648221 := by
        calc
          (37 : ZMod 13385572201) ^ 34041 = (37 : ZMod 13385572201) ^ (17020 + 17020 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 17020 * (37 : ZMod 13385572201) ^ 17020) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 2340648221 := by rw [factor_1_14]; decide
      have factor_1_16 : (37 : ZMod 13385572201) ^ 68082 = 516959263 := by
        calc
          (37 : ZMod 13385572201) ^ 68082 = (37 : ZMod 13385572201) ^ (34041 + 34041) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 34041 * (37 : ZMod 13385572201) ^ 34041 := by rw [pow_add]
          _ = 516959263 := by rw [factor_1_15]; decide
      have factor_1_17 : (37 : ZMod 13385572201) ^ 136165 = 11659520589 := by
        calc
          (37 : ZMod 13385572201) ^ 136165 = (37 : ZMod 13385572201) ^ (68082 + 68082 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 68082 * (37 : ZMod 13385572201) ^ 68082) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 11659520589 := by rw [factor_1_16]; decide
      have factor_1_18 : (37 : ZMod 13385572201) ^ 272330 = 2401649700 := by
        calc
          (37 : ZMod 13385572201) ^ 272330 = (37 : ZMod 13385572201) ^ (136165 + 136165) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 136165 * (37 : ZMod 13385572201) ^ 136165 := by rw [pow_add]
          _ = 2401649700 := by rw [factor_1_17]; decide
      have factor_1_19 : (37 : ZMod 13385572201) ^ 544660 = 8200819557 := by
        calc
          (37 : ZMod 13385572201) ^ 544660 = (37 : ZMod 13385572201) ^ (272330 + 272330) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 272330 * (37 : ZMod 13385572201) ^ 272330 := by rw [pow_add]
          _ = 8200819557 := by rw [factor_1_18]; decide
      have factor_1_20 : (37 : ZMod 13385572201) ^ 1089320 = 9990430416 := by
        calc
          (37 : ZMod 13385572201) ^ 1089320 = (37 : ZMod 13385572201) ^ (544660 + 544660) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 544660 * (37 : ZMod 13385572201) ^ 544660 := by rw [pow_add]
          _ = 9990430416 := by rw [factor_1_19]; decide
      have factor_1_21 : (37 : ZMod 13385572201) ^ 2178641 = 13081588336 := by
        calc
          (37 : ZMod 13385572201) ^ 2178641 = (37 : ZMod 13385572201) ^ (1089320 + 1089320 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1089320 * (37 : ZMod 13385572201) ^ 1089320) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 13081588336 := by rw [factor_1_20]; decide
      have factor_1_22 : (37 : ZMod 13385572201) ^ 4357282 = 3493227408 := by
        calc
          (37 : ZMod 13385572201) ^ 4357282 = (37 : ZMod 13385572201) ^ (2178641 + 2178641) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 2178641 * (37 : ZMod 13385572201) ^ 2178641 := by rw [pow_add]
          _ = 3493227408 := by rw [factor_1_21]; decide
      have factor_1_23 : (37 : ZMod 13385572201) ^ 8714565 = 5236453217 := by
        calc
          (37 : ZMod 13385572201) ^ 8714565 = (37 : ZMod 13385572201) ^ (4357282 + 4357282 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 4357282 * (37 : ZMod 13385572201) ^ 4357282) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5236453217 := by rw [factor_1_22]; decide
      have factor_1_24 : (37 : ZMod 13385572201) ^ 17429130 = 5717514995 := by
        calc
          (37 : ZMod 13385572201) ^ 17429130 = (37 : ZMod 13385572201) ^ (8714565 + 8714565) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 8714565 * (37 : ZMod 13385572201) ^ 8714565 := by rw [pow_add]
          _ = 5717514995 := by rw [factor_1_23]; decide
      have factor_1_25 : (37 : ZMod 13385572201) ^ 34858260 = 9679327151 := by
        calc
          (37 : ZMod 13385572201) ^ 34858260 = (37 : ZMod 13385572201) ^ (17429130 + 17429130) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 17429130 * (37 : ZMod 13385572201) ^ 17429130 := by rw [pow_add]
          _ = 9679327151 := by rw [factor_1_24]; decide
      have factor_1_26 : (37 : ZMod 13385572201) ^ 69716521 = 3097356820 := by
        calc
          (37 : ZMod 13385572201) ^ 69716521 = (37 : ZMod 13385572201) ^ (34858260 + 34858260 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 34858260 * (37 : ZMod 13385572201) ^ 34858260) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3097356820 := by rw [factor_1_25]; decide
      have factor_1_27 : (37 : ZMod 13385572201) ^ 139433043 = 4873004351 := by
        calc
          (37 : ZMod 13385572201) ^ 139433043 = (37 : ZMod 13385572201) ^ (69716521 + 69716521 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 69716521 * (37 : ZMod 13385572201) ^ 69716521) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4873004351 := by rw [factor_1_26]; decide
      have factor_1_28 : (37 : ZMod 13385572201) ^ 278866087 = 7957483300 := by
        calc
          (37 : ZMod 13385572201) ^ 278866087 = (37 : ZMod 13385572201) ^ (139433043 + 139433043 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 139433043 * (37 : ZMod 13385572201) ^ 139433043) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7957483300 := by rw [factor_1_27]; decide
      have factor_1_29 : (37 : ZMod 13385572201) ^ 557732175 = 10230212413 := by
        calc
          (37 : ZMod 13385572201) ^ 557732175 = (37 : ZMod 13385572201) ^ (278866087 + 278866087 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 278866087 * (37 : ZMod 13385572201) ^ 278866087) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 10230212413 := by rw [factor_1_28]; decide
      have factor_1_30 : (37 : ZMod 13385572201) ^ 1115464350 = 11914157567 := by
        calc
          (37 : ZMod 13385572201) ^ 1115464350 = (37 : ZMod 13385572201) ^ (557732175 + 557732175) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 557732175 * (37 : ZMod 13385572201) ^ 557732175 := by rw [pow_add]
          _ = 11914157567 := by rw [factor_1_29]; decide
      have factor_1_31 : (37 : ZMod 13385572201) ^ 2230928700 = 4050794086 := by
        calc
          (37 : ZMod 13385572201) ^ 2230928700 = (37 : ZMod 13385572201) ^ (1115464350 + 1115464350) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1115464350 * (37 : ZMod 13385572201) ^ 1115464350 := by rw [pow_add]
          _ = 4050794086 := by rw [factor_1_30]; decide
      have factor_1_32 : (37 : ZMod 13385572201) ^ 4461857400 = 4050794085 := by
        calc
          (37 : ZMod 13385572201) ^ 4461857400 = (37 : ZMod 13385572201) ^ (2230928700 + 2230928700) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 2230928700 * (37 : ZMod 13385572201) ^ 2230928700 := by rw [pow_add]
          _ = 4050794085 := by rw [factor_1_31]; decide
      change (37 : ZMod 13385572201) ^ 4461857400 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have factor_2_1 : (37 : ZMod 13385572201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 13385572201) ^ 2 = (37 : ZMod 13385572201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_2_0]; decide
      have factor_2_2 : (37 : ZMod 13385572201) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 13385572201) ^ 4 = (37 : ZMod 13385572201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 2 * (37 : ZMod 13385572201) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_2_1]; decide
      have factor_2_3 : (37 : ZMod 13385572201) ^ 9 = 1219295568 := by
        calc
          (37 : ZMod 13385572201) ^ 9 = (37 : ZMod 13385572201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 4 * (37 : ZMod 13385572201) ^ 4) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1219295568 := by rw [factor_2_2]; decide
      have factor_2_4 : (37 : ZMod 13385572201) ^ 19 = 2955418662 := by
        calc
          (37 : ZMod 13385572201) ^ 19 = (37 : ZMod 13385572201) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 9 * (37 : ZMod 13385572201) ^ 9) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 2955418662 := by rw [factor_2_3]; decide
      have factor_2_5 : (37 : ZMod 13385572201) ^ 39 = 11963884150 := by
        calc
          (37 : ZMod 13385572201) ^ 39 = (37 : ZMod 13385572201) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 19 * (37 : ZMod 13385572201) ^ 19) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 11963884150 := by rw [factor_2_4]; decide
      have factor_2_6 : (37 : ZMod 13385572201) ^ 79 = 188321726 := by
        calc
          (37 : ZMod 13385572201) ^ 79 = (37 : ZMod 13385572201) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 39 * (37 : ZMod 13385572201) ^ 39) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 188321726 := by rw [factor_2_5]; decide
      have factor_2_7 : (37 : ZMod 13385572201) ^ 159 = 828290915 := by
        calc
          (37 : ZMod 13385572201) ^ 159 = (37 : ZMod 13385572201) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 79 * (37 : ZMod 13385572201) ^ 79) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 828290915 := by rw [factor_2_6]; decide
      have factor_2_8 : (37 : ZMod 13385572201) ^ 319 = 9091202565 := by
        calc
          (37 : ZMod 13385572201) ^ 319 = (37 : ZMod 13385572201) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 159 * (37 : ZMod 13385572201) ^ 159) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9091202565 := by rw [factor_2_7]; decide
      have factor_2_9 : (37 : ZMod 13385572201) ^ 638 = 1590599305 := by
        calc
          (37 : ZMod 13385572201) ^ 638 = (37 : ZMod 13385572201) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 319 * (37 : ZMod 13385572201) ^ 319 := by rw [pow_add]
          _ = 1590599305 := by rw [factor_2_8]; decide
      have factor_2_10 : (37 : ZMod 13385572201) ^ 1276 = 4032093889 := by
        calc
          (37 : ZMod 13385572201) ^ 1276 = (37 : ZMod 13385572201) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 638 * (37 : ZMod 13385572201) ^ 638 := by rw [pow_add]
          _ = 4032093889 := by rw [factor_2_9]; decide
      have factor_2_11 : (37 : ZMod 13385572201) ^ 2553 = 5586262703 := by
        calc
          (37 : ZMod 13385572201) ^ 2553 = (37 : ZMod 13385572201) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1276 * (37 : ZMod 13385572201) ^ 1276) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5586262703 := by rw [factor_2_10]; decide
      have factor_2_12 : (37 : ZMod 13385572201) ^ 5106 = 8595743781 := by
        calc
          (37 : ZMod 13385572201) ^ 5106 = (37 : ZMod 13385572201) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 2553 * (37 : ZMod 13385572201) ^ 2553 := by rw [pow_add]
          _ = 8595743781 := by rw [factor_2_11]; decide
      have factor_2_13 : (37 : ZMod 13385572201) ^ 10212 = 11383328164 := by
        calc
          (37 : ZMod 13385572201) ^ 10212 = (37 : ZMod 13385572201) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 5106 * (37 : ZMod 13385572201) ^ 5106 := by rw [pow_add]
          _ = 11383328164 := by rw [factor_2_12]; decide
      have factor_2_14 : (37 : ZMod 13385572201) ^ 20424 = 7184138797 := by
        calc
          (37 : ZMod 13385572201) ^ 20424 = (37 : ZMod 13385572201) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 10212 * (37 : ZMod 13385572201) ^ 10212 := by rw [pow_add]
          _ = 7184138797 := by rw [factor_2_13]; decide
      have factor_2_15 : (37 : ZMod 13385572201) ^ 40849 = 1705099875 := by
        calc
          (37 : ZMod 13385572201) ^ 40849 = (37 : ZMod 13385572201) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 20424 * (37 : ZMod 13385572201) ^ 20424) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1705099875 := by rw [factor_2_14]; decide
      have factor_2_16 : (37 : ZMod 13385572201) ^ 81699 = 1275538172 := by
        calc
          (37 : ZMod 13385572201) ^ 81699 = (37 : ZMod 13385572201) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 40849 * (37 : ZMod 13385572201) ^ 40849) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1275538172 := by rw [factor_2_15]; decide
      have factor_2_17 : (37 : ZMod 13385572201) ^ 163398 = 70771979 := by
        calc
          (37 : ZMod 13385572201) ^ 163398 = (37 : ZMod 13385572201) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 81699 * (37 : ZMod 13385572201) ^ 81699 := by rw [pow_add]
          _ = 70771979 := by rw [factor_2_16]; decide
      have factor_2_18 : (37 : ZMod 13385572201) ^ 326796 = 6063117457 := by
        calc
          (37 : ZMod 13385572201) ^ 326796 = (37 : ZMod 13385572201) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 163398 * (37 : ZMod 13385572201) ^ 163398 := by rw [pow_add]
          _ = 6063117457 := by rw [factor_2_17]; decide
      have factor_2_19 : (37 : ZMod 13385572201) ^ 653592 = 7759147897 := by
        calc
          (37 : ZMod 13385572201) ^ 653592 = (37 : ZMod 13385572201) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 326796 * (37 : ZMod 13385572201) ^ 326796 := by rw [pow_add]
          _ = 7759147897 := by rw [factor_2_18]; decide
      have factor_2_20 : (37 : ZMod 13385572201) ^ 1307184 = 2330173235 := by
        calc
          (37 : ZMod 13385572201) ^ 1307184 = (37 : ZMod 13385572201) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 653592 * (37 : ZMod 13385572201) ^ 653592 := by rw [pow_add]
          _ = 2330173235 := by rw [factor_2_19]; decide
      have factor_2_21 : (37 : ZMod 13385572201) ^ 2614369 = 7000999512 := by
        calc
          (37 : ZMod 13385572201) ^ 2614369 = (37 : ZMod 13385572201) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1307184 * (37 : ZMod 13385572201) ^ 1307184) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7000999512 := by rw [factor_2_20]; decide
      have factor_2_22 : (37 : ZMod 13385572201) ^ 5228739 = 12272601493 := by
        calc
          (37 : ZMod 13385572201) ^ 5228739 = (37 : ZMod 13385572201) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 2614369 * (37 : ZMod 13385572201) ^ 2614369) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 12272601493 := by rw [factor_2_21]; decide
      have factor_2_23 : (37 : ZMod 13385572201) ^ 10457478 = 559597044 := by
        calc
          (37 : ZMod 13385572201) ^ 10457478 = (37 : ZMod 13385572201) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 5228739 * (37 : ZMod 13385572201) ^ 5228739 := by rw [pow_add]
          _ = 559597044 := by rw [factor_2_22]; decide
      have factor_2_24 : (37 : ZMod 13385572201) ^ 20914956 = 2483810230 := by
        calc
          (37 : ZMod 13385572201) ^ 20914956 = (37 : ZMod 13385572201) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 10457478 * (37 : ZMod 13385572201) ^ 10457478 := by rw [pow_add]
          _ = 2483810230 := by rw [factor_2_23]; decide
      have factor_2_25 : (37 : ZMod 13385572201) ^ 41829913 = 10222041139 := by
        calc
          (37 : ZMod 13385572201) ^ 41829913 = (37 : ZMod 13385572201) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 20914956 * (37 : ZMod 13385572201) ^ 20914956) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 10222041139 := by rw [factor_2_24]; decide
      have factor_2_26 : (37 : ZMod 13385572201) ^ 83659826 = 1302040675 := by
        calc
          (37 : ZMod 13385572201) ^ 83659826 = (37 : ZMod 13385572201) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 41829913 * (37 : ZMod 13385572201) ^ 41829913 := by rw [pow_add]
          _ = 1302040675 := by rw [factor_2_25]; decide
      have factor_2_27 : (37 : ZMod 13385572201) ^ 167319652 = 615093193 := by
        calc
          (37 : ZMod 13385572201) ^ 167319652 = (37 : ZMod 13385572201) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 83659826 * (37 : ZMod 13385572201) ^ 83659826 := by rw [pow_add]
          _ = 615093193 := by rw [factor_2_26]; decide
      have factor_2_28 : (37 : ZMod 13385572201) ^ 334639305 = 6835262460 := by
        calc
          (37 : ZMod 13385572201) ^ 334639305 = (37 : ZMod 13385572201) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 167319652 * (37 : ZMod 13385572201) ^ 167319652) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 6835262460 := by rw [factor_2_27]; decide
      have factor_2_29 : (37 : ZMod 13385572201) ^ 669278610 = 8330147469 := by
        calc
          (37 : ZMod 13385572201) ^ 669278610 = (37 : ZMod 13385572201) ^ (334639305 + 334639305) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 334639305 * (37 : ZMod 13385572201) ^ 334639305 := by rw [pow_add]
          _ = 8330147469 := by rw [factor_2_28]; decide
      have factor_2_30 : (37 : ZMod 13385572201) ^ 1338557220 = 3332906630 := by
        calc
          (37 : ZMod 13385572201) ^ 1338557220 = (37 : ZMod 13385572201) ^ (669278610 + 669278610) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 669278610 * (37 : ZMod 13385572201) ^ 669278610 := by rw [pow_add]
          _ = 3332906630 := by rw [factor_2_29]; decide
      have factor_2_31 : (37 : ZMod 13385572201) ^ 2677114440 = 6232280260 := by
        calc
          (37 : ZMod 13385572201) ^ 2677114440 = (37 : ZMod 13385572201) ^ (1338557220 + 1338557220) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1338557220 * (37 : ZMod 13385572201) ^ 1338557220 := by rw [pow_add]
          _ = 6232280260 := by rw [factor_2_30]; decide
      change (37 : ZMod 13385572201) ^ 2677114440 ≠ 1
      rw [factor_2_31]
      decide
    ·
      have factor_3_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have factor_3_1 : (37 : ZMod 13385572201) ^ 3 = 50653 := by
        calc
          (37 : ZMod 13385572201) ^ 3 = (37 : ZMod 13385572201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_3_0]; decide
      have factor_3_2 : (37 : ZMod 13385572201) ^ 7 = 1232871726 := by
        calc
          (37 : ZMod 13385572201) ^ 7 = (37 : ZMod 13385572201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 3 * (37 : ZMod 13385572201) ^ 3) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1232871726 := by rw [factor_3_1]; decide
      have factor_3_3 : (37 : ZMod 13385572201) ^ 14 = 9495734016 := by
        calc
          (37 : ZMod 13385572201) ^ 14 = (37 : ZMod 13385572201) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 7 * (37 : ZMod 13385572201) ^ 7 := by rw [pow_add]
          _ = 9495734016 := by rw [factor_3_2]; decide
      have factor_3_4 : (37 : ZMod 13385572201) ^ 28 = 1233367292 := by
        calc
          (37 : ZMod 13385572201) ^ 28 = (37 : ZMod 13385572201) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 14 * (37 : ZMod 13385572201) ^ 14 := by rw [pow_add]
          _ = 1233367292 := by rw [factor_3_3]; decide
      have factor_3_5 : (37 : ZMod 13385572201) ^ 56 = 10645543698 := by
        calc
          (37 : ZMod 13385572201) ^ 56 = (37 : ZMod 13385572201) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 28 * (37 : ZMod 13385572201) ^ 28 := by rw [pow_add]
          _ = 10645543698 := by rw [factor_3_4]; decide
      have factor_3_6 : (37 : ZMod 13385572201) ^ 113 = 3272751665 := by
        calc
          (37 : ZMod 13385572201) ^ 113 = (37 : ZMod 13385572201) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 56 * (37 : ZMod 13385572201) ^ 56) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3272751665 := by rw [factor_3_5]; decide
      have factor_3_7 : (37 : ZMod 13385572201) ^ 227 = 13212485995 := by
        calc
          (37 : ZMod 13385572201) ^ 227 = (37 : ZMod 13385572201) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 113 * (37 : ZMod 13385572201) ^ 113) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 13212485995 := by rw [factor_3_6]; decide
      have factor_3_8 : (37 : ZMod 13385572201) ^ 455 = 8027583214 := by
        calc
          (37 : ZMod 13385572201) ^ 455 = (37 : ZMod 13385572201) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 227 * (37 : ZMod 13385572201) ^ 227) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 8027583214 := by rw [factor_3_7]; decide
      have factor_3_9 : (37 : ZMod 13385572201) ^ 911 = 3061577387 := by
        calc
          (37 : ZMod 13385572201) ^ 911 = (37 : ZMod 13385572201) ^ (455 + 455 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 455 * (37 : ZMod 13385572201) ^ 455) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3061577387 := by rw [factor_3_8]; decide
      have factor_3_10 : (37 : ZMod 13385572201) ^ 1823 = 8674282726 := by
        calc
          (37 : ZMod 13385572201) ^ 1823 = (37 : ZMod 13385572201) ^ (911 + 911 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 911 * (37 : ZMod 13385572201) ^ 911) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 8674282726 := by rw [factor_3_9]; decide
      have factor_3_11 : (37 : ZMod 13385572201) ^ 3647 = 10528790271 := by
        calc
          (37 : ZMod 13385572201) ^ 3647 = (37 : ZMod 13385572201) ^ (1823 + 1823 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1823 * (37 : ZMod 13385572201) ^ 1823) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 10528790271 := by rw [factor_3_10]; decide
      have factor_3_12 : (37 : ZMod 13385572201) ^ 7294 = 1375978234 := by
        calc
          (37 : ZMod 13385572201) ^ 7294 = (37 : ZMod 13385572201) ^ (3647 + 3647) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 3647 * (37 : ZMod 13385572201) ^ 3647 := by rw [pow_add]
          _ = 1375978234 := by rw [factor_3_11]; decide
      have factor_3_13 : (37 : ZMod 13385572201) ^ 14589 = 190903198 := by
        calc
          (37 : ZMod 13385572201) ^ 14589 = (37 : ZMod 13385572201) ^ (7294 + 7294 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 7294 * (37 : ZMod 13385572201) ^ 7294) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 190903198 := by rw [factor_3_12]; decide
      have factor_3_14 : (37 : ZMod 13385572201) ^ 29178 = 3637157569 := by
        calc
          (37 : ZMod 13385572201) ^ 29178 = (37 : ZMod 13385572201) ^ (14589 + 14589) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 14589 * (37 : ZMod 13385572201) ^ 14589 := by rw [pow_add]
          _ = 3637157569 := by rw [factor_3_13]; decide
      have factor_3_15 : (37 : ZMod 13385572201) ^ 58356 = 7684905985 := by
        calc
          (37 : ZMod 13385572201) ^ 58356 = (37 : ZMod 13385572201) ^ (29178 + 29178) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 29178 * (37 : ZMod 13385572201) ^ 29178 := by rw [pow_add]
          _ = 7684905985 := by rw [factor_3_14]; decide
      have factor_3_16 : (37 : ZMod 13385572201) ^ 116712 = 7593294353 := by
        calc
          (37 : ZMod 13385572201) ^ 116712 = (37 : ZMod 13385572201) ^ (58356 + 58356) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 58356 * (37 : ZMod 13385572201) ^ 58356 := by rw [pow_add]
          _ = 7593294353 := by rw [factor_3_15]; decide
      have factor_3_17 : (37 : ZMod 13385572201) ^ 233425 = 2469014129 := by
        calc
          (37 : ZMod 13385572201) ^ 233425 = (37 : ZMod 13385572201) ^ (116712 + 116712 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 116712 * (37 : ZMod 13385572201) ^ 116712) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 2469014129 := by rw [factor_3_16]; decide
      have factor_3_18 : (37 : ZMod 13385572201) ^ 466851 = 1076491630 := by
        calc
          (37 : ZMod 13385572201) ^ 466851 = (37 : ZMod 13385572201) ^ (233425 + 233425 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 233425 * (37 : ZMod 13385572201) ^ 233425) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1076491630 := by rw [factor_3_17]; decide
      have factor_3_19 : (37 : ZMod 13385572201) ^ 933703 = 2290413838 := by
        calc
          (37 : ZMod 13385572201) ^ 933703 = (37 : ZMod 13385572201) ^ (466851 + 466851 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 466851 * (37 : ZMod 13385572201) ^ 466851) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 2290413838 := by rw [factor_3_18]; decide
      have factor_3_20 : (37 : ZMod 13385572201) ^ 1867406 = 9701752265 := by
        calc
          (37 : ZMod 13385572201) ^ 1867406 = (37 : ZMod 13385572201) ^ (933703 + 933703) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 933703 * (37 : ZMod 13385572201) ^ 933703 := by rw [pow_add]
          _ = 9701752265 := by rw [factor_3_19]; decide
      have factor_3_21 : (37 : ZMod 13385572201) ^ 3734813 = 12788094391 := by
        calc
          (37 : ZMod 13385572201) ^ 3734813 = (37 : ZMod 13385572201) ^ (1867406 + 1867406 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1867406 * (37 : ZMod 13385572201) ^ 1867406) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 12788094391 := by rw [factor_3_20]; decide
      have factor_3_22 : (37 : ZMod 13385572201) ^ 7469627 = 11250641754 := by
        calc
          (37 : ZMod 13385572201) ^ 7469627 = (37 : ZMod 13385572201) ^ (3734813 + 3734813 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 3734813 * (37 : ZMod 13385572201) ^ 3734813) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 11250641754 := by rw [factor_3_21]; decide
      have factor_3_23 : (37 : ZMod 13385572201) ^ 14939254 = 10108859500 := by
        calc
          (37 : ZMod 13385572201) ^ 14939254 = (37 : ZMod 13385572201) ^ (7469627 + 7469627) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 7469627 * (37 : ZMod 13385572201) ^ 7469627 := by rw [pow_add]
          _ = 10108859500 := by rw [factor_3_22]; decide
      have factor_3_24 : (37 : ZMod 13385572201) ^ 29878509 = 6787505567 := by
        calc
          (37 : ZMod 13385572201) ^ 29878509 = (37 : ZMod 13385572201) ^ (14939254 + 14939254 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 14939254 * (37 : ZMod 13385572201) ^ 14939254) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 6787505567 := by rw [factor_3_23]; decide
      have factor_3_25 : (37 : ZMod 13385572201) ^ 59757018 = 520925915 := by
        calc
          (37 : ZMod 13385572201) ^ 59757018 = (37 : ZMod 13385572201) ^ (29878509 + 29878509) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 29878509 * (37 : ZMod 13385572201) ^ 29878509 := by rw [pow_add]
          _ = 520925915 := by rw [factor_3_24]; decide
      have factor_3_26 : (37 : ZMod 13385572201) ^ 119514037 = 3614903967 := by
        calc
          (37 : ZMod 13385572201) ^ 119514037 = (37 : ZMod 13385572201) ^ (59757018 + 59757018 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 59757018 * (37 : ZMod 13385572201) ^ 59757018) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3614903967 := by rw [factor_3_25]; decide
      have factor_3_27 : (37 : ZMod 13385572201) ^ 239028075 = 8572979364 := by
        calc
          (37 : ZMod 13385572201) ^ 239028075 = (37 : ZMod 13385572201) ^ (119514037 + 119514037 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 119514037 * (37 : ZMod 13385572201) ^ 119514037) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 8572979364 := by rw [factor_3_26]; decide
      have factor_3_28 : (37 : ZMod 13385572201) ^ 478056150 = 4535027200 := by
        calc
          (37 : ZMod 13385572201) ^ 478056150 = (37 : ZMod 13385572201) ^ (239028075 + 239028075) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 239028075 * (37 : ZMod 13385572201) ^ 239028075 := by rw [pow_add]
          _ = 4535027200 := by rw [factor_3_27]; decide
      have factor_3_29 : (37 : ZMod 13385572201) ^ 956112300 = 13092027365 := by
        calc
          (37 : ZMod 13385572201) ^ 956112300 = (37 : ZMod 13385572201) ^ (478056150 + 478056150) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 478056150 * (37 : ZMod 13385572201) ^ 478056150 := by rw [pow_add]
          _ = 13092027365 := by rw [factor_3_28]; decide
      have factor_3_30 : (37 : ZMod 13385572201) ^ 1912224600 = 7158533275 := by
        calc
          (37 : ZMod 13385572201) ^ 1912224600 = (37 : ZMod 13385572201) ^ (956112300 + 956112300) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 956112300 * (37 : ZMod 13385572201) ^ 956112300 := by rw [pow_add]
          _ = 7158533275 := by rw [factor_3_29]; decide
      change (37 : ZMod 13385572201) ^ 1912224600 ≠ 1
      rw [factor_3_30]
      decide
    ·
      have factor_4_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have factor_4_1 : (37 : ZMod 13385572201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 13385572201) ^ 2 = (37 : ZMod 13385572201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_4_0]; decide
      have factor_4_2 : (37 : ZMod 13385572201) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 13385572201) ^ 4 = (37 : ZMod 13385572201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 2 * (37 : ZMod 13385572201) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_4_1]; decide
      have factor_4_3 : (37 : ZMod 13385572201) ^ 9 = 1219295568 := by
        calc
          (37 : ZMod 13385572201) ^ 9 = (37 : ZMod 13385572201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 4 * (37 : ZMod 13385572201) ^ 4) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1219295568 := by rw [factor_4_2]; decide
      have factor_4_4 : (37 : ZMod 13385572201) ^ 18 = 1165192845 := by
        calc
          (37 : ZMod 13385572201) ^ 18 = (37 : ZMod 13385572201) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 9 * (37 : ZMod 13385572201) ^ 9 := by rw [pow_add]
          _ = 1165192845 := by rw [factor_4_3]; decide
      have factor_4_5 : (37 : ZMod 13385572201) ^ 36 = 5577447835 := by
        calc
          (37 : ZMod 13385572201) ^ 36 = (37 : ZMod 13385572201) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 18 * (37 : ZMod 13385572201) ^ 18 := by rw [pow_add]
          _ = 5577447835 := by rw [factor_4_4]; decide
      have factor_4_6 : (37 : ZMod 13385572201) ^ 72 = 4649723291 := by
        calc
          (37 : ZMod 13385572201) ^ 72 = (37 : ZMod 13385572201) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 36 * (37 : ZMod 13385572201) ^ 36 := by rw [pow_add]
          _ = 4649723291 := by rw [factor_4_5]; decide
      have factor_4_7 : (37 : ZMod 13385572201) ^ 145 = 6157916792 := by
        calc
          (37 : ZMod 13385572201) ^ 145 = (37 : ZMod 13385572201) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 72 * (37 : ZMod 13385572201) ^ 72) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 6157916792 := by rw [factor_4_6]; decide
      have factor_4_8 : (37 : ZMod 13385572201) ^ 290 = 10741600271 := by
        calc
          (37 : ZMod 13385572201) ^ 290 = (37 : ZMod 13385572201) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 145 * (37 : ZMod 13385572201) ^ 145 := by rw [pow_add]
          _ = 10741600271 := by rw [factor_4_7]; decide
      have factor_4_9 : (37 : ZMod 13385572201) ^ 580 = 5392120156 := by
        calc
          (37 : ZMod 13385572201) ^ 580 = (37 : ZMod 13385572201) ^ (290 + 290) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 290 * (37 : ZMod 13385572201) ^ 290 := by rw [pow_add]
          _ = 5392120156 := by rw [factor_4_8]; decide
      have factor_4_10 : (37 : ZMod 13385572201) ^ 1160 = 7473509903 := by
        calc
          (37 : ZMod 13385572201) ^ 1160 = (37 : ZMod 13385572201) ^ (580 + 580) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 580 * (37 : ZMod 13385572201) ^ 580 := by rw [pow_add]
          _ = 7473509903 := by rw [factor_4_9]; decide
      have factor_4_11 : (37 : ZMod 13385572201) ^ 2320 = 6858114440 := by
        calc
          (37 : ZMod 13385572201) ^ 2320 = (37 : ZMod 13385572201) ^ (1160 + 1160) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1160 * (37 : ZMod 13385572201) ^ 1160 := by rw [pow_add]
          _ = 6858114440 := by rw [factor_4_10]; decide
      have factor_4_12 : (37 : ZMod 13385572201) ^ 4641 = 4560174244 := by
        calc
          (37 : ZMod 13385572201) ^ 4641 = (37 : ZMod 13385572201) ^ (2320 + 2320 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 2320 * (37 : ZMod 13385572201) ^ 2320) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4560174244 := by rw [factor_4_11]; decide
      have factor_4_13 : (37 : ZMod 13385572201) ^ 9283 = 7084764191 := by
        calc
          (37 : ZMod 13385572201) ^ 9283 = (37 : ZMod 13385572201) ^ (4641 + 4641 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 4641 * (37 : ZMod 13385572201) ^ 4641) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7084764191 := by rw [factor_4_12]; decide
      have factor_4_14 : (37 : ZMod 13385572201) ^ 18567 = 11236691617 := by
        calc
          (37 : ZMod 13385572201) ^ 18567 = (37 : ZMod 13385572201) ^ (9283 + 9283 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 9283 * (37 : ZMod 13385572201) ^ 9283) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 11236691617 := by rw [factor_4_13]; decide
      have factor_4_15 : (37 : ZMod 13385572201) ^ 37135 = 1500779288 := by
        calc
          (37 : ZMod 13385572201) ^ 37135 = (37 : ZMod 13385572201) ^ (18567 + 18567 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 18567 * (37 : ZMod 13385572201) ^ 18567) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1500779288 := by rw [factor_4_14]; decide
      have factor_4_16 : (37 : ZMod 13385572201) ^ 74271 = 4459790410 := by
        calc
          (37 : ZMod 13385572201) ^ 74271 = (37 : ZMod 13385572201) ^ (37135 + 37135 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 37135 * (37 : ZMod 13385572201) ^ 37135) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4459790410 := by rw [factor_4_15]; decide
      have factor_4_17 : (37 : ZMod 13385572201) ^ 148543 = 4443144648 := by
        calc
          (37 : ZMod 13385572201) ^ 148543 = (37 : ZMod 13385572201) ^ (74271 + 74271 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 74271 * (37 : ZMod 13385572201) ^ 74271) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4443144648 := by rw [factor_4_16]; decide
      have factor_4_18 : (37 : ZMod 13385572201) ^ 297087 = 4778230947 := by
        calc
          (37 : ZMod 13385572201) ^ 297087 = (37 : ZMod 13385572201) ^ (148543 + 148543 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 148543 * (37 : ZMod 13385572201) ^ 148543) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4778230947 := by rw [factor_4_17]; decide
      have factor_4_19 : (37 : ZMod 13385572201) ^ 594174 = 10527090292 := by
        calc
          (37 : ZMod 13385572201) ^ 594174 = (37 : ZMod 13385572201) ^ (297087 + 297087) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 297087 * (37 : ZMod 13385572201) ^ 297087 := by rw [pow_add]
          _ = 10527090292 := by rw [factor_4_18]; decide
      have factor_4_20 : (37 : ZMod 13385572201) ^ 1188349 = 7780790148 := by
        calc
          (37 : ZMod 13385572201) ^ 1188349 = (37 : ZMod 13385572201) ^ (594174 + 594174 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 594174 * (37 : ZMod 13385572201) ^ 594174) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7780790148 := by rw [factor_4_19]; decide
      have factor_4_21 : (37 : ZMod 13385572201) ^ 2376699 = 10956661779 := by
        calc
          (37 : ZMod 13385572201) ^ 2376699 = (37 : ZMod 13385572201) ^ (1188349 + 1188349 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1188349 * (37 : ZMod 13385572201) ^ 1188349) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 10956661779 := by rw [factor_4_20]; decide
      have factor_4_22 : (37 : ZMod 13385572201) ^ 4753399 = 11795181966 := by
        calc
          (37 : ZMod 13385572201) ^ 4753399 = (37 : ZMod 13385572201) ^ (2376699 + 2376699 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 2376699 * (37 : ZMod 13385572201) ^ 2376699) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 11795181966 := by rw [factor_4_21]; decide
      have factor_4_23 : (37 : ZMod 13385572201) ^ 9506798 = 3318200573 := by
        calc
          (37 : ZMod 13385572201) ^ 9506798 = (37 : ZMod 13385572201) ^ (4753399 + 4753399) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 4753399 * (37 : ZMod 13385572201) ^ 4753399 := by rw [pow_add]
          _ = 3318200573 := by rw [factor_4_22]; decide
      have factor_4_24 : (37 : ZMod 13385572201) ^ 19013596 = 6430742527 := by
        calc
          (37 : ZMod 13385572201) ^ 19013596 = (37 : ZMod 13385572201) ^ (9506798 + 9506798) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 9506798 * (37 : ZMod 13385572201) ^ 9506798 := by rw [pow_add]
          _ = 6430742527 := by rw [factor_4_23]; decide
      have factor_4_25 : (37 : ZMod 13385572201) ^ 38027193 = 3340586915 := by
        calc
          (37 : ZMod 13385572201) ^ 38027193 = (37 : ZMod 13385572201) ^ (19013596 + 19013596 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 19013596 * (37 : ZMod 13385572201) ^ 19013596) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3340586915 := by rw [factor_4_24]; decide
      have factor_4_26 : (37 : ZMod 13385572201) ^ 76054387 = 2684630729 := by
        calc
          (37 : ZMod 13385572201) ^ 76054387 = (37 : ZMod 13385572201) ^ (38027193 + 38027193 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 38027193 * (37 : ZMod 13385572201) ^ 38027193) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 2684630729 := by rw [factor_4_25]; decide
      have factor_4_27 : (37 : ZMod 13385572201) ^ 152108775 = 5398156825 := by
        calc
          (37 : ZMod 13385572201) ^ 152108775 = (37 : ZMod 13385572201) ^ (76054387 + 76054387 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 76054387 * (37 : ZMod 13385572201) ^ 76054387) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5398156825 := by rw [factor_4_26]; decide
      have factor_4_28 : (37 : ZMod 13385572201) ^ 304217550 = 11472165158 := by
        calc
          (37 : ZMod 13385572201) ^ 304217550 = (37 : ZMod 13385572201) ^ (152108775 + 152108775) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 152108775 * (37 : ZMod 13385572201) ^ 152108775 := by rw [pow_add]
          _ = 11472165158 := by rw [factor_4_27]; decide
      have factor_4_29 : (37 : ZMod 13385572201) ^ 608435100 = 1973977361 := by
        calc
          (37 : ZMod 13385572201) ^ 608435100 = (37 : ZMod 13385572201) ^ (304217550 + 304217550) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 304217550 * (37 : ZMod 13385572201) ^ 304217550 := by rw [pow_add]
          _ = 1973977361 := by rw [factor_4_28]; decide
      have factor_4_30 : (37 : ZMod 13385572201) ^ 1216870200 = 12394881444 := by
        calc
          (37 : ZMod 13385572201) ^ 1216870200 = (37 : ZMod 13385572201) ^ (608435100 + 608435100) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 608435100 * (37 : ZMod 13385572201) ^ 608435100 := by rw [pow_add]
          _ = 12394881444 := by rw [factor_4_29]; decide
      change (37 : ZMod 13385572201) ^ 1216870200 ≠ 1
      rw [factor_4_30]
      decide
    ·
      have factor_5_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have factor_5_1 : (37 : ZMod 13385572201) ^ 3 = 50653 := by
        calc
          (37 : ZMod 13385572201) ^ 3 = (37 : ZMod 13385572201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_5_0]; decide
      have factor_5_2 : (37 : ZMod 13385572201) ^ 7 = 1232871726 := by
        calc
          (37 : ZMod 13385572201) ^ 7 = (37 : ZMod 13385572201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 3 * (37 : ZMod 13385572201) ^ 3) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1232871726 := by rw [factor_5_1]; decide
      have factor_5_3 : (37 : ZMod 13385572201) ^ 15 = 3317281366 := by
        calc
          (37 : ZMod 13385572201) ^ 15 = (37 : ZMod 13385572201) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 7 * (37 : ZMod 13385572201) ^ 7) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3317281366 := by rw [factor_5_2]; decide
      have factor_5_4 : (37 : ZMod 13385572201) ^ 30 = 1897725422 := by
        calc
          (37 : ZMod 13385572201) ^ 30 = (37 : ZMod 13385572201) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 15 * (37 : ZMod 13385572201) ^ 15 := by rw [pow_add]
          _ = 1897725422 := by rw [factor_5_3]; decide
      have factor_5_5 : (37 : ZMod 13385572201) ^ 61 = 3971027947 := by
        calc
          (37 : ZMod 13385572201) ^ 61 = (37 : ZMod 13385572201) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 30 * (37 : ZMod 13385572201) ^ 30) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3971027947 := by rw [factor_5_4]; decide
      have factor_5_6 : (37 : ZMod 13385572201) ^ 122 = 4451185443 := by
        calc
          (37 : ZMod 13385572201) ^ 122 = (37 : ZMod 13385572201) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 61 * (37 : ZMod 13385572201) ^ 61 := by rw [pow_add]
          _ = 4451185443 := by rw [factor_5_5]; decide
      have factor_5_7 : (37 : ZMod 13385572201) ^ 245 = 1284406810 := by
        calc
          (37 : ZMod 13385572201) ^ 245 = (37 : ZMod 13385572201) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 122 * (37 : ZMod 13385572201) ^ 122) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1284406810 := by rw [factor_5_6]; decide
      have factor_5_8 : (37 : ZMod 13385572201) ^ 490 = 9948219199 := by
        calc
          (37 : ZMod 13385572201) ^ 490 = (37 : ZMod 13385572201) ^ (245 + 245) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 245 * (37 : ZMod 13385572201) ^ 245 := by rw [pow_add]
          _ = 9948219199 := by rw [factor_5_7]; decide
      have factor_5_9 : (37 : ZMod 13385572201) ^ 981 = 9978940976 := by
        calc
          (37 : ZMod 13385572201) ^ 981 = (37 : ZMod 13385572201) ^ (490 + 490 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 490 * (37 : ZMod 13385572201) ^ 490) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9978940976 := by rw [factor_5_8]; decide
      have factor_5_10 : (37 : ZMod 13385572201) ^ 1963 = 12504959206 := by
        calc
          (37 : ZMod 13385572201) ^ 1963 = (37 : ZMod 13385572201) ^ (981 + 981 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 981 * (37 : ZMod 13385572201) ^ 981) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 12504959206 := by rw [factor_5_9]; decide
      have factor_5_11 : (37 : ZMod 13385572201) ^ 3927 = 6129942888 := by
        calc
          (37 : ZMod 13385572201) ^ 3927 = (37 : ZMod 13385572201) ^ (1963 + 1963 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1963 * (37 : ZMod 13385572201) ^ 1963) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 6129942888 := by rw [factor_5_10]; decide
      have factor_5_12 : (37 : ZMod 13385572201) ^ 7855 = 9403491989 := by
        calc
          (37 : ZMod 13385572201) ^ 7855 = (37 : ZMod 13385572201) ^ (3927 + 3927 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 3927 * (37 : ZMod 13385572201) ^ 3927) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9403491989 := by rw [factor_5_11]; decide
      have factor_5_13 : (37 : ZMod 13385572201) ^ 15711 = 5108021402 := by
        calc
          (37 : ZMod 13385572201) ^ 15711 = (37 : ZMod 13385572201) ^ (7855 + 7855 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 7855 * (37 : ZMod 13385572201) ^ 7855) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5108021402 := by rw [factor_5_12]; decide
      have factor_5_14 : (37 : ZMod 13385572201) ^ 31422 = 11871134419 := by
        calc
          (37 : ZMod 13385572201) ^ 31422 = (37 : ZMod 13385572201) ^ (15711 + 15711) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 15711 * (37 : ZMod 13385572201) ^ 15711 := by rw [pow_add]
          _ = 11871134419 := by rw [factor_5_13]; decide
      have factor_5_15 : (37 : ZMod 13385572201) ^ 62845 = 8567538552 := by
        calc
          (37 : ZMod 13385572201) ^ 62845 = (37 : ZMod 13385572201) ^ (31422 + 31422 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 31422 * (37 : ZMod 13385572201) ^ 31422) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 8567538552 := by rw [factor_5_14]; decide
      have factor_5_16 : (37 : ZMod 13385572201) ^ 125690 = 7956010287 := by
        calc
          (37 : ZMod 13385572201) ^ 125690 = (37 : ZMod 13385572201) ^ (62845 + 62845) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 62845 * (37 : ZMod 13385572201) ^ 62845 := by rw [pow_add]
          _ = 7956010287 := by rw [factor_5_15]; decide
      have factor_5_17 : (37 : ZMod 13385572201) ^ 251381 = 10115975180 := by
        calc
          (37 : ZMod 13385572201) ^ 251381 = (37 : ZMod 13385572201) ^ (125690 + 125690 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 125690 * (37 : ZMod 13385572201) ^ 125690) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 10115975180 := by rw [factor_5_16]; decide
      have factor_5_18 : (37 : ZMod 13385572201) ^ 502763 = 2377953690 := by
        calc
          (37 : ZMod 13385572201) ^ 502763 = (37 : ZMod 13385572201) ^ (251381 + 251381 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 251381 * (37 : ZMod 13385572201) ^ 251381) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 2377953690 := by rw [factor_5_17]; decide
      have factor_5_19 : (37 : ZMod 13385572201) ^ 1005526 = 101847621 := by
        calc
          (37 : ZMod 13385572201) ^ 1005526 = (37 : ZMod 13385572201) ^ (502763 + 502763) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 502763 * (37 : ZMod 13385572201) ^ 502763 := by rw [pow_add]
          _ = 101847621 := by rw [factor_5_18]; decide
      have factor_5_20 : (37 : ZMod 13385572201) ^ 2011053 = 43368951 := by
        calc
          (37 : ZMod 13385572201) ^ 2011053 = (37 : ZMod 13385572201) ^ (1005526 + 1005526 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1005526 * (37 : ZMod 13385572201) ^ 1005526) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 43368951 := by rw [factor_5_19]; decide
      have factor_5_21 : (37 : ZMod 13385572201) ^ 4022107 = 7104213204 := by
        calc
          (37 : ZMod 13385572201) ^ 4022107 = (37 : ZMod 13385572201) ^ (2011053 + 2011053 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 2011053 * (37 : ZMod 13385572201) ^ 2011053) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7104213204 := by rw [factor_5_20]; decide
      have factor_5_22 : (37 : ZMod 13385572201) ^ 8044214 = 12061830189 := by
        calc
          (37 : ZMod 13385572201) ^ 8044214 = (37 : ZMod 13385572201) ^ (4022107 + 4022107) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 4022107 * (37 : ZMod 13385572201) ^ 4022107 := by rw [pow_add]
          _ = 12061830189 := by rw [factor_5_21]; decide
      have factor_5_23 : (37 : ZMod 13385572201) ^ 16088428 = 12384039667 := by
        calc
          (37 : ZMod 13385572201) ^ 16088428 = (37 : ZMod 13385572201) ^ (8044214 + 8044214) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 8044214 * (37 : ZMod 13385572201) ^ 8044214 := by rw [pow_add]
          _ = 12384039667 := by rw [factor_5_22]; decide
      have factor_5_24 : (37 : ZMod 13385572201) ^ 32176856 = 7457540495 := by
        calc
          (37 : ZMod 13385572201) ^ 32176856 = (37 : ZMod 13385572201) ^ (16088428 + 16088428) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 16088428 * (37 : ZMod 13385572201) ^ 16088428 := by rw [pow_add]
          _ = 7457540495 := by rw [factor_5_23]; decide
      have factor_5_25 : (37 : ZMod 13385572201) ^ 64353712 = 6541609668 := by
        calc
          (37 : ZMod 13385572201) ^ 64353712 = (37 : ZMod 13385572201) ^ (32176856 + 32176856) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 32176856 * (37 : ZMod 13385572201) ^ 32176856 := by rw [pow_add]
          _ = 6541609668 := by rw [factor_5_24]; decide
      have factor_5_26 : (37 : ZMod 13385572201) ^ 128707425 = 1379756218 := by
        calc
          (37 : ZMod 13385572201) ^ 128707425 = (37 : ZMod 13385572201) ^ (64353712 + 64353712 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 64353712 * (37 : ZMod 13385572201) ^ 64353712) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1379756218 := by rw [factor_5_25]; decide
      have factor_5_27 : (37 : ZMod 13385572201) ^ 257414850 = 7842503998 := by
        calc
          (37 : ZMod 13385572201) ^ 257414850 = (37 : ZMod 13385572201) ^ (128707425 + 128707425) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 128707425 * (37 : ZMod 13385572201) ^ 128707425 := by rw [pow_add]
          _ = 7842503998 := by rw [factor_5_26]; decide
      have factor_5_28 : (37 : ZMod 13385572201) ^ 514829700 = 4241035315 := by
        calc
          (37 : ZMod 13385572201) ^ 514829700 = (37 : ZMod 13385572201) ^ (257414850 + 257414850) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 257414850 * (37 : ZMod 13385572201) ^ 257414850 := by rw [pow_add]
          _ = 4241035315 := by rw [factor_5_27]; decide
      have factor_5_29 : (37 : ZMod 13385572201) ^ 1029659400 = 6137362642 := by
        calc
          (37 : ZMod 13385572201) ^ 1029659400 = (37 : ZMod 13385572201) ^ (514829700 + 514829700) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 514829700 * (37 : ZMod 13385572201) ^ 514829700 := by rw [pow_add]
          _ = 6137362642 := by rw [factor_5_28]; decide
      change (37 : ZMod 13385572201) ^ 1029659400 ≠ 1
      rw [factor_5_29]
      decide
    ·
      have factor_6_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have factor_6_1 : (37 : ZMod 13385572201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 13385572201) ^ 2 = (37 : ZMod 13385572201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_6_0]; decide
      have factor_6_2 : (37 : ZMod 13385572201) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 13385572201) ^ 5 = (37 : ZMod 13385572201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 2 * (37 : ZMod 13385572201) ^ 2) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_6_1]; decide
      have factor_6_3 : (37 : ZMod 13385572201) ^ 11 = 9404679668 := by
        calc
          (37 : ZMod 13385572201) ^ 11 = (37 : ZMod 13385572201) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 5 * (37 : ZMod 13385572201) ^ 5) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9404679668 := by rw [factor_6_2]; decide
      have factor_6_4 : (37 : ZMod 13385572201) ^ 23 = 7389363184 := by
        calc
          (37 : ZMod 13385572201) ^ 23 = (37 : ZMod 13385572201) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 11 * (37 : ZMod 13385572201) ^ 11) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7389363184 := by rw [factor_6_3]; decide
      have factor_6_5 : (37 : ZMod 13385572201) ^ 46 = 13075005673 := by
        calc
          (37 : ZMod 13385572201) ^ 46 = (37 : ZMod 13385572201) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 23 * (37 : ZMod 13385572201) ^ 23 := by rw [pow_add]
          _ = 13075005673 := by rw [factor_6_4]; decide
      have factor_6_6 : (37 : ZMod 13385572201) ^ 93 = 5417004056 := by
        calc
          (37 : ZMod 13385572201) ^ 93 = (37 : ZMod 13385572201) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 46 * (37 : ZMod 13385572201) ^ 46) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5417004056 := by rw [factor_6_5]; decide
      have factor_6_7 : (37 : ZMod 13385572201) ^ 187 = 12284715577 := by
        calc
          (37 : ZMod 13385572201) ^ 187 = (37 : ZMod 13385572201) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 93 * (37 : ZMod 13385572201) ^ 93) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 12284715577 := by rw [factor_6_6]; decide
      have factor_6_8 : (37 : ZMod 13385572201) ^ 375 = 7128883843 := by
        calc
          (37 : ZMod 13385572201) ^ 375 = (37 : ZMod 13385572201) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 187 * (37 : ZMod 13385572201) ^ 187) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7128883843 := by rw [factor_6_7]; decide
      have factor_6_9 : (37 : ZMod 13385572201) ^ 750 = 4982165929 := by
        calc
          (37 : ZMod 13385572201) ^ 750 = (37 : ZMod 13385572201) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 375 * (37 : ZMod 13385572201) ^ 375 := by rw [pow_add]
          _ = 4982165929 := by rw [factor_6_8]; decide
      have factor_6_10 : (37 : ZMod 13385572201) ^ 1501 = 10995773645 := by
        calc
          (37 : ZMod 13385572201) ^ 1501 = (37 : ZMod 13385572201) ^ (750 + 750 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 750 * (37 : ZMod 13385572201) ^ 750) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 10995773645 := by rw [factor_6_9]; decide
      have factor_6_11 : (37 : ZMod 13385572201) ^ 3003 = 2190087656 := by
        calc
          (37 : ZMod 13385572201) ^ 3003 = (37 : ZMod 13385572201) ^ (1501 + 1501 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1501 * (37 : ZMod 13385572201) ^ 1501) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 2190087656 := by rw [factor_6_10]; decide
      have factor_6_12 : (37 : ZMod 13385572201) ^ 6007 = 4999742382 := by
        calc
          (37 : ZMod 13385572201) ^ 6007 = (37 : ZMod 13385572201) ^ (3003 + 3003 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 3003 * (37 : ZMod 13385572201) ^ 3003) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4999742382 := by rw [factor_6_11]; decide
      have factor_6_13 : (37 : ZMod 13385572201) ^ 12014 = 10296163201 := by
        calc
          (37 : ZMod 13385572201) ^ 12014 = (37 : ZMod 13385572201) ^ (6007 + 6007) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 6007 * (37 : ZMod 13385572201) ^ 6007 := by rw [pow_add]
          _ = 10296163201 := by rw [factor_6_12]; decide
      have factor_6_14 : (37 : ZMod 13385572201) ^ 24029 = 4488444597 := by
        calc
          (37 : ZMod 13385572201) ^ 24029 = (37 : ZMod 13385572201) ^ (12014 + 12014 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 12014 * (37 : ZMod 13385572201) ^ 12014) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4488444597 := by rw [factor_6_13]; decide
      have factor_6_15 : (37 : ZMod 13385572201) ^ 48058 = 12242515803 := by
        calc
          (37 : ZMod 13385572201) ^ 48058 = (37 : ZMod 13385572201) ^ (24029 + 24029) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 24029 * (37 : ZMod 13385572201) ^ 24029 := by rw [pow_add]
          _ = 12242515803 := by rw [factor_6_14]; decide
      have factor_6_16 : (37 : ZMod 13385572201) ^ 96116 = 5441704891 := by
        calc
          (37 : ZMod 13385572201) ^ 96116 = (37 : ZMod 13385572201) ^ (48058 + 48058) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 48058 * (37 : ZMod 13385572201) ^ 48058 := by rw [pow_add]
          _ = 5441704891 := by rw [factor_6_15]; decide
      have factor_6_17 : (37 : ZMod 13385572201) ^ 192233 = 1317428878 := by
        calc
          (37 : ZMod 13385572201) ^ 192233 = (37 : ZMod 13385572201) ^ (96116 + 96116 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 96116 * (37 : ZMod 13385572201) ^ 96116) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1317428878 := by rw [factor_6_16]; decide
      have factor_6_18 : (37 : ZMod 13385572201) ^ 384466 = 5904478881 := by
        calc
          (37 : ZMod 13385572201) ^ 384466 = (37 : ZMod 13385572201) ^ (192233 + 192233) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 192233 * (37 : ZMod 13385572201) ^ 192233 := by rw [pow_add]
          _ = 5904478881 := by rw [factor_6_17]; decide
      have factor_6_19 : (37 : ZMod 13385572201) ^ 768932 = 856396900 := by
        calc
          (37 : ZMod 13385572201) ^ 768932 = (37 : ZMod 13385572201) ^ (384466 + 384466) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 384466 * (37 : ZMod 13385572201) ^ 384466 := by rw [pow_add]
          _ = 856396900 := by rw [factor_6_18]; decide
      have factor_6_20 : (37 : ZMod 13385572201) ^ 1537864 = 4150657495 := by
        calc
          (37 : ZMod 13385572201) ^ 1537864 = (37 : ZMod 13385572201) ^ (768932 + 768932) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 768932 * (37 : ZMod 13385572201) ^ 768932 := by rw [pow_add]
          _ = 4150657495 := by rw [factor_6_19]; decide
      have factor_6_21 : (37 : ZMod 13385572201) ^ 3075728 = 10664054172 := by
        calc
          (37 : ZMod 13385572201) ^ 3075728 = (37 : ZMod 13385572201) ^ (1537864 + 1537864) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1537864 * (37 : ZMod 13385572201) ^ 1537864 := by rw [pow_add]
          _ = 10664054172 := by rw [factor_6_20]; decide
      have factor_6_22 : (37 : ZMod 13385572201) ^ 6151457 = 3387939690 := by
        calc
          (37 : ZMod 13385572201) ^ 6151457 = (37 : ZMod 13385572201) ^ (3075728 + 3075728 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 3075728 * (37 : ZMod 13385572201) ^ 3075728) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3387939690 := by rw [factor_6_21]; decide
      have factor_6_23 : (37 : ZMod 13385572201) ^ 12302915 = 9795410252 := by
        calc
          (37 : ZMod 13385572201) ^ 12302915 = (37 : ZMod 13385572201) ^ (6151457 + 6151457 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 6151457 * (37 : ZMod 13385572201) ^ 6151457) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9795410252 := by rw [factor_6_22]; decide
      have factor_6_24 : (37 : ZMod 13385572201) ^ 24605831 = 4394661646 := by
        calc
          (37 : ZMod 13385572201) ^ 24605831 = (37 : ZMod 13385572201) ^ (12302915 + 12302915 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 12302915 * (37 : ZMod 13385572201) ^ 12302915) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4394661646 := by rw [factor_6_23]; decide
      have factor_6_25 : (37 : ZMod 13385572201) ^ 49211662 = 2079724562 := by
        calc
          (37 : ZMod 13385572201) ^ 49211662 = (37 : ZMod 13385572201) ^ (24605831 + 24605831) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 24605831 * (37 : ZMod 13385572201) ^ 24605831 := by rw [pow_add]
          _ = 2079724562 := by rw [factor_6_24]; decide
      have factor_6_26 : (37 : ZMod 13385572201) ^ 98423325 = 3443014444 := by
        calc
          (37 : ZMod 13385572201) ^ 98423325 = (37 : ZMod 13385572201) ^ (49211662 + 49211662 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 49211662 * (37 : ZMod 13385572201) ^ 49211662) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3443014444 := by rw [factor_6_25]; decide
      have factor_6_27 : (37 : ZMod 13385572201) ^ 196846650 = 12568226133 := by
        calc
          (37 : ZMod 13385572201) ^ 196846650 = (37 : ZMod 13385572201) ^ (98423325 + 98423325) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 98423325 * (37 : ZMod 13385572201) ^ 98423325 := by rw [pow_add]
          _ = 12568226133 := by rw [factor_6_26]; decide
      have factor_6_28 : (37 : ZMod 13385572201) ^ 393693300 = 1703836667 := by
        calc
          (37 : ZMod 13385572201) ^ 393693300 = (37 : ZMod 13385572201) ^ (196846650 + 196846650) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 196846650 * (37 : ZMod 13385572201) ^ 196846650 := by rw [pow_add]
          _ = 1703836667 := by rw [factor_6_27]; decide
      have factor_6_29 : (37 : ZMod 13385572201) ^ 787386600 = 9266277752 := by
        calc
          (37 : ZMod 13385572201) ^ 787386600 = (37 : ZMod 13385572201) ^ (393693300 + 393693300) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 393693300 * (37 : ZMod 13385572201) ^ 393693300 := by rw [pow_add]
          _ = 9266277752 := by rw [factor_6_28]; decide
      change (37 : ZMod 13385572201) ^ 787386600 ≠ 1
      rw [factor_6_29]
      decide
    ·
      have factor_7_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have factor_7_1 : (37 : ZMod 13385572201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 13385572201) ^ 2 = (37 : ZMod 13385572201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_7_0]; decide
      have factor_7_2 : (37 : ZMod 13385572201) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 13385572201) ^ 5 = (37 : ZMod 13385572201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 2 * (37 : ZMod 13385572201) ^ 2) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_7_1]; decide
      have factor_7_3 : (37 : ZMod 13385572201) ^ 10 = 4957219413 := by
        calc
          (37 : ZMod 13385572201) ^ 10 = (37 : ZMod 13385572201) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 5 * (37 : ZMod 13385572201) ^ 5 := by rw [pow_add]
          _ = 4957219413 := by rw [factor_7_2]; decide
      have factor_7_4 : (37 : ZMod 13385572201) ^ 20 = 2265912886 := by
        calc
          (37 : ZMod 13385572201) ^ 20 = (37 : ZMod 13385572201) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 10 * (37 : ZMod 13385572201) ^ 10 := by rw [pow_add]
          _ = 2265912886 := by rw [factor_7_3]; decide
      have factor_7_5 : (37 : ZMod 13385572201) ^ 41 = 8002599527 := by
        calc
          (37 : ZMod 13385572201) ^ 41 = (37 : ZMod 13385572201) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 20 * (37 : ZMod 13385572201) ^ 20) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 8002599527 := by rw [factor_7_4]; decide
      have factor_7_6 : (37 : ZMod 13385572201) ^ 83 = 7852098119 := by
        calc
          (37 : ZMod 13385572201) ^ 83 = (37 : ZMod 13385572201) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 41 * (37 : ZMod 13385572201) ^ 41) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7852098119 := by rw [factor_7_5]; decide
      have factor_7_7 : (37 : ZMod 13385572201) ^ 167 = 3022436602 := by
        calc
          (37 : ZMod 13385572201) ^ 167 = (37 : ZMod 13385572201) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 83 * (37 : ZMod 13385572201) ^ 83) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3022436602 := by rw [factor_7_6]; decide
      have factor_7_8 : (37 : ZMod 13385572201) ^ 335 = 11844911998 := by
        calc
          (37 : ZMod 13385572201) ^ 335 = (37 : ZMod 13385572201) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 167 * (37 : ZMod 13385572201) ^ 167) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 11844911998 := by rw [factor_7_7]; decide
      have factor_7_9 : (37 : ZMod 13385572201) ^ 671 = 2510728311 := by
        calc
          (37 : ZMod 13385572201) ^ 671 = (37 : ZMod 13385572201) ^ (335 + 335 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 335 * (37 : ZMod 13385572201) ^ 335) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 2510728311 := by rw [factor_7_8]; decide
      have factor_7_10 : (37 : ZMod 13385572201) ^ 1343 = 5658189493 := by
        calc
          (37 : ZMod 13385572201) ^ 1343 = (37 : ZMod 13385572201) ^ (671 + 671 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 671 * (37 : ZMod 13385572201) ^ 671) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5658189493 := by rw [factor_7_9]; decide
      have factor_7_11 : (37 : ZMod 13385572201) ^ 2687 = 10184424687 := by
        calc
          (37 : ZMod 13385572201) ^ 2687 = (37 : ZMod 13385572201) ^ (1343 + 1343 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1343 * (37 : ZMod 13385572201) ^ 1343) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 10184424687 := by rw [factor_7_10]; decide
      have factor_7_12 : (37 : ZMod 13385572201) ^ 5374 = 7517212857 := by
        calc
          (37 : ZMod 13385572201) ^ 5374 = (37 : ZMod 13385572201) ^ (2687 + 2687) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 2687 * (37 : ZMod 13385572201) ^ 2687 := by rw [pow_add]
          _ = 7517212857 := by rw [factor_7_11]; decide
      have factor_7_13 : (37 : ZMod 13385572201) ^ 10749 = 12459404998 := by
        calc
          (37 : ZMod 13385572201) ^ 10749 = (37 : ZMod 13385572201) ^ (5374 + 5374 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 5374 * (37 : ZMod 13385572201) ^ 5374) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 12459404998 := by rw [factor_7_12]; decide
      have factor_7_14 : (37 : ZMod 13385572201) ^ 21499 = 1389203083 := by
        calc
          (37 : ZMod 13385572201) ^ 21499 = (37 : ZMod 13385572201) ^ (10749 + 10749 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 10749 * (37 : ZMod 13385572201) ^ 10749) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1389203083 := by rw [factor_7_13]; decide
      have factor_7_15 : (37 : ZMod 13385572201) ^ 42999 = 12203048688 := by
        calc
          (37 : ZMod 13385572201) ^ 42999 = (37 : ZMod 13385572201) ^ (21499 + 21499 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 21499 * (37 : ZMod 13385572201) ^ 21499) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 12203048688 := by rw [factor_7_14]; decide
      have factor_7_16 : (37 : ZMod 13385572201) ^ 85998 = 3638628726 := by
        calc
          (37 : ZMod 13385572201) ^ 85998 = (37 : ZMod 13385572201) ^ (42999 + 42999) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 42999 * (37 : ZMod 13385572201) ^ 42999 := by rw [pow_add]
          _ = 3638628726 := by rw [factor_7_15]; decide
      have factor_7_17 : (37 : ZMod 13385572201) ^ 171997 = 7609780488 := by
        calc
          (37 : ZMod 13385572201) ^ 171997 = (37 : ZMod 13385572201) ^ (85998 + 85998 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 85998 * (37 : ZMod 13385572201) ^ 85998) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7609780488 := by rw [factor_7_16]; decide
      have factor_7_18 : (37 : ZMod 13385572201) ^ 343995 = 12895905856 := by
        calc
          (37 : ZMod 13385572201) ^ 343995 = (37 : ZMod 13385572201) ^ (171997 + 171997 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 171997 * (37 : ZMod 13385572201) ^ 171997) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 12895905856 := by rw [factor_7_17]; decide
      have factor_7_19 : (37 : ZMod 13385572201) ^ 687991 = 12281437783 := by
        calc
          (37 : ZMod 13385572201) ^ 687991 = (37 : ZMod 13385572201) ^ (343995 + 343995 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 343995 * (37 : ZMod 13385572201) ^ 343995) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 12281437783 := by rw [factor_7_18]; decide
      have factor_7_20 : (37 : ZMod 13385572201) ^ 1375983 = 6412408061 := by
        calc
          (37 : ZMod 13385572201) ^ 1375983 = (37 : ZMod 13385572201) ^ (687991 + 687991 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 687991 * (37 : ZMod 13385572201) ^ 687991) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 6412408061 := by rw [factor_7_19]; decide
      have factor_7_21 : (37 : ZMod 13385572201) ^ 2751967 = 5420518159 := by
        calc
          (37 : ZMod 13385572201) ^ 2751967 = (37 : ZMod 13385572201) ^ (1375983 + 1375983 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 1375983 * (37 : ZMod 13385572201) ^ 1375983) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 5420518159 := by rw [factor_7_20]; decide
      have factor_7_22 : (37 : ZMod 13385572201) ^ 5503935 = 6292606415 := by
        calc
          (37 : ZMod 13385572201) ^ 5503935 = (37 : ZMod 13385572201) ^ (2751967 + 2751967 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 2751967 * (37 : ZMod 13385572201) ^ 2751967) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 6292606415 := by rw [factor_7_21]; decide
      have factor_7_23 : (37 : ZMod 13385572201) ^ 11007871 = 7722432361 := by
        calc
          (37 : ZMod 13385572201) ^ 11007871 = (37 : ZMod 13385572201) ^ (5503935 + 5503935 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 5503935 * (37 : ZMod 13385572201) ^ 5503935) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 7722432361 := by rw [factor_7_22]; decide
      have factor_7_24 : (37 : ZMod 13385572201) ^ 22015743 = 6288988112 := by
        calc
          (37 : ZMod 13385572201) ^ 22015743 = (37 : ZMod 13385572201) ^ (11007871 + 11007871 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 11007871 * (37 : ZMod 13385572201) ^ 11007871) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 6288988112 := by rw [factor_7_23]; decide
      have factor_7_25 : (37 : ZMod 13385572201) ^ 44031487 = 136668907 := by
        calc
          (37 : ZMod 13385572201) ^ 44031487 = (37 : ZMod 13385572201) ^ (22015743 + 22015743 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 22015743 * (37 : ZMod 13385572201) ^ 22015743) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 136668907 := by rw [factor_7_24]; decide
      have factor_7_26 : (37 : ZMod 13385572201) ^ 88062975 = 9456153964 := by
        calc
          (37 : ZMod 13385572201) ^ 88062975 = (37 : ZMod 13385572201) ^ (44031487 + 44031487 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 44031487 * (37 : ZMod 13385572201) ^ 44031487) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9456153964 := by rw [factor_7_25]; decide
      have factor_7_27 : (37 : ZMod 13385572201) ^ 176125950 = 7016354929 := by
        calc
          (37 : ZMod 13385572201) ^ 176125950 = (37 : ZMod 13385572201) ^ (88062975 + 88062975) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 88062975 * (37 : ZMod 13385572201) ^ 88062975 := by rw [pow_add]
          _ = 7016354929 := by rw [factor_7_26]; decide
      have factor_7_28 : (37 : ZMod 13385572201) ^ 352251900 = 4505116948 := by
        calc
          (37 : ZMod 13385572201) ^ 352251900 = (37 : ZMod 13385572201) ^ (176125950 + 176125950) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 176125950 * (37 : ZMod 13385572201) ^ 176125950 := by rw [pow_add]
          _ = 4505116948 := by rw [factor_7_27]; decide
      have factor_7_29 : (37 : ZMod 13385572201) ^ 704503800 = 12593620600 := by
        calc
          (37 : ZMod 13385572201) ^ 704503800 = (37 : ZMod 13385572201) ^ (352251900 + 352251900) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 352251900 * (37 : ZMod 13385572201) ^ 352251900 := by rw [pow_add]
          _ = 12593620600 := by rw [factor_7_28]; decide
      change (37 : ZMod 13385572201) ^ 704503800 ≠ 1
      rw [factor_7_29]
      decide
    ·
      have factor_8_0 : (37 : ZMod 13385572201) ^ 1 = 37 := by norm_num
      have factor_8_1 : (37 : ZMod 13385572201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 13385572201) ^ 2 = (37 : ZMod 13385572201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1 * (37 : ZMod 13385572201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_8_0]; decide
      have factor_8_2 : (37 : ZMod 13385572201) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 13385572201) ^ 4 = (37 : ZMod 13385572201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 2 * (37 : ZMod 13385572201) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_8_1]; decide
      have factor_8_3 : (37 : ZMod 13385572201) ^ 8 = 5459537259 := by
        calc
          (37 : ZMod 13385572201) ^ 8 = (37 : ZMod 13385572201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 4 * (37 : ZMod 13385572201) ^ 4 := by rw [pow_add]
          _ = 5459537259 := by rw [factor_8_2]; decide
      have factor_8_4 : (37 : ZMod 13385572201) ^ 17 = 3649213915 := by
        calc
          (37 : ZMod 13385572201) ^ 17 = (37 : ZMod 13385572201) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 8 * (37 : ZMod 13385572201) ^ 8) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3649213915 := by rw [factor_8_3]; decide
      have factor_8_5 : (37 : ZMod 13385572201) ^ 34 = 2741809835 := by
        calc
          (37 : ZMod 13385572201) ^ 34 = (37 : ZMod 13385572201) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 17 * (37 : ZMod 13385572201) ^ 17 := by rw [pow_add]
          _ = 2741809835 := by rw [factor_8_4]; decide
      have factor_8_6 : (37 : ZMod 13385572201) ^ 69 = 9006079607 := by
        calc
          (37 : ZMod 13385572201) ^ 69 = (37 : ZMod 13385572201) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 34 * (37 : ZMod 13385572201) ^ 34) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9006079607 := by rw [factor_8_5]; decide
      have factor_8_7 : (37 : ZMod 13385572201) ^ 138 = 9064138096 := by
        calc
          (37 : ZMod 13385572201) ^ 138 = (37 : ZMod 13385572201) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 69 * (37 : ZMod 13385572201) ^ 69 := by rw [pow_add]
          _ = 9064138096 := by rw [factor_8_6]; decide
      have factor_8_8 : (37 : ZMod 13385572201) ^ 277 = 4006067291 := by
        calc
          (37 : ZMod 13385572201) ^ 277 = (37 : ZMod 13385572201) ^ (138 + 138 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 138 * (37 : ZMod 13385572201) ^ 138) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 4006067291 := by rw [factor_8_7]; decide
      have factor_8_9 : (37 : ZMod 13385572201) ^ 555 = 9873860189 := by
        calc
          (37 : ZMod 13385572201) ^ 555 = (37 : ZMod 13385572201) ^ (277 + 277 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 277 * (37 : ZMod 13385572201) ^ 277) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9873860189 := by rw [factor_8_8]; decide
      have factor_8_10 : (37 : ZMod 13385572201) ^ 1110 = 11518444624 := by
        calc
          (37 : ZMod 13385572201) ^ 1110 = (37 : ZMod 13385572201) ^ (555 + 555) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 555 * (37 : ZMod 13385572201) ^ 555 := by rw [pow_add]
          _ = 11518444624 := by rw [factor_8_9]; decide
      have factor_8_11 : (37 : ZMod 13385572201) ^ 2220 = 6223038115 := by
        calc
          (37 : ZMod 13385572201) ^ 2220 = (37 : ZMod 13385572201) ^ (1110 + 1110) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1110 * (37 : ZMod 13385572201) ^ 1110 := by rw [pow_add]
          _ = 6223038115 := by rw [factor_8_10]; decide
      have factor_8_12 : (37 : ZMod 13385572201) ^ 4440 = 965600010 := by
        calc
          (37 : ZMod 13385572201) ^ 4440 = (37 : ZMod 13385572201) ^ (2220 + 2220) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 2220 * (37 : ZMod 13385572201) ^ 2220 := by rw [pow_add]
          _ = 965600010 := by rw [factor_8_11]; decide
      have factor_8_13 : (37 : ZMod 13385572201) ^ 8880 = 10071690853 := by
        calc
          (37 : ZMod 13385572201) ^ 8880 = (37 : ZMod 13385572201) ^ (4440 + 4440) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 4440 * (37 : ZMod 13385572201) ^ 4440 := by rw [pow_add]
          _ = 10071690853 := by rw [factor_8_12]; decide
      have factor_8_14 : (37 : ZMod 13385572201) ^ 17760 = 11544956327 := by
        calc
          (37 : ZMod 13385572201) ^ 17760 = (37 : ZMod 13385572201) ^ (8880 + 8880) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 8880 * (37 : ZMod 13385572201) ^ 8880 := by rw [pow_add]
          _ = 11544956327 := by rw [factor_8_13]; decide
      have factor_8_15 : (37 : ZMod 13385572201) ^ 35521 = 9280412721 := by
        calc
          (37 : ZMod 13385572201) ^ 35521 = (37 : ZMod 13385572201) ^ (17760 + 17760 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 17760 * (37 : ZMod 13385572201) ^ 17760) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9280412721 := by rw [factor_8_14]; decide
      have factor_8_16 : (37 : ZMod 13385572201) ^ 71042 = 2859415749 := by
        calc
          (37 : ZMod 13385572201) ^ 71042 = (37 : ZMod 13385572201) ^ (35521 + 35521) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 35521 * (37 : ZMod 13385572201) ^ 35521 := by rw [pow_add]
          _ = 2859415749 := by rw [factor_8_15]; decide
      have factor_8_17 : (37 : ZMod 13385572201) ^ 142085 = 1972249620 := by
        calc
          (37 : ZMod 13385572201) ^ 142085 = (37 : ZMod 13385572201) ^ (71042 + 71042 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 71042 * (37 : ZMod 13385572201) ^ 71042) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1972249620 := by rw [factor_8_16]; decide
      have factor_8_18 : (37 : ZMod 13385572201) ^ 284170 = 2529658481 := by
        calc
          (37 : ZMod 13385572201) ^ 284170 = (37 : ZMod 13385572201) ^ (142085 + 142085) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 142085 * (37 : ZMod 13385572201) ^ 142085 := by rw [pow_add]
          _ = 2529658481 := by rw [factor_8_17]; decide
      have factor_8_19 : (37 : ZMod 13385572201) ^ 568341 = 9916161225 := by
        calc
          (37 : ZMod 13385572201) ^ 568341 = (37 : ZMod 13385572201) ^ (284170 + 284170 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 284170 * (37 : ZMod 13385572201) ^ 284170) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 9916161225 := by rw [factor_8_18]; decide
      have factor_8_20 : (37 : ZMod 13385572201) ^ 1136682 = 9235302575 := by
        calc
          (37 : ZMod 13385572201) ^ 1136682 = (37 : ZMod 13385572201) ^ (568341 + 568341) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 568341 * (37 : ZMod 13385572201) ^ 568341 := by rw [pow_add]
          _ = 9235302575 := by rw [factor_8_19]; decide
      have factor_8_21 : (37 : ZMod 13385572201) ^ 2273364 = 10200782156 := by
        calc
          (37 : ZMod 13385572201) ^ 2273364 = (37 : ZMod 13385572201) ^ (1136682 + 1136682) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 1136682 * (37 : ZMod 13385572201) ^ 1136682 := by rw [pow_add]
          _ = 10200782156 := by rw [factor_8_20]; decide
      have factor_8_22 : (37 : ZMod 13385572201) ^ 4546729 = 6611876834 := by
        calc
          (37 : ZMod 13385572201) ^ 4546729 = (37 : ZMod 13385572201) ^ (2273364 + 2273364 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 2273364 * (37 : ZMod 13385572201) ^ 2273364) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 6611876834 := by rw [factor_8_21]; decide
      have factor_8_23 : (37 : ZMod 13385572201) ^ 9093459 = 3112870060 := by
        calc
          (37 : ZMod 13385572201) ^ 9093459 = (37 : ZMod 13385572201) ^ (4546729 + 4546729 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 4546729 * (37 : ZMod 13385572201) ^ 4546729) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3112870060 := by rw [factor_8_22]; decide
      have factor_8_24 : (37 : ZMod 13385572201) ^ 18186918 = 11057749021 := by
        calc
          (37 : ZMod 13385572201) ^ 18186918 = (37 : ZMod 13385572201) ^ (9093459 + 9093459) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 9093459 * (37 : ZMod 13385572201) ^ 9093459 := by rw [pow_add]
          _ = 11057749021 := by rw [factor_8_23]; decide
      have factor_8_25 : (37 : ZMod 13385572201) ^ 36373837 = 3006139308 := by
        calc
          (37 : ZMod 13385572201) ^ 36373837 = (37 : ZMod 13385572201) ^ (18186918 + 18186918 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 18186918 * (37 : ZMod 13385572201) ^ 18186918) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 3006139308 := by rw [factor_8_24]; decide
      have factor_8_26 : (37 : ZMod 13385572201) ^ 72747675 = 1523273087 := by
        calc
          (37 : ZMod 13385572201) ^ 72747675 = (37 : ZMod 13385572201) ^ (36373837 + 36373837 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = ((37 : ZMod 13385572201) ^ 36373837 * (37 : ZMod 13385572201) ^ 36373837) * (37 : ZMod 13385572201) := by rw [pow_succ, pow_add]
          _ = 1523273087 := by rw [factor_8_25]; decide
      have factor_8_27 : (37 : ZMod 13385572201) ^ 145495350 = 12694492865 := by
        calc
          (37 : ZMod 13385572201) ^ 145495350 = (37 : ZMod 13385572201) ^ (72747675 + 72747675) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 72747675 * (37 : ZMod 13385572201) ^ 72747675 := by rw [pow_add]
          _ = 12694492865 := by rw [factor_8_26]; decide
      have factor_8_28 : (37 : ZMod 13385572201) ^ 290990700 = 4830471587 := by
        calc
          (37 : ZMod 13385572201) ^ 290990700 = (37 : ZMod 13385572201) ^ (145495350 + 145495350) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 145495350 * (37 : ZMod 13385572201) ^ 145495350 := by rw [pow_add]
          _ = 4830471587 := by rw [factor_8_27]; decide
      have factor_8_29 : (37 : ZMod 13385572201) ^ 581981400 = 211464617 := by
        calc
          (37 : ZMod 13385572201) ^ 581981400 = (37 : ZMod 13385572201) ^ (290990700 + 290990700) :=
            congrArg (fun n : ℕ => (37 : ZMod 13385572201) ^ n) (by norm_num)
          _ = (37 : ZMod 13385572201) ^ 290990700 * (37 : ZMod 13385572201) ^ 290990700 := by rw [pow_add]
          _ = 211464617 := by rw [factor_8_28]; decide
      change (37 : ZMod 13385572201) ^ 581981400 ≠ 1
      rw [factor_8_29]
      decide

#print axioms prime_lucas_13385572201

end TotientTailPeriodKiller
end Erdos249257
