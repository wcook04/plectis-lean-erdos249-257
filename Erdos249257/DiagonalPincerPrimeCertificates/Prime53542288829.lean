import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_53542288829 : Nat.Prime 53542288829 := by
  apply lucas_primality 53542288829 (3 : ZMod 53542288829)
  ·
      have fermat_0 : (3 : ZMod 53542288829) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 53542288829) ^ 3 = 27 := by
        calc
          (3 : ZMod 53542288829) ^ 3 = (3 : ZMod 53542288829) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1 * (3 : ZMod 53542288829) ^ 1) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 53542288829) ^ 6 = 729 := by
        calc
          (3 : ZMod 53542288829) ^ 6 = (3 : ZMod 53542288829) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 3 * (3 : ZMod 53542288829) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 53542288829) ^ 12 = 531441 := by
        calc
          (3 : ZMod 53542288829) ^ 12 = (3 : ZMod 53542288829) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 6 * (3 : ZMod 53542288829) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 53542288829) ^ 24 = 14718092336 := by
        calc
          (3 : ZMod 53542288829) ^ 24 = (3 : ZMod 53542288829) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 12 * (3 : ZMod 53542288829) ^ 12 := by rw [pow_add]
          _ = 14718092336 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 53542288829) ^ 49 = 23251751366 := by
        calc
          (3 : ZMod 53542288829) ^ 49 = (3 : ZMod 53542288829) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 24 * (3 : ZMod 53542288829) ^ 24) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 23251751366 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 53542288829) ^ 99 = 16823402336 := by
        calc
          (3 : ZMod 53542288829) ^ 99 = (3 : ZMod 53542288829) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 49 * (3 : ZMod 53542288829) ^ 49) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 16823402336 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 53542288829) ^ 199 = 44334024943 := by
        calc
          (3 : ZMod 53542288829) ^ 199 = (3 : ZMod 53542288829) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 99 * (3 : ZMod 53542288829) ^ 99) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 44334024943 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 53542288829) ^ 398 = 5957634629 := by
        calc
          (3 : ZMod 53542288829) ^ 398 = (3 : ZMod 53542288829) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 199 * (3 : ZMod 53542288829) ^ 199 := by rw [pow_add]
          _ = 5957634629 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 53542288829) ^ 797 = 51664542727 := by
        calc
          (3 : ZMod 53542288829) ^ 797 = (3 : ZMod 53542288829) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 398 * (3 : ZMod 53542288829) ^ 398) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 51664542727 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 53542288829) ^ 1595 = 34109272656 := by
        calc
          (3 : ZMod 53542288829) ^ 1595 = (3 : ZMod 53542288829) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 797 * (3 : ZMod 53542288829) ^ 797) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 34109272656 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 53542288829) ^ 3191 = 47857687571 := by
        calc
          (3 : ZMod 53542288829) ^ 3191 = (3 : ZMod 53542288829) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1595 * (3 : ZMod 53542288829) ^ 1595) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 47857687571 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 53542288829) ^ 6382 = 20591696966 := by
        calc
          (3 : ZMod 53542288829) ^ 6382 = (3 : ZMod 53542288829) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 3191 * (3 : ZMod 53542288829) ^ 3191 := by rw [pow_add]
          _ = 20591696966 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 53542288829) ^ 12765 = 12661314111 := by
        calc
          (3 : ZMod 53542288829) ^ 12765 = (3 : ZMod 53542288829) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 6382 * (3 : ZMod 53542288829) ^ 6382) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 12661314111 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 53542288829) ^ 25530 = 38807947009 := by
        calc
          (3 : ZMod 53542288829) ^ 25530 = (3 : ZMod 53542288829) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 12765 * (3 : ZMod 53542288829) ^ 12765 := by rw [pow_add]
          _ = 38807947009 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 53542288829) ^ 51061 = 27009069828 := by
        calc
          (3 : ZMod 53542288829) ^ 51061 = (3 : ZMod 53542288829) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 25530 * (3 : ZMod 53542288829) ^ 25530) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 27009069828 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 53542288829) ^ 102123 = 35302899125 := by
        calc
          (3 : ZMod 53542288829) ^ 102123 = (3 : ZMod 53542288829) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 51061 * (3 : ZMod 53542288829) ^ 51061) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 35302899125 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 53542288829) ^ 204247 = 38435857800 := by
        calc
          (3 : ZMod 53542288829) ^ 204247 = (3 : ZMod 53542288829) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 102123 * (3 : ZMod 53542288829) ^ 102123) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 38435857800 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 53542288829) ^ 408495 = 51454275469 := by
        calc
          (3 : ZMod 53542288829) ^ 408495 = (3 : ZMod 53542288829) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 204247 * (3 : ZMod 53542288829) ^ 204247) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 51454275469 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 53542288829) ^ 816990 = 6213675391 := by
        calc
          (3 : ZMod 53542288829) ^ 816990 = (3 : ZMod 53542288829) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 408495 * (3 : ZMod 53542288829) ^ 408495 := by rw [pow_add]
          _ = 6213675391 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 53542288829) ^ 1633980 = 27985680826 := by
        calc
          (3 : ZMod 53542288829) ^ 1633980 = (3 : ZMod 53542288829) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 816990 * (3 : ZMod 53542288829) ^ 816990 := by rw [pow_add]
          _ = 27985680826 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 53542288829) ^ 3267961 = 11778820968 := by
        calc
          (3 : ZMod 53542288829) ^ 3267961 = (3 : ZMod 53542288829) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1633980 * (3 : ZMod 53542288829) ^ 1633980) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 11778820968 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 53542288829) ^ 6535923 = 44839916264 := by
        calc
          (3 : ZMod 53542288829) ^ 6535923 = (3 : ZMod 53542288829) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 3267961 * (3 : ZMod 53542288829) ^ 3267961) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 44839916264 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 53542288829) ^ 13071847 = 22467355834 := by
        calc
          (3 : ZMod 53542288829) ^ 13071847 = (3 : ZMod 53542288829) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 6535923 * (3 : ZMod 53542288829) ^ 6535923) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 22467355834 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 53542288829) ^ 26143695 = 28513133561 := by
        calc
          (3 : ZMod 53542288829) ^ 26143695 = (3 : ZMod 53542288829) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 13071847 * (3 : ZMod 53542288829) ^ 13071847) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 28513133561 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 53542288829) ^ 52287391 = 49631855044 := by
        calc
          (3 : ZMod 53542288829) ^ 52287391 = (3 : ZMod 53542288829) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 26143695 * (3 : ZMod 53542288829) ^ 26143695) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 49631855044 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 53542288829) ^ 104574782 = 7168663394 := by
        calc
          (3 : ZMod 53542288829) ^ 104574782 = (3 : ZMod 53542288829) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 52287391 * (3 : ZMod 53542288829) ^ 52287391 := by rw [pow_add]
          _ = 7168663394 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 53542288829) ^ 209149565 = 24529925491 := by
        calc
          (3 : ZMod 53542288829) ^ 209149565 = (3 : ZMod 53542288829) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 104574782 * (3 : ZMod 53542288829) ^ 104574782) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 24529925491 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 53542288829) ^ 418299131 = 25001627260 := by
        calc
          (3 : ZMod 53542288829) ^ 418299131 = (3 : ZMod 53542288829) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 209149565 * (3 : ZMod 53542288829) ^ 209149565) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 25001627260 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 53542288829) ^ 836598262 = 41566082560 := by
        calc
          (3 : ZMod 53542288829) ^ 836598262 = (3 : ZMod 53542288829) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 418299131 * (3 : ZMod 53542288829) ^ 418299131 := by rw [pow_add]
          _ = 41566082560 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 53542288829) ^ 1673196525 = 1383199450 := by
        calc
          (3 : ZMod 53542288829) ^ 1673196525 = (3 : ZMod 53542288829) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 836598262 * (3 : ZMod 53542288829) ^ 836598262) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 1383199450 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 53542288829) ^ 3346393051 = 36852761590 := by
        calc
          (3 : ZMod 53542288829) ^ 3346393051 = (3 : ZMod 53542288829) ^ (1673196525 + 1673196525 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1673196525 * (3 : ZMod 53542288829) ^ 1673196525) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 36852761590 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 53542288829) ^ 6692786103 = 44640607255 := by
        calc
          (3 : ZMod 53542288829) ^ 6692786103 = (3 : ZMod 53542288829) ^ (3346393051 + 3346393051 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 3346393051 * (3 : ZMod 53542288829) ^ 3346393051) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 44640607255 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 53542288829) ^ 13385572207 = 17217429040 := by
        calc
          (3 : ZMod 53542288829) ^ 13385572207 = (3 : ZMod 53542288829) ^ (6692786103 + 6692786103 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 6692786103 * (3 : ZMod 53542288829) ^ 6692786103) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 17217429040 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 53542288829) ^ 26771144414 = 53542288828 := by
        calc
          (3 : ZMod 53542288829) ^ 26771144414 = (3 : ZMod 53542288829) ^ (13385572207 + 13385572207) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 13385572207 * (3 : ZMod 53542288829) ^ 13385572207 := by rw [pow_add]
          _ = 53542288828 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 53542288829) ^ 53542288828 = 1 := by
        calc
          (3 : ZMod 53542288829) ^ 53542288828 = (3 : ZMod 53542288829) ^ (26771144414 + 26771144414) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 26771144414 * (3 : ZMod 53542288829) ^ 26771144414 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 2), (179, 1), (1526117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 2), (179, 1), (1526117, 1)] : List FactorBlock).map factorBlockValue).prod = 53542288829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 53542288829) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 53542288829) ^ 3 = 27 := by
        calc
          (3 : ZMod 53542288829) ^ 3 = (3 : ZMod 53542288829) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1 * (3 : ZMod 53542288829) ^ 1) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 53542288829) ^ 6 = 729 := by
        calc
          (3 : ZMod 53542288829) ^ 6 = (3 : ZMod 53542288829) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 3 * (3 : ZMod 53542288829) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 53542288829) ^ 12 = 531441 := by
        calc
          (3 : ZMod 53542288829) ^ 12 = (3 : ZMod 53542288829) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 6 * (3 : ZMod 53542288829) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 53542288829) ^ 24 = 14718092336 := by
        calc
          (3 : ZMod 53542288829) ^ 24 = (3 : ZMod 53542288829) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 12 * (3 : ZMod 53542288829) ^ 12 := by rw [pow_add]
          _ = 14718092336 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 53542288829) ^ 49 = 23251751366 := by
        calc
          (3 : ZMod 53542288829) ^ 49 = (3 : ZMod 53542288829) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 24 * (3 : ZMod 53542288829) ^ 24) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 23251751366 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 53542288829) ^ 99 = 16823402336 := by
        calc
          (3 : ZMod 53542288829) ^ 99 = (3 : ZMod 53542288829) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 49 * (3 : ZMod 53542288829) ^ 49) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 16823402336 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 53542288829) ^ 199 = 44334024943 := by
        calc
          (3 : ZMod 53542288829) ^ 199 = (3 : ZMod 53542288829) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 99 * (3 : ZMod 53542288829) ^ 99) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 44334024943 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 53542288829) ^ 398 = 5957634629 := by
        calc
          (3 : ZMod 53542288829) ^ 398 = (3 : ZMod 53542288829) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 199 * (3 : ZMod 53542288829) ^ 199 := by rw [pow_add]
          _ = 5957634629 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 53542288829) ^ 797 = 51664542727 := by
        calc
          (3 : ZMod 53542288829) ^ 797 = (3 : ZMod 53542288829) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 398 * (3 : ZMod 53542288829) ^ 398) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 51664542727 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 53542288829) ^ 1595 = 34109272656 := by
        calc
          (3 : ZMod 53542288829) ^ 1595 = (3 : ZMod 53542288829) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 797 * (3 : ZMod 53542288829) ^ 797) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 34109272656 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 53542288829) ^ 3191 = 47857687571 := by
        calc
          (3 : ZMod 53542288829) ^ 3191 = (3 : ZMod 53542288829) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1595 * (3 : ZMod 53542288829) ^ 1595) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 47857687571 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 53542288829) ^ 6382 = 20591696966 := by
        calc
          (3 : ZMod 53542288829) ^ 6382 = (3 : ZMod 53542288829) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 3191 * (3 : ZMod 53542288829) ^ 3191 := by rw [pow_add]
          _ = 20591696966 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 53542288829) ^ 12765 = 12661314111 := by
        calc
          (3 : ZMod 53542288829) ^ 12765 = (3 : ZMod 53542288829) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 6382 * (3 : ZMod 53542288829) ^ 6382) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 12661314111 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 53542288829) ^ 25530 = 38807947009 := by
        calc
          (3 : ZMod 53542288829) ^ 25530 = (3 : ZMod 53542288829) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 12765 * (3 : ZMod 53542288829) ^ 12765 := by rw [pow_add]
          _ = 38807947009 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 53542288829) ^ 51061 = 27009069828 := by
        calc
          (3 : ZMod 53542288829) ^ 51061 = (3 : ZMod 53542288829) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 25530 * (3 : ZMod 53542288829) ^ 25530) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 27009069828 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 53542288829) ^ 102123 = 35302899125 := by
        calc
          (3 : ZMod 53542288829) ^ 102123 = (3 : ZMod 53542288829) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 51061 * (3 : ZMod 53542288829) ^ 51061) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 35302899125 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 53542288829) ^ 204247 = 38435857800 := by
        calc
          (3 : ZMod 53542288829) ^ 204247 = (3 : ZMod 53542288829) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 102123 * (3 : ZMod 53542288829) ^ 102123) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 38435857800 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 53542288829) ^ 408495 = 51454275469 := by
        calc
          (3 : ZMod 53542288829) ^ 408495 = (3 : ZMod 53542288829) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 204247 * (3 : ZMod 53542288829) ^ 204247) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 51454275469 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 53542288829) ^ 816990 = 6213675391 := by
        calc
          (3 : ZMod 53542288829) ^ 816990 = (3 : ZMod 53542288829) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 408495 * (3 : ZMod 53542288829) ^ 408495 := by rw [pow_add]
          _ = 6213675391 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 53542288829) ^ 1633980 = 27985680826 := by
        calc
          (3 : ZMod 53542288829) ^ 1633980 = (3 : ZMod 53542288829) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 816990 * (3 : ZMod 53542288829) ^ 816990 := by rw [pow_add]
          _ = 27985680826 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 53542288829) ^ 3267961 = 11778820968 := by
        calc
          (3 : ZMod 53542288829) ^ 3267961 = (3 : ZMod 53542288829) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1633980 * (3 : ZMod 53542288829) ^ 1633980) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 11778820968 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 53542288829) ^ 6535923 = 44839916264 := by
        calc
          (3 : ZMod 53542288829) ^ 6535923 = (3 : ZMod 53542288829) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 3267961 * (3 : ZMod 53542288829) ^ 3267961) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 44839916264 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 53542288829) ^ 13071847 = 22467355834 := by
        calc
          (3 : ZMod 53542288829) ^ 13071847 = (3 : ZMod 53542288829) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 6535923 * (3 : ZMod 53542288829) ^ 6535923) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 22467355834 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 53542288829) ^ 26143695 = 28513133561 := by
        calc
          (3 : ZMod 53542288829) ^ 26143695 = (3 : ZMod 53542288829) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 13071847 * (3 : ZMod 53542288829) ^ 13071847) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 28513133561 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 53542288829) ^ 52287391 = 49631855044 := by
        calc
          (3 : ZMod 53542288829) ^ 52287391 = (3 : ZMod 53542288829) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 26143695 * (3 : ZMod 53542288829) ^ 26143695) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 49631855044 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 53542288829) ^ 104574782 = 7168663394 := by
        calc
          (3 : ZMod 53542288829) ^ 104574782 = (3 : ZMod 53542288829) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 52287391 * (3 : ZMod 53542288829) ^ 52287391 := by rw [pow_add]
          _ = 7168663394 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 53542288829) ^ 209149565 = 24529925491 := by
        calc
          (3 : ZMod 53542288829) ^ 209149565 = (3 : ZMod 53542288829) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 104574782 * (3 : ZMod 53542288829) ^ 104574782) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 24529925491 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 53542288829) ^ 418299131 = 25001627260 := by
        calc
          (3 : ZMod 53542288829) ^ 418299131 = (3 : ZMod 53542288829) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 209149565 * (3 : ZMod 53542288829) ^ 209149565) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 25001627260 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 53542288829) ^ 836598262 = 41566082560 := by
        calc
          (3 : ZMod 53542288829) ^ 836598262 = (3 : ZMod 53542288829) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 418299131 * (3 : ZMod 53542288829) ^ 418299131 := by rw [pow_add]
          _ = 41566082560 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 53542288829) ^ 1673196525 = 1383199450 := by
        calc
          (3 : ZMod 53542288829) ^ 1673196525 = (3 : ZMod 53542288829) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 836598262 * (3 : ZMod 53542288829) ^ 836598262) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 1383199450 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 53542288829) ^ 3346393051 = 36852761590 := by
        calc
          (3 : ZMod 53542288829) ^ 3346393051 = (3 : ZMod 53542288829) ^ (1673196525 + 1673196525 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1673196525 * (3 : ZMod 53542288829) ^ 1673196525) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 36852761590 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 53542288829) ^ 6692786103 = 44640607255 := by
        calc
          (3 : ZMod 53542288829) ^ 6692786103 = (3 : ZMod 53542288829) ^ (3346393051 + 3346393051 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 3346393051 * (3 : ZMod 53542288829) ^ 3346393051) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 44640607255 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 53542288829) ^ 13385572207 = 17217429040 := by
        calc
          (3 : ZMod 53542288829) ^ 13385572207 = (3 : ZMod 53542288829) ^ (6692786103 + 6692786103 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 6692786103 * (3 : ZMod 53542288829) ^ 6692786103) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 17217429040 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 53542288829) ^ 26771144414 = 53542288828 := by
        calc
          (3 : ZMod 53542288829) ^ 26771144414 = (3 : ZMod 53542288829) ^ (13385572207 + 13385572207) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 13385572207 * (3 : ZMod 53542288829) ^ 13385572207 := by rw [pow_add]
          _ = 53542288828 := by rw [factor_0_33]; decide
      change (3 : ZMod 53542288829) ^ 26771144414 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (3 : ZMod 53542288829) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 53542288829) ^ 3 = 27 := by
        calc
          (3 : ZMod 53542288829) ^ 3 = (3 : ZMod 53542288829) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1 * (3 : ZMod 53542288829) ^ 1) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 53542288829) ^ 7 = 2187 := by
        calc
          (3 : ZMod 53542288829) ^ 7 = (3 : ZMod 53542288829) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 3 * (3 : ZMod 53542288829) ^ 3) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 53542288829) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 53542288829) ^ 14 = (3 : ZMod 53542288829) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 7 * (3 : ZMod 53542288829) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 53542288829) ^ 28 = 14235124978 := by
        calc
          (3 : ZMod 53542288829) ^ 28 = (3 : ZMod 53542288829) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 14 * (3 : ZMod 53542288829) ^ 14 := by rw [pow_add]
          _ = 14235124978 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 53542288829) ^ 56 = 39948138721 := by
        calc
          (3 : ZMod 53542288829) ^ 56 = (3 : ZMod 53542288829) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 28 * (3 : ZMod 53542288829) ^ 28 := by rw [pow_add]
          _ = 39948138721 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 53542288829) ^ 113 = 50792397079 := by
        calc
          (3 : ZMod 53542288829) ^ 113 = (3 : ZMod 53542288829) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 56 * (3 : ZMod 53542288829) ^ 56) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 50792397079 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 53542288829) ^ 227 = 13844982046 := by
        calc
          (3 : ZMod 53542288829) ^ 227 = (3 : ZMod 53542288829) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 113 * (3 : ZMod 53542288829) ^ 113) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 13844982046 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 53542288829) ^ 455 = 22674643108 := by
        calc
          (3 : ZMod 53542288829) ^ 455 = (3 : ZMod 53542288829) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 227 * (3 : ZMod 53542288829) ^ 227) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 22674643108 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 53542288829) ^ 911 = 24929984519 := by
        calc
          (3 : ZMod 53542288829) ^ 911 = (3 : ZMod 53542288829) ^ (455 + 455 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 455 * (3 : ZMod 53542288829) ^ 455) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 24929984519 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 53542288829) ^ 1823 = 365275559 := by
        calc
          (3 : ZMod 53542288829) ^ 1823 = (3 : ZMod 53542288829) ^ (911 + 911 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 911 * (3 : ZMod 53542288829) ^ 911) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 365275559 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 53542288829) ^ 3647 = 30971457328 := by
        calc
          (3 : ZMod 53542288829) ^ 3647 = (3 : ZMod 53542288829) ^ (1823 + 1823 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1823 * (3 : ZMod 53542288829) ^ 1823) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 30971457328 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 53542288829) ^ 7294 = 41318794404 := by
        calc
          (3 : ZMod 53542288829) ^ 7294 = (3 : ZMod 53542288829) ^ (3647 + 3647) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 3647 * (3 : ZMod 53542288829) ^ 3647 := by rw [pow_add]
          _ = 41318794404 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 53542288829) ^ 14589 = 33465517721 := by
        calc
          (3 : ZMod 53542288829) ^ 14589 = (3 : ZMod 53542288829) ^ (7294 + 7294 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 7294 * (3 : ZMod 53542288829) ^ 7294) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 33465517721 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 53542288829) ^ 29178 = 25313544545 := by
        calc
          (3 : ZMod 53542288829) ^ 29178 = (3 : ZMod 53542288829) ^ (14589 + 14589) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 14589 * (3 : ZMod 53542288829) ^ 14589 := by rw [pow_add]
          _ = 25313544545 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 53542288829) ^ 58356 = 45406124337 := by
        calc
          (3 : ZMod 53542288829) ^ 58356 = (3 : ZMod 53542288829) ^ (29178 + 29178) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 29178 * (3 : ZMod 53542288829) ^ 29178 := by rw [pow_add]
          _ = 45406124337 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 53542288829) ^ 116712 = 7743651324 := by
        calc
          (3 : ZMod 53542288829) ^ 116712 = (3 : ZMod 53542288829) ^ (58356 + 58356) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 58356 * (3 : ZMod 53542288829) ^ 58356 := by rw [pow_add]
          _ = 7743651324 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 53542288829) ^ 233425 = 33471005920 := by
        calc
          (3 : ZMod 53542288829) ^ 233425 = (3 : ZMod 53542288829) ^ (116712 + 116712 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 116712 * (3 : ZMod 53542288829) ^ 116712) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 33471005920 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 53542288829) ^ 466851 = 25422655593 := by
        calc
          (3 : ZMod 53542288829) ^ 466851 = (3 : ZMod 53542288829) ^ (233425 + 233425 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 233425 * (3 : ZMod 53542288829) ^ 233425) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 25422655593 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 53542288829) ^ 933703 = 31143873712 := by
        calc
          (3 : ZMod 53542288829) ^ 933703 = (3 : ZMod 53542288829) ^ (466851 + 466851 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 466851 * (3 : ZMod 53542288829) ^ 466851) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 31143873712 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 53542288829) ^ 1867406 = 6621099700 := by
        calc
          (3 : ZMod 53542288829) ^ 1867406 = (3 : ZMod 53542288829) ^ (933703 + 933703) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 933703 * (3 : ZMod 53542288829) ^ 933703 := by rw [pow_add]
          _ = 6621099700 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 53542288829) ^ 3734813 = 22904887833 := by
        calc
          (3 : ZMod 53542288829) ^ 3734813 = (3 : ZMod 53542288829) ^ (1867406 + 1867406 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 1867406 * (3 : ZMod 53542288829) ^ 1867406) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 22904887833 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 53542288829) ^ 7469627 = 45640456544 := by
        calc
          (3 : ZMod 53542288829) ^ 7469627 = (3 : ZMod 53542288829) ^ (3734813 + 3734813 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 3734813 * (3 : ZMod 53542288829) ^ 3734813) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 45640456544 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 53542288829) ^ 14939254 = 15411435030 := by
        calc
          (3 : ZMod 53542288829) ^ 14939254 = (3 : ZMod 53542288829) ^ (7469627 + 7469627) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 7469627 * (3 : ZMod 53542288829) ^ 7469627 := by rw [pow_add]
          _ = 15411435030 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 53542288829) ^ 29878509 = 2365818242 := by
        calc
          (3 : ZMod 53542288829) ^ 29878509 = (3 : ZMod 53542288829) ^ (14939254 + 14939254 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 14939254 * (3 : ZMod 53542288829) ^ 14939254) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 2365818242 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 53542288829) ^ 59757018 = 52285958999 := by
        calc
          (3 : ZMod 53542288829) ^ 59757018 = (3 : ZMod 53542288829) ^ (29878509 + 29878509) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 29878509 * (3 : ZMod 53542288829) ^ 29878509 := by rw [pow_add]
          _ = 52285958999 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 53542288829) ^ 119514037 = 14202696304 := by
        calc
          (3 : ZMod 53542288829) ^ 119514037 = (3 : ZMod 53542288829) ^ (59757018 + 59757018 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 59757018 * (3 : ZMod 53542288829) ^ 59757018) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 14202696304 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 53542288829) ^ 239028075 = 12398333938 := by
        calc
          (3 : ZMod 53542288829) ^ 239028075 = (3 : ZMod 53542288829) ^ (119514037 + 119514037 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 119514037 * (3 : ZMod 53542288829) ^ 119514037) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 12398333938 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 53542288829) ^ 478056150 = 24567526721 := by
        calc
          (3 : ZMod 53542288829) ^ 478056150 = (3 : ZMod 53542288829) ^ (239028075 + 239028075) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 239028075 * (3 : ZMod 53542288829) ^ 239028075 := by rw [pow_add]
          _ = 24567526721 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 53542288829) ^ 956112300 = 46593879860 := by
        calc
          (3 : ZMod 53542288829) ^ 956112300 = (3 : ZMod 53542288829) ^ (478056150 + 478056150) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 478056150 * (3 : ZMod 53542288829) ^ 478056150 := by rw [pow_add]
          _ = 46593879860 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 53542288829) ^ 1912224601 = 7106075823 := by
        calc
          (3 : ZMod 53542288829) ^ 1912224601 = (3 : ZMod 53542288829) ^ (956112300 + 956112300 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 956112300 * (3 : ZMod 53542288829) ^ 956112300) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 7106075823 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 53542288829) ^ 3824449202 = 20219143850 := by
        calc
          (3 : ZMod 53542288829) ^ 3824449202 = (3 : ZMod 53542288829) ^ (1912224601 + 1912224601) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 1912224601 * (3 : ZMod 53542288829) ^ 1912224601 := by rw [pow_add]
          _ = 20219143850 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 53542288829) ^ 7648898404 = 11653562226 := by
        calc
          (3 : ZMod 53542288829) ^ 7648898404 = (3 : ZMod 53542288829) ^ (3824449202 + 3824449202) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 3824449202 * (3 : ZMod 53542288829) ^ 3824449202 := by rw [pow_add]
          _ = 11653562226 := by rw [factor_1_31]; decide
      change (3 : ZMod 53542288829) ^ 7648898404 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (3 : ZMod 53542288829) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 53542288829) ^ 2 = 9 := by
        calc
          (3 : ZMod 53542288829) ^ 2 = (3 : ZMod 53542288829) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 1 * (3 : ZMod 53542288829) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 53542288829) ^ 4 = 81 := by
        calc
          (3 : ZMod 53542288829) ^ 4 = (3 : ZMod 53542288829) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 2 * (3 : ZMod 53542288829) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 53542288829) ^ 8 = 6561 := by
        calc
          (3 : ZMod 53542288829) ^ 8 = (3 : ZMod 53542288829) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 4 * (3 : ZMod 53542288829) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 53542288829) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 53542288829) ^ 17 = (3 : ZMod 53542288829) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 8 * (3 : ZMod 53542288829) ^ 8) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 53542288829) ^ 35 = 24148517237 := by
        calc
          (3 : ZMod 53542288829) ^ 35 = (3 : ZMod 53542288829) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 17 * (3 : ZMod 53542288829) ^ 17) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 24148517237 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 53542288829) ^ 71 = 1804129840 := by
        calc
          (3 : ZMod 53542288829) ^ 71 = (3 : ZMod 53542288829) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 35 * (3 : ZMod 53542288829) ^ 35) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 1804129840 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 53542288829) ^ 142 = 18180681210 := by
        calc
          (3 : ZMod 53542288829) ^ 142 = (3 : ZMod 53542288829) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 71 * (3 : ZMod 53542288829) ^ 71 := by rw [pow_add]
          _ = 18180681210 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 53542288829) ^ 285 = 14614985886 := by
        calc
          (3 : ZMod 53542288829) ^ 285 = (3 : ZMod 53542288829) ^ (142 + 142 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 142 * (3 : ZMod 53542288829) ^ 142) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 14614985886 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 53542288829) ^ 570 = 42660493884 := by
        calc
          (3 : ZMod 53542288829) ^ 570 = (3 : ZMod 53542288829) ^ (285 + 285) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 285 * (3 : ZMod 53542288829) ^ 285 := by rw [pow_add]
          _ = 42660493884 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 53542288829) ^ 1141 = 42065472838 := by
        calc
          (3 : ZMod 53542288829) ^ 1141 = (3 : ZMod 53542288829) ^ (570 + 570 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 570 * (3 : ZMod 53542288829) ^ 570) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 42065472838 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 53542288829) ^ 2282 = 18463952783 := by
        calc
          (3 : ZMod 53542288829) ^ 2282 = (3 : ZMod 53542288829) ^ (1141 + 1141) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 1141 * (3 : ZMod 53542288829) ^ 1141 := by rw [pow_add]
          _ = 18463952783 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 53542288829) ^ 4564 = 51595124577 := by
        calc
          (3 : ZMod 53542288829) ^ 4564 = (3 : ZMod 53542288829) ^ (2282 + 2282) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 2282 * (3 : ZMod 53542288829) ^ 2282 := by rw [pow_add]
          _ = 51595124577 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 53542288829) ^ 9128 = 20692584979 := by
        calc
          (3 : ZMod 53542288829) ^ 9128 = (3 : ZMod 53542288829) ^ (4564 + 4564) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 4564 * (3 : ZMod 53542288829) ^ 4564 := by rw [pow_add]
          _ = 20692584979 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 53542288829) ^ 18256 = 48541347446 := by
        calc
          (3 : ZMod 53542288829) ^ 18256 = (3 : ZMod 53542288829) ^ (9128 + 9128) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 9128 * (3 : ZMod 53542288829) ^ 9128 := by rw [pow_add]
          _ = 48541347446 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 53542288829) ^ 36513 = 4929036991 := by
        calc
          (3 : ZMod 53542288829) ^ 36513 = (3 : ZMod 53542288829) ^ (18256 + 18256 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 18256 * (3 : ZMod 53542288829) ^ 18256) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 4929036991 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 53542288829) ^ 73027 = 42030850168 := by
        calc
          (3 : ZMod 53542288829) ^ 73027 = (3 : ZMod 53542288829) ^ (36513 + 36513 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 36513 * (3 : ZMod 53542288829) ^ 36513) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 42030850168 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 53542288829) ^ 146054 = 29404527154 := by
        calc
          (3 : ZMod 53542288829) ^ 146054 = (3 : ZMod 53542288829) ^ (73027 + 73027) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 73027 * (3 : ZMod 53542288829) ^ 73027 := by rw [pow_add]
          _ = 29404527154 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 53542288829) ^ 292108 = 18338546823 := by
        calc
          (3 : ZMod 53542288829) ^ 292108 = (3 : ZMod 53542288829) ^ (146054 + 146054) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 146054 * (3 : ZMod 53542288829) ^ 146054 := by rw [pow_add]
          _ = 18338546823 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 53542288829) ^ 584216 = 34089776305 := by
        calc
          (3 : ZMod 53542288829) ^ 584216 = (3 : ZMod 53542288829) ^ (292108 + 292108) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 292108 * (3 : ZMod 53542288829) ^ 292108 := by rw [pow_add]
          _ = 34089776305 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 53542288829) ^ 1168433 = 45731933359 := by
        calc
          (3 : ZMod 53542288829) ^ 1168433 = (3 : ZMod 53542288829) ^ (584216 + 584216 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 584216 * (3 : ZMod 53542288829) ^ 584216) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 45731933359 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 53542288829) ^ 2336866 = 49988964256 := by
        calc
          (3 : ZMod 53542288829) ^ 2336866 = (3 : ZMod 53542288829) ^ (1168433 + 1168433) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 1168433 * (3 : ZMod 53542288829) ^ 1168433 := by rw [pow_add]
          _ = 49988964256 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 53542288829) ^ 4673733 = 19748750696 := by
        calc
          (3 : ZMod 53542288829) ^ 4673733 = (3 : ZMod 53542288829) ^ (2336866 + 2336866 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 2336866 * (3 : ZMod 53542288829) ^ 2336866) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 19748750696 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 53542288829) ^ 9347466 = 43292902733 := by
        calc
          (3 : ZMod 53542288829) ^ 9347466 = (3 : ZMod 53542288829) ^ (4673733 + 4673733) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 4673733 * (3 : ZMod 53542288829) ^ 4673733 := by rw [pow_add]
          _ = 43292902733 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 53542288829) ^ 18694933 = 21778022377 := by
        calc
          (3 : ZMod 53542288829) ^ 18694933 = (3 : ZMod 53542288829) ^ (9347466 + 9347466 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 9347466 * (3 : ZMod 53542288829) ^ 9347466) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 21778022377 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 53542288829) ^ 37389866 = 29966258281 := by
        calc
          (3 : ZMod 53542288829) ^ 37389866 = (3 : ZMod 53542288829) ^ (18694933 + 18694933) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 18694933 * (3 : ZMod 53542288829) ^ 18694933 := by rw [pow_add]
          _ = 29966258281 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 53542288829) ^ 74779733 = 21685032896 := by
        calc
          (3 : ZMod 53542288829) ^ 74779733 = (3 : ZMod 53542288829) ^ (37389866 + 37389866 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 37389866 * (3 : ZMod 53542288829) ^ 37389866) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 21685032896 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 53542288829) ^ 149559466 = 35374265449 := by
        calc
          (3 : ZMod 53542288829) ^ 149559466 = (3 : ZMod 53542288829) ^ (74779733 + 74779733) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 74779733 * (3 : ZMod 53542288829) ^ 74779733 := by rw [pow_add]
          _ = 35374265449 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 53542288829) ^ 299118932 = 22771789374 := by
        calc
          (3 : ZMod 53542288829) ^ 299118932 = (3 : ZMod 53542288829) ^ (149559466 + 149559466) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 149559466 * (3 : ZMod 53542288829) ^ 149559466 := by rw [pow_add]
          _ = 22771789374 := by rw [factor_2_27]; decide
      change (3 : ZMod 53542288829) ^ 299118932 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (3 : ZMod 53542288829) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 53542288829) ^ 2 = 9 := by
        calc
          (3 : ZMod 53542288829) ^ 2 = (3 : ZMod 53542288829) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 1 * (3 : ZMod 53542288829) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 53542288829) ^ 4 = 81 := by
        calc
          (3 : ZMod 53542288829) ^ 4 = (3 : ZMod 53542288829) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 2 * (3 : ZMod 53542288829) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 53542288829) ^ 8 = 6561 := by
        calc
          (3 : ZMod 53542288829) ^ 8 = (3 : ZMod 53542288829) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 4 * (3 : ZMod 53542288829) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 53542288829) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 53542288829) ^ 17 = (3 : ZMod 53542288829) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 8 * (3 : ZMod 53542288829) ^ 8) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 53542288829) ^ 34 = 43744364965 := by
        calc
          (3 : ZMod 53542288829) ^ 34 = (3 : ZMod 53542288829) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 17 * (3 : ZMod 53542288829) ^ 17 := by rw [pow_add]
          _ = 43744364965 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 53542288829) ^ 68 = 25846440171 := by
        calc
          (3 : ZMod 53542288829) ^ 68 = (3 : ZMod 53542288829) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 34 * (3 : ZMod 53542288829) ^ 34 := by rw [pow_add]
          _ = 25846440171 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 53542288829) ^ 137 = 13956151759 := by
        calc
          (3 : ZMod 53542288829) ^ 137 = (3 : ZMod 53542288829) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 68 * (3 : ZMod 53542288829) ^ 68) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 13956151759 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 53542288829) ^ 274 = 12202127935 := by
        calc
          (3 : ZMod 53542288829) ^ 274 = (3 : ZMod 53542288829) ^ (137 + 137) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 137 * (3 : ZMod 53542288829) ^ 137 := by rw [pow_add]
          _ = 12202127935 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 53542288829) ^ 548 = 38028341498 := by
        calc
          (3 : ZMod 53542288829) ^ 548 = (3 : ZMod 53542288829) ^ (274 + 274) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 274 * (3 : ZMod 53542288829) ^ 274 := by rw [pow_add]
          _ = 38028341498 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 53542288829) ^ 1096 = 19919979244 := by
        calc
          (3 : ZMod 53542288829) ^ 1096 = (3 : ZMod 53542288829) ^ (548 + 548) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 548 * (3 : ZMod 53542288829) ^ 548 := by rw [pow_add]
          _ = 19919979244 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 53542288829) ^ 2192 = 31603428270 := by
        calc
          (3 : ZMod 53542288829) ^ 2192 = (3 : ZMod 53542288829) ^ (1096 + 1096) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 1096 * (3 : ZMod 53542288829) ^ 1096 := by rw [pow_add]
          _ = 31603428270 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 53542288829) ^ 4385 = 40943916659 := by
        calc
          (3 : ZMod 53542288829) ^ 4385 = (3 : ZMod 53542288829) ^ (2192 + 2192 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 2192 * (3 : ZMod 53542288829) ^ 2192) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 40943916659 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 53542288829) ^ 8771 = 10301599264 := by
        calc
          (3 : ZMod 53542288829) ^ 8771 = (3 : ZMod 53542288829) ^ (4385 + 4385 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = ((3 : ZMod 53542288829) ^ 4385 * (3 : ZMod 53542288829) ^ 4385) * (3 : ZMod 53542288829) := by rw [pow_succ, pow_add]
          _ = 10301599264 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 53542288829) ^ 17542 = 7414236325 := by
        calc
          (3 : ZMod 53542288829) ^ 17542 = (3 : ZMod 53542288829) ^ (8771 + 8771) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 8771 * (3 : ZMod 53542288829) ^ 8771 := by rw [pow_add]
          _ = 7414236325 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 53542288829) ^ 35084 = 12001212142 := by
        calc
          (3 : ZMod 53542288829) ^ 35084 = (3 : ZMod 53542288829) ^ (17542 + 17542) :=
            congrArg (fun n : ℕ => (3 : ZMod 53542288829) ^ n) (by norm_num)
          _ = (3 : ZMod 53542288829) ^ 17542 * (3 : ZMod 53542288829) ^ 17542 := by rw [pow_add]
          _ = 12001212142 := by rw [factor_3_14]; decide
      change (3 : ZMod 53542288829) ^ 35084 ≠ 1
      rw [factor_3_15]
      decide

#print axioms prime_lucas_53542288829

end TotientTailPeriodKiller
end Erdos249257
