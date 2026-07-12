import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_26771144429 : Nat.Prime 26771144429 := by
  apply lucas_primality 26771144429 (2 : ZMod 26771144429)
  ·
      have fermat_0 : (2 : ZMod 26771144429) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 26771144429) ^ 3 = 8 := by
        calc
          (2 : ZMod 26771144429) ^ 3 = (2 : ZMod 26771144429) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1 * (2 : ZMod 26771144429) ^ 1) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 26771144429) ^ 6 = 64 := by
        calc
          (2 : ZMod 26771144429) ^ 6 = (2 : ZMod 26771144429) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 3 * (2 : ZMod 26771144429) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 26771144429) ^ 12 = 4096 := by
        calc
          (2 : ZMod 26771144429) ^ 12 = (2 : ZMod 26771144429) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 6 * (2 : ZMod 26771144429) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 26771144429) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 26771144429) ^ 24 = (2 : ZMod 26771144429) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 12 * (2 : ZMod 26771144429) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 26771144429) ^ 49 = 6328368300 := by
        calc
          (2 : ZMod 26771144429) ^ 49 = (2 : ZMod 26771144429) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 24 * (2 : ZMod 26771144429) ^ 24) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 6328368300 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 26771144429) ^ 99 = 13113479971 := by
        calc
          (2 : ZMod 26771144429) ^ 99 = (2 : ZMod 26771144429) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 49 * (2 : ZMod 26771144429) ^ 49) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 13113479971 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 26771144429) ^ 199 = 2464664844 := by
        calc
          (2 : ZMod 26771144429) ^ 199 = (2 : ZMod 26771144429) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 99 * (2 : ZMod 26771144429) ^ 99) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 2464664844 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 26771144429) ^ 398 = 8004837561 := by
        calc
          (2 : ZMod 26771144429) ^ 398 = (2 : ZMod 26771144429) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 199 * (2 : ZMod 26771144429) ^ 199 := by rw [pow_add]
          _ = 8004837561 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 26771144429) ^ 797 = 620809344 := by
        calc
          (2 : ZMod 26771144429) ^ 797 = (2 : ZMod 26771144429) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 398 * (2 : ZMod 26771144429) ^ 398) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 620809344 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 26771144429) ^ 1595 = 12740849453 := by
        calc
          (2 : ZMod 26771144429) ^ 1595 = (2 : ZMod 26771144429) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 797 * (2 : ZMod 26771144429) ^ 797) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 12740849453 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 26771144429) ^ 3191 = 22764446382 := by
        calc
          (2 : ZMod 26771144429) ^ 3191 = (2 : ZMod 26771144429) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1595 * (2 : ZMod 26771144429) ^ 1595) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 22764446382 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 26771144429) ^ 6382 = 10185988921 := by
        calc
          (2 : ZMod 26771144429) ^ 6382 = (2 : ZMod 26771144429) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 3191 * (2 : ZMod 26771144429) ^ 3191 := by rw [pow_add]
          _ = 10185988921 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 26771144429) ^ 12765 = 6443108117 := by
        calc
          (2 : ZMod 26771144429) ^ 12765 = (2 : ZMod 26771144429) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 6382 * (2 : ZMod 26771144429) ^ 6382) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 6443108117 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 26771144429) ^ 25530 = 17701082493 := by
        calc
          (2 : ZMod 26771144429) ^ 25530 = (2 : ZMod 26771144429) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 12765 * (2 : ZMod 26771144429) ^ 12765 := by rw [pow_add]
          _ = 17701082493 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 26771144429) ^ 51061 = 13246726442 := by
        calc
          (2 : ZMod 26771144429) ^ 51061 = (2 : ZMod 26771144429) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 25530 * (2 : ZMod 26771144429) ^ 25530) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 13246726442 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 26771144429) ^ 102123 = 26380570205 := by
        calc
          (2 : ZMod 26771144429) ^ 102123 = (2 : ZMod 26771144429) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 51061 * (2 : ZMod 26771144429) ^ 51061) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 26380570205 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 26771144429) ^ 204247 = 11640216438 := by
        calc
          (2 : ZMod 26771144429) ^ 204247 = (2 : ZMod 26771144429) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 102123 * (2 : ZMod 26771144429) ^ 102123) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 11640216438 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 26771144429) ^ 408495 = 13696140815 := by
        calc
          (2 : ZMod 26771144429) ^ 408495 = (2 : ZMod 26771144429) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 204247 * (2 : ZMod 26771144429) ^ 204247) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 13696140815 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 26771144429) ^ 816990 = 2879408979 := by
        calc
          (2 : ZMod 26771144429) ^ 816990 = (2 : ZMod 26771144429) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 408495 * (2 : ZMod 26771144429) ^ 408495 := by rw [pow_add]
          _ = 2879408979 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 26771144429) ^ 1633980 = 25565273308 := by
        calc
          (2 : ZMod 26771144429) ^ 1633980 = (2 : ZMod 26771144429) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 816990 * (2 : ZMod 26771144429) ^ 816990 := by rw [pow_add]
          _ = 25565273308 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 26771144429) ^ 3267961 = 1157970381 := by
        calc
          (2 : ZMod 26771144429) ^ 3267961 = (2 : ZMod 26771144429) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1633980 * (2 : ZMod 26771144429) ^ 1633980) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 1157970381 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 26771144429) ^ 6535923 = 6908857031 := by
        calc
          (2 : ZMod 26771144429) ^ 6535923 = (2 : ZMod 26771144429) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 3267961 * (2 : ZMod 26771144429) ^ 3267961) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 6908857031 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 26771144429) ^ 13071847 = 17232303432 := by
        calc
          (2 : ZMod 26771144429) ^ 13071847 = (2 : ZMod 26771144429) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 6535923 * (2 : ZMod 26771144429) ^ 6535923) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 17232303432 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 26771144429) ^ 26143695 = 12364453780 := by
        calc
          (2 : ZMod 26771144429) ^ 26143695 = (2 : ZMod 26771144429) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 13071847 * (2 : ZMod 26771144429) ^ 13071847) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 12364453780 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 26771144429) ^ 52287391 = 18988183499 := by
        calc
          (2 : ZMod 26771144429) ^ 52287391 = (2 : ZMod 26771144429) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 26143695 * (2 : ZMod 26771144429) ^ 26143695) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 18988183499 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 26771144429) ^ 104574782 = 18570670308 := by
        calc
          (2 : ZMod 26771144429) ^ 104574782 = (2 : ZMod 26771144429) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 52287391 * (2 : ZMod 26771144429) ^ 52287391 := by rw [pow_add]
          _ = 18570670308 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 26771144429) ^ 209149565 = 4976111439 := by
        calc
          (2 : ZMod 26771144429) ^ 209149565 = (2 : ZMod 26771144429) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 104574782 * (2 : ZMod 26771144429) ^ 104574782) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 4976111439 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 26771144429) ^ 418299131 = 11922239281 := by
        calc
          (2 : ZMod 26771144429) ^ 418299131 = (2 : ZMod 26771144429) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 209149565 * (2 : ZMod 26771144429) ^ 209149565) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 11922239281 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 26771144429) ^ 836598263 = 11683901210 := by
        calc
          (2 : ZMod 26771144429) ^ 836598263 = (2 : ZMod 26771144429) ^ (418299131 + 418299131 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 418299131 * (2 : ZMod 26771144429) ^ 418299131) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 11683901210 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 26771144429) ^ 1673196526 = 15352302751 := by
        calc
          (2 : ZMod 26771144429) ^ 1673196526 = (2 : ZMod 26771144429) ^ (836598263 + 836598263) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 836598263 * (2 : ZMod 26771144429) ^ 836598263 := by rw [pow_add]
          _ = 15352302751 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 26771144429) ^ 3346393053 = 12573431444 := by
        calc
          (2 : ZMod 26771144429) ^ 3346393053 = (2 : ZMod 26771144429) ^ (1673196526 + 1673196526 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1673196526 * (2 : ZMod 26771144429) ^ 1673196526) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 12573431444 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 26771144429) ^ 6692786107 = 25146862887 := by
        calc
          (2 : ZMod 26771144429) ^ 6692786107 = (2 : ZMod 26771144429) ^ (3346393053 + 3346393053 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 3346393053 * (2 : ZMod 26771144429) ^ 3346393053) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 25146862887 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 26771144429) ^ 13385572214 = 26771144428 := by
        calc
          (2 : ZMod 26771144429) ^ 13385572214 = (2 : ZMod 26771144429) ^ (6692786107 + 6692786107) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 6692786107 * (2 : ZMod 26771144429) ^ 6692786107 := by rw [pow_add]
          _ = 26771144428 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 26771144429) ^ 26771144428 = 1 := by
        calc
          (2 : ZMod 26771144429) ^ 26771144428 = (2 : ZMod 26771144429) ^ (13385572214 + 13385572214) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 13385572214 * (2 : ZMod 26771144429) ^ 13385572214 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (37, 1), (25840873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (37, 1), (25840873, 1)] : List FactorBlock).map factorBlockValue).prod = 26771144429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 26771144429) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 26771144429) ^ 3 = 8 := by
        calc
          (2 : ZMod 26771144429) ^ 3 = (2 : ZMod 26771144429) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1 * (2 : ZMod 26771144429) ^ 1) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 26771144429) ^ 6 = 64 := by
        calc
          (2 : ZMod 26771144429) ^ 6 = (2 : ZMod 26771144429) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 3 * (2 : ZMod 26771144429) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 26771144429) ^ 12 = 4096 := by
        calc
          (2 : ZMod 26771144429) ^ 12 = (2 : ZMod 26771144429) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 6 * (2 : ZMod 26771144429) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 26771144429) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 26771144429) ^ 24 = (2 : ZMod 26771144429) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 12 * (2 : ZMod 26771144429) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 26771144429) ^ 49 = 6328368300 := by
        calc
          (2 : ZMod 26771144429) ^ 49 = (2 : ZMod 26771144429) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 24 * (2 : ZMod 26771144429) ^ 24) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 6328368300 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 26771144429) ^ 99 = 13113479971 := by
        calc
          (2 : ZMod 26771144429) ^ 99 = (2 : ZMod 26771144429) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 49 * (2 : ZMod 26771144429) ^ 49) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 13113479971 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 26771144429) ^ 199 = 2464664844 := by
        calc
          (2 : ZMod 26771144429) ^ 199 = (2 : ZMod 26771144429) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 99 * (2 : ZMod 26771144429) ^ 99) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 2464664844 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 26771144429) ^ 398 = 8004837561 := by
        calc
          (2 : ZMod 26771144429) ^ 398 = (2 : ZMod 26771144429) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 199 * (2 : ZMod 26771144429) ^ 199 := by rw [pow_add]
          _ = 8004837561 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 26771144429) ^ 797 = 620809344 := by
        calc
          (2 : ZMod 26771144429) ^ 797 = (2 : ZMod 26771144429) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 398 * (2 : ZMod 26771144429) ^ 398) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 620809344 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 26771144429) ^ 1595 = 12740849453 := by
        calc
          (2 : ZMod 26771144429) ^ 1595 = (2 : ZMod 26771144429) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 797 * (2 : ZMod 26771144429) ^ 797) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 12740849453 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 26771144429) ^ 3191 = 22764446382 := by
        calc
          (2 : ZMod 26771144429) ^ 3191 = (2 : ZMod 26771144429) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1595 * (2 : ZMod 26771144429) ^ 1595) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 22764446382 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 26771144429) ^ 6382 = 10185988921 := by
        calc
          (2 : ZMod 26771144429) ^ 6382 = (2 : ZMod 26771144429) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 3191 * (2 : ZMod 26771144429) ^ 3191 := by rw [pow_add]
          _ = 10185988921 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 26771144429) ^ 12765 = 6443108117 := by
        calc
          (2 : ZMod 26771144429) ^ 12765 = (2 : ZMod 26771144429) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 6382 * (2 : ZMod 26771144429) ^ 6382) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 6443108117 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 26771144429) ^ 25530 = 17701082493 := by
        calc
          (2 : ZMod 26771144429) ^ 25530 = (2 : ZMod 26771144429) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 12765 * (2 : ZMod 26771144429) ^ 12765 := by rw [pow_add]
          _ = 17701082493 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 26771144429) ^ 51061 = 13246726442 := by
        calc
          (2 : ZMod 26771144429) ^ 51061 = (2 : ZMod 26771144429) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 25530 * (2 : ZMod 26771144429) ^ 25530) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 13246726442 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 26771144429) ^ 102123 = 26380570205 := by
        calc
          (2 : ZMod 26771144429) ^ 102123 = (2 : ZMod 26771144429) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 51061 * (2 : ZMod 26771144429) ^ 51061) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 26380570205 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 26771144429) ^ 204247 = 11640216438 := by
        calc
          (2 : ZMod 26771144429) ^ 204247 = (2 : ZMod 26771144429) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 102123 * (2 : ZMod 26771144429) ^ 102123) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 11640216438 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 26771144429) ^ 408495 = 13696140815 := by
        calc
          (2 : ZMod 26771144429) ^ 408495 = (2 : ZMod 26771144429) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 204247 * (2 : ZMod 26771144429) ^ 204247) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 13696140815 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 26771144429) ^ 816990 = 2879408979 := by
        calc
          (2 : ZMod 26771144429) ^ 816990 = (2 : ZMod 26771144429) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 408495 * (2 : ZMod 26771144429) ^ 408495 := by rw [pow_add]
          _ = 2879408979 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 26771144429) ^ 1633980 = 25565273308 := by
        calc
          (2 : ZMod 26771144429) ^ 1633980 = (2 : ZMod 26771144429) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 816990 * (2 : ZMod 26771144429) ^ 816990 := by rw [pow_add]
          _ = 25565273308 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 26771144429) ^ 3267961 = 1157970381 := by
        calc
          (2 : ZMod 26771144429) ^ 3267961 = (2 : ZMod 26771144429) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1633980 * (2 : ZMod 26771144429) ^ 1633980) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 1157970381 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 26771144429) ^ 6535923 = 6908857031 := by
        calc
          (2 : ZMod 26771144429) ^ 6535923 = (2 : ZMod 26771144429) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 3267961 * (2 : ZMod 26771144429) ^ 3267961) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 6908857031 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 26771144429) ^ 13071847 = 17232303432 := by
        calc
          (2 : ZMod 26771144429) ^ 13071847 = (2 : ZMod 26771144429) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 6535923 * (2 : ZMod 26771144429) ^ 6535923) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 17232303432 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 26771144429) ^ 26143695 = 12364453780 := by
        calc
          (2 : ZMod 26771144429) ^ 26143695 = (2 : ZMod 26771144429) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 13071847 * (2 : ZMod 26771144429) ^ 13071847) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 12364453780 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 26771144429) ^ 52287391 = 18988183499 := by
        calc
          (2 : ZMod 26771144429) ^ 52287391 = (2 : ZMod 26771144429) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 26143695 * (2 : ZMod 26771144429) ^ 26143695) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 18988183499 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 26771144429) ^ 104574782 = 18570670308 := by
        calc
          (2 : ZMod 26771144429) ^ 104574782 = (2 : ZMod 26771144429) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 52287391 * (2 : ZMod 26771144429) ^ 52287391 := by rw [pow_add]
          _ = 18570670308 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 26771144429) ^ 209149565 = 4976111439 := by
        calc
          (2 : ZMod 26771144429) ^ 209149565 = (2 : ZMod 26771144429) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 104574782 * (2 : ZMod 26771144429) ^ 104574782) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 4976111439 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 26771144429) ^ 418299131 = 11922239281 := by
        calc
          (2 : ZMod 26771144429) ^ 418299131 = (2 : ZMod 26771144429) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 209149565 * (2 : ZMod 26771144429) ^ 209149565) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 11922239281 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 26771144429) ^ 836598263 = 11683901210 := by
        calc
          (2 : ZMod 26771144429) ^ 836598263 = (2 : ZMod 26771144429) ^ (418299131 + 418299131 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 418299131 * (2 : ZMod 26771144429) ^ 418299131) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 11683901210 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 26771144429) ^ 1673196526 = 15352302751 := by
        calc
          (2 : ZMod 26771144429) ^ 1673196526 = (2 : ZMod 26771144429) ^ (836598263 + 836598263) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 836598263 * (2 : ZMod 26771144429) ^ 836598263 := by rw [pow_add]
          _ = 15352302751 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 26771144429) ^ 3346393053 = 12573431444 := by
        calc
          (2 : ZMod 26771144429) ^ 3346393053 = (2 : ZMod 26771144429) ^ (1673196526 + 1673196526 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1673196526 * (2 : ZMod 26771144429) ^ 1673196526) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 12573431444 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 26771144429) ^ 6692786107 = 25146862887 := by
        calc
          (2 : ZMod 26771144429) ^ 6692786107 = (2 : ZMod 26771144429) ^ (3346393053 + 3346393053 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 3346393053 * (2 : ZMod 26771144429) ^ 3346393053) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 25146862887 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 26771144429) ^ 13385572214 = 26771144428 := by
        calc
          (2 : ZMod 26771144429) ^ 13385572214 = (2 : ZMod 26771144429) ^ (6692786107 + 6692786107) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 6692786107 * (2 : ZMod 26771144429) ^ 6692786107 := by rw [pow_add]
          _ = 26771144428 := by rw [factor_0_32]; decide
      change (2 : ZMod 26771144429) ^ 13385572214 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (2 : ZMod 26771144429) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 26771144429) ^ 3 = 8 := by
        calc
          (2 : ZMod 26771144429) ^ 3 = (2 : ZMod 26771144429) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1 * (2 : ZMod 26771144429) ^ 1) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 26771144429) ^ 7 = 128 := by
        calc
          (2 : ZMod 26771144429) ^ 7 = (2 : ZMod 26771144429) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 3 * (2 : ZMod 26771144429) ^ 3) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 26771144429) ^ 14 = 16384 := by
        calc
          (2 : ZMod 26771144429) ^ 14 = (2 : ZMod 26771144429) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 7 * (2 : ZMod 26771144429) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 26771144429) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 26771144429) ^ 28 = (2 : ZMod 26771144429) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 14 * (2 : ZMod 26771144429) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 26771144429) ^ 56 = 6896809530 := by
        calc
          (2 : ZMod 26771144429) ^ 56 = (2 : ZMod 26771144429) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 28 * (2 : ZMod 26771144429) ^ 28 := by rw [pow_add]
          _ = 6896809530 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 26771144429) ^ 113 = 12821802139 := by
        calc
          (2 : ZMod 26771144429) ^ 113 = (2 : ZMod 26771144429) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 56 * (2 : ZMod 26771144429) ^ 56) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 12821802139 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 26771144429) ^ 227 = 584525448 := by
        calc
          (2 : ZMod 26771144429) ^ 227 = (2 : ZMod 26771144429) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 113 * (2 : ZMod 26771144429) ^ 113) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 584525448 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 26771144429) ^ 455 = 5009735732 := by
        calc
          (2 : ZMod 26771144429) ^ 455 = (2 : ZMod 26771144429) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 227 * (2 : ZMod 26771144429) ^ 227) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 5009735732 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 26771144429) ^ 911 = 7769801808 := by
        calc
          (2 : ZMod 26771144429) ^ 911 = (2 : ZMod 26771144429) ^ (455 + 455 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 455 * (2 : ZMod 26771144429) ^ 455) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 7769801808 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 26771144429) ^ 1823 = 7405119536 := by
        calc
          (2 : ZMod 26771144429) ^ 1823 = (2 : ZMod 26771144429) ^ (911 + 911 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 911 * (2 : ZMod 26771144429) ^ 911) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 7405119536 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 26771144429) ^ 3647 = 25110841572 := by
        calc
          (2 : ZMod 26771144429) ^ 3647 = (2 : ZMod 26771144429) ^ (1823 + 1823 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1823 * (2 : ZMod 26771144429) ^ 1823) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 25110841572 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 26771144429) ^ 7294 = 3247643613 := by
        calc
          (2 : ZMod 26771144429) ^ 7294 = (2 : ZMod 26771144429) ^ (3647 + 3647) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 3647 * (2 : ZMod 26771144429) ^ 3647 := by rw [pow_add]
          _ = 3247643613 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 26771144429) ^ 14589 = 20756191375 := by
        calc
          (2 : ZMod 26771144429) ^ 14589 = (2 : ZMod 26771144429) ^ (7294 + 7294 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 7294 * (2 : ZMod 26771144429) ^ 7294) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 20756191375 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 26771144429) ^ 29178 = 1755504307 := by
        calc
          (2 : ZMod 26771144429) ^ 29178 = (2 : ZMod 26771144429) ^ (14589 + 14589) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 14589 * (2 : ZMod 26771144429) ^ 14589 := by rw [pow_add]
          _ = 1755504307 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 26771144429) ^ 58356 = 10752013259 := by
        calc
          (2 : ZMod 26771144429) ^ 58356 = (2 : ZMod 26771144429) ^ (29178 + 29178) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 29178 * (2 : ZMod 26771144429) ^ 29178 := by rw [pow_add]
          _ = 10752013259 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 26771144429) ^ 116712 = 11866820212 := by
        calc
          (2 : ZMod 26771144429) ^ 116712 = (2 : ZMod 26771144429) ^ (58356 + 58356) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 58356 * (2 : ZMod 26771144429) ^ 58356 := by rw [pow_add]
          _ = 11866820212 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 26771144429) ^ 233425 = 23356841183 := by
        calc
          (2 : ZMod 26771144429) ^ 233425 = (2 : ZMod 26771144429) ^ (116712 + 116712 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 116712 * (2 : ZMod 26771144429) ^ 116712) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 23356841183 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 26771144429) ^ 466851 = 8106340506 := by
        calc
          (2 : ZMod 26771144429) ^ 466851 = (2 : ZMod 26771144429) ^ (233425 + 233425 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 233425 * (2 : ZMod 26771144429) ^ 233425) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 8106340506 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 26771144429) ^ 933703 = 24866024298 := by
        calc
          (2 : ZMod 26771144429) ^ 933703 = (2 : ZMod 26771144429) ^ (466851 + 466851 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 466851 * (2 : ZMod 26771144429) ^ 466851) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 24866024298 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 26771144429) ^ 1867406 = 13589817833 := by
        calc
          (2 : ZMod 26771144429) ^ 1867406 = (2 : ZMod 26771144429) ^ (933703 + 933703) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 933703 * (2 : ZMod 26771144429) ^ 933703 := by rw [pow_add]
          _ = 13589817833 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 26771144429) ^ 3734813 = 19414044509 := by
        calc
          (2 : ZMod 26771144429) ^ 3734813 = (2 : ZMod 26771144429) ^ (1867406 + 1867406 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1867406 * (2 : ZMod 26771144429) ^ 1867406) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 19414044509 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 26771144429) ^ 7469627 = 15806189018 := by
        calc
          (2 : ZMod 26771144429) ^ 7469627 = (2 : ZMod 26771144429) ^ (3734813 + 3734813 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 3734813 * (2 : ZMod 26771144429) ^ 3734813) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 15806189018 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 26771144429) ^ 14939254 = 18876833026 := by
        calc
          (2 : ZMod 26771144429) ^ 14939254 = (2 : ZMod 26771144429) ^ (7469627 + 7469627) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 7469627 * (2 : ZMod 26771144429) ^ 7469627 := by rw [pow_add]
          _ = 18876833026 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 26771144429) ^ 29878509 = 9100079309 := by
        calc
          (2 : ZMod 26771144429) ^ 29878509 = (2 : ZMod 26771144429) ^ (14939254 + 14939254 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 14939254 * (2 : ZMod 26771144429) ^ 14939254) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 9100079309 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 26771144429) ^ 59757018 = 10648813281 := by
        calc
          (2 : ZMod 26771144429) ^ 59757018 = (2 : ZMod 26771144429) ^ (29878509 + 29878509) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 29878509 * (2 : ZMod 26771144429) ^ 29878509 := by rw [pow_add]
          _ = 10648813281 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 26771144429) ^ 119514037 = 25572026722 := by
        calc
          (2 : ZMod 26771144429) ^ 119514037 = (2 : ZMod 26771144429) ^ (59757018 + 59757018 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 59757018 * (2 : ZMod 26771144429) ^ 59757018) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 25572026722 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 26771144429) ^ 239028075 = 16112668249 := by
        calc
          (2 : ZMod 26771144429) ^ 239028075 = (2 : ZMod 26771144429) ^ (119514037 + 119514037 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 119514037 * (2 : ZMod 26771144429) ^ 119514037) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 16112668249 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 26771144429) ^ 478056150 = 19794089050 := by
        calc
          (2 : ZMod 26771144429) ^ 478056150 = (2 : ZMod 26771144429) ^ (239028075 + 239028075) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 239028075 * (2 : ZMod 26771144429) ^ 239028075 := by rw [pow_add]
          _ = 19794089050 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 26771144429) ^ 956112301 = 6336390561 := by
        calc
          (2 : ZMod 26771144429) ^ 956112301 = (2 : ZMod 26771144429) ^ (478056150 + 478056150 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 478056150 * (2 : ZMod 26771144429) ^ 478056150) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 6336390561 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 26771144429) ^ 1912224602 = 20899341722 := by
        calc
          (2 : ZMod 26771144429) ^ 1912224602 = (2 : ZMod 26771144429) ^ (956112301 + 956112301) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 956112301 * (2 : ZMod 26771144429) ^ 956112301 := by rw [pow_add]
          _ = 20899341722 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 26771144429) ^ 3824449204 = 4995334120 := by
        calc
          (2 : ZMod 26771144429) ^ 3824449204 = (2 : ZMod 26771144429) ^ (1912224602 + 1912224602) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 1912224602 * (2 : ZMod 26771144429) ^ 1912224602 := by rw [pow_add]
          _ = 4995334120 := by rw [factor_1_30]; decide
      change (2 : ZMod 26771144429) ^ 3824449204 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (2 : ZMod 26771144429) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 26771144429) ^ 2 = 4 := by
        calc
          (2 : ZMod 26771144429) ^ 2 = (2 : ZMod 26771144429) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 1 * (2 : ZMod 26771144429) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 26771144429) ^ 5 = 32 := by
        calc
          (2 : ZMod 26771144429) ^ 5 = (2 : ZMod 26771144429) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 2 * (2 : ZMod 26771144429) ^ 2) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 26771144429) ^ 10 = 1024 := by
        calc
          (2 : ZMod 26771144429) ^ 10 = (2 : ZMod 26771144429) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 5 * (2 : ZMod 26771144429) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 26771144429) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 26771144429) ^ 21 = (2 : ZMod 26771144429) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 10 * (2 : ZMod 26771144429) ^ 10) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 26771144429) ^ 43 = 15157649496 := by
        calc
          (2 : ZMod 26771144429) ^ 43 = (2 : ZMod 26771144429) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 21 * (2 : ZMod 26771144429) ^ 21) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 15157649496 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 26771144429) ^ 86 = 19821790093 := by
        calc
          (2 : ZMod 26771144429) ^ 86 = (2 : ZMod 26771144429) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 43 * (2 : ZMod 26771144429) ^ 43 := by rw [pow_add]
          _ = 19821790093 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 26771144429) ^ 172 = 15240766955 := by
        calc
          (2 : ZMod 26771144429) ^ 172 = (2 : ZMod 26771144429) ^ (86 + 86) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 86 * (2 : ZMod 26771144429) ^ 86 := by rw [pow_add]
          _ = 15240766955 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 26771144429) ^ 345 = 24203040320 := by
        calc
          (2 : ZMod 26771144429) ^ 345 = (2 : ZMod 26771144429) ^ (172 + 172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 172 * (2 : ZMod 26771144429) ^ 172) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 24203040320 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 26771144429) ^ 690 = 10647695341 := by
        calc
          (2 : ZMod 26771144429) ^ 690 = (2 : ZMod 26771144429) ^ (345 + 345) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 345 * (2 : ZMod 26771144429) ^ 345 := by rw [pow_add]
          _ = 10647695341 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 26771144429) ^ 1380 = 15185310677 := by
        calc
          (2 : ZMod 26771144429) ^ 1380 = (2 : ZMod 26771144429) ^ (690 + 690) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 690 * (2 : ZMod 26771144429) ^ 690 := by rw [pow_add]
          _ = 15185310677 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 26771144429) ^ 2760 = 12975611372 := by
        calc
          (2 : ZMod 26771144429) ^ 2760 = (2 : ZMod 26771144429) ^ (1380 + 1380) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 1380 * (2 : ZMod 26771144429) ^ 1380 := by rw [pow_add]
          _ = 12975611372 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 26771144429) ^ 5520 = 6293627578 := by
        calc
          (2 : ZMod 26771144429) ^ 5520 = (2 : ZMod 26771144429) ^ (2760 + 2760) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 2760 * (2 : ZMod 26771144429) ^ 2760 := by rw [pow_add]
          _ = 6293627578 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 26771144429) ^ 11040 = 7413474201 := by
        calc
          (2 : ZMod 26771144429) ^ 11040 = (2 : ZMod 26771144429) ^ (5520 + 5520) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 5520 * (2 : ZMod 26771144429) ^ 5520 := by rw [pow_add]
          _ = 7413474201 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 26771144429) ^ 22080 = 10114599657 := by
        calc
          (2 : ZMod 26771144429) ^ 22080 = (2 : ZMod 26771144429) ^ (11040 + 11040) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 11040 * (2 : ZMod 26771144429) ^ 11040 := by rw [pow_add]
          _ = 10114599657 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 26771144429) ^ 44161 = 20149954126 := by
        calc
          (2 : ZMod 26771144429) ^ 44161 = (2 : ZMod 26771144429) ^ (22080 + 22080 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 22080 * (2 : ZMod 26771144429) ^ 22080) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 20149954126 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 26771144429) ^ 88323 = 25737079963 := by
        calc
          (2 : ZMod 26771144429) ^ 88323 = (2 : ZMod 26771144429) ^ (44161 + 44161 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 44161 * (2 : ZMod 26771144429) ^ 44161) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 25737079963 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 26771144429) ^ 176646 = 17020967216 := by
        calc
          (2 : ZMod 26771144429) ^ 176646 = (2 : ZMod 26771144429) ^ (88323 + 88323) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 88323 * (2 : ZMod 26771144429) ^ 88323 := by rw [pow_add]
          _ = 17020967216 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 26771144429) ^ 353293 = 16420732669 := by
        calc
          (2 : ZMod 26771144429) ^ 353293 = (2 : ZMod 26771144429) ^ (176646 + 176646 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 176646 * (2 : ZMod 26771144429) ^ 176646) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 16420732669 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 26771144429) ^ 706586 = 11340103633 := by
        calc
          (2 : ZMod 26771144429) ^ 706586 = (2 : ZMod 26771144429) ^ (353293 + 353293) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 353293 * (2 : ZMod 26771144429) ^ 353293 := by rw [pow_add]
          _ = 11340103633 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 26771144429) ^ 1413172 = 18552356535 := by
        calc
          (2 : ZMod 26771144429) ^ 1413172 = (2 : ZMod 26771144429) ^ (706586 + 706586) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 706586 * (2 : ZMod 26771144429) ^ 706586 := by rw [pow_add]
          _ = 18552356535 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 26771144429) ^ 2826345 = 11144059893 := by
        calc
          (2 : ZMod 26771144429) ^ 2826345 = (2 : ZMod 26771144429) ^ (1413172 + 1413172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 1413172 * (2 : ZMod 26771144429) ^ 1413172) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 11144059893 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 26771144429) ^ 5652690 = 14980628750 := by
        calc
          (2 : ZMod 26771144429) ^ 5652690 = (2 : ZMod 26771144429) ^ (2826345 + 2826345) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 2826345 * (2 : ZMod 26771144429) ^ 2826345 := by rw [pow_add]
          _ = 14980628750 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 26771144429) ^ 11305381 = 19424078855 := by
        calc
          (2 : ZMod 26771144429) ^ 11305381 = (2 : ZMod 26771144429) ^ (5652690 + 5652690 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 5652690 * (2 : ZMod 26771144429) ^ 5652690) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 19424078855 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 26771144429) ^ 22610763 = 19769222805 := by
        calc
          (2 : ZMod 26771144429) ^ 22610763 = (2 : ZMod 26771144429) ^ (11305381 + 11305381 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 11305381 * (2 : ZMod 26771144429) ^ 11305381) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 19769222805 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 26771144429) ^ 45221527 = 11731377628 := by
        calc
          (2 : ZMod 26771144429) ^ 45221527 = (2 : ZMod 26771144429) ^ (22610763 + 22610763 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 22610763 * (2 : ZMod 26771144429) ^ 22610763) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 11731377628 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 26771144429) ^ 90443055 = 3170542155 := by
        calc
          (2 : ZMod 26771144429) ^ 90443055 = (2 : ZMod 26771144429) ^ (45221527 + 45221527 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 45221527 * (2 : ZMod 26771144429) ^ 45221527) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 3170542155 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 26771144429) ^ 180886111 = 6948337038 := by
        calc
          (2 : ZMod 26771144429) ^ 180886111 = (2 : ZMod 26771144429) ^ (90443055 + 90443055 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 90443055 * (2 : ZMod 26771144429) ^ 90443055) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 6948337038 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 26771144429) ^ 361772222 = 3914634264 := by
        calc
          (2 : ZMod 26771144429) ^ 361772222 = (2 : ZMod 26771144429) ^ (180886111 + 180886111) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 180886111 * (2 : ZMod 26771144429) ^ 180886111 := by rw [pow_add]
          _ = 3914634264 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 26771144429) ^ 723544444 = 10735010472 := by
        calc
          (2 : ZMod 26771144429) ^ 723544444 = (2 : ZMod 26771144429) ^ (361772222 + 361772222) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 361772222 * (2 : ZMod 26771144429) ^ 361772222 := by rw [pow_add]
          _ = 10735010472 := by rw [factor_2_28]; decide
      change (2 : ZMod 26771144429) ^ 723544444 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (2 : ZMod 26771144429) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 26771144429) ^ 2 = 4 := by
        calc
          (2 : ZMod 26771144429) ^ 2 = (2 : ZMod 26771144429) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 1 * (2 : ZMod 26771144429) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 26771144429) ^ 4 = 16 := by
        calc
          (2 : ZMod 26771144429) ^ 4 = (2 : ZMod 26771144429) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 2 * (2 : ZMod 26771144429) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 26771144429) ^ 8 = 256 := by
        calc
          (2 : ZMod 26771144429) ^ 8 = (2 : ZMod 26771144429) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 4 * (2 : ZMod 26771144429) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 26771144429) ^ 16 = 65536 := by
        calc
          (2 : ZMod 26771144429) ^ 16 = (2 : ZMod 26771144429) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 8 * (2 : ZMod 26771144429) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 26771144429) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 26771144429) ^ 32 = (2 : ZMod 26771144429) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 16 * (2 : ZMod 26771144429) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 26771144429) ^ 64 = 25458851795 := by
        calc
          (2 : ZMod 26771144429) ^ 64 = (2 : ZMod 26771144429) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 32 * (2 : ZMod 26771144429) ^ 32 := by rw [pow_add]
          _ = 25458851795 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 26771144429) ^ 129 = 23714788481 := by
        calc
          (2 : ZMod 26771144429) ^ 129 = (2 : ZMod 26771144429) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 64 * (2 : ZMod 26771144429) ^ 64) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 23714788481 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 26771144429) ^ 259 = 18179126750 := by
        calc
          (2 : ZMod 26771144429) ^ 259 = (2 : ZMod 26771144429) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = ((2 : ZMod 26771144429) ^ 129 * (2 : ZMod 26771144429) ^ 129) * (2 : ZMod 26771144429) := by rw [pow_succ, pow_add]
          _ = 18179126750 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 26771144429) ^ 518 = 2014829494 := by
        calc
          (2 : ZMod 26771144429) ^ 518 = (2 : ZMod 26771144429) ^ (259 + 259) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 259 * (2 : ZMod 26771144429) ^ 259 := by rw [pow_add]
          _ = 2014829494 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 26771144429) ^ 1036 = 18813280509 := by
        calc
          (2 : ZMod 26771144429) ^ 1036 = (2 : ZMod 26771144429) ^ (518 + 518) :=
            congrArg (fun n : ℕ => (2 : ZMod 26771144429) ^ n) (by norm_num)
          _ = (2 : ZMod 26771144429) ^ 518 * (2 : ZMod 26771144429) ^ 518 := by rw [pow_add]
          _ = 18813280509 := by rw [factor_3_9]; decide
      change (2 : ZMod 26771144429) ^ 1036 ≠ 1
      rw [factor_3_10]
      decide

#print axioms prime_lucas_26771144429

end TotientTailPeriodKiller
end Erdos249257
