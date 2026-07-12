import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_830406971 : Nat.Prime 830406971 := by
  apply lucas_primality 830406971 (6 : ZMod 830406971)
  ·
      have fermat_0 : (6 : ZMod 830406971) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 830406971) ^ 3 = 216 := by
        calc
          (6 : ZMod 830406971) ^ 3 = (6 : ZMod 830406971) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1 * (6 : ZMod 830406971) ^ 1) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 830406971) ^ 6 = 46656 := by
        calc
          (6 : ZMod 830406971) ^ 6 = (6 : ZMod 830406971) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 3 * (6 : ZMod 830406971) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 830406971) ^ 12 = 515968394 := by
        calc
          (6 : ZMod 830406971) ^ 12 = (6 : ZMod 830406971) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 6 * (6 : ZMod 830406971) ^ 6 := by rw [pow_add]
          _ = 515968394 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 830406971) ^ 24 = 759885408 := by
        calc
          (6 : ZMod 830406971) ^ 24 = (6 : ZMod 830406971) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 12 * (6 : ZMod 830406971) ^ 12 := by rw [pow_add]
          _ = 759885408 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 830406971) ^ 49 = 640700334 := by
        calc
          (6 : ZMod 830406971) ^ 49 = (6 : ZMod 830406971) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 24 * (6 : ZMod 830406971) ^ 24) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 640700334 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 830406971) ^ 98 = 661840791 := by
        calc
          (6 : ZMod 830406971) ^ 98 = (6 : ZMod 830406971) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 49 * (6 : ZMod 830406971) ^ 49 := by rw [pow_add]
          _ = 661840791 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 830406971) ^ 197 = 474638701 := by
        calc
          (6 : ZMod 830406971) ^ 197 = (6 : ZMod 830406971) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 98 * (6 : ZMod 830406971) ^ 98) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 474638701 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 830406971) ^ 395 = 135308793 := by
        calc
          (6 : ZMod 830406971) ^ 395 = (6 : ZMod 830406971) ^ (197 + 197 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 197 * (6 : ZMod 830406971) ^ 197) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 135308793 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 830406971) ^ 791 = 469155116 := by
        calc
          (6 : ZMod 830406971) ^ 791 = (6 : ZMod 830406971) ^ (395 + 395 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 395 * (6 : ZMod 830406971) ^ 395) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 469155116 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 830406971) ^ 1583 = 22547007 := by
        calc
          (6 : ZMod 830406971) ^ 1583 = (6 : ZMod 830406971) ^ (791 + 791 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 791 * (6 : ZMod 830406971) ^ 791) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 22547007 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 830406971) ^ 3167 = 764861470 := by
        calc
          (6 : ZMod 830406971) ^ 3167 = (6 : ZMod 830406971) ^ (1583 + 1583 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1583 * (6 : ZMod 830406971) ^ 1583) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 764861470 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 830406971) ^ 6335 = 580890408 := by
        calc
          (6 : ZMod 830406971) ^ 6335 = (6 : ZMod 830406971) ^ (3167 + 3167 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 3167 * (6 : ZMod 830406971) ^ 3167) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 580890408 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 830406971) ^ 12671 = 652084408 := by
        calc
          (6 : ZMod 830406971) ^ 12671 = (6 : ZMod 830406971) ^ (6335 + 6335 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 6335 * (6 : ZMod 830406971) ^ 6335) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 652084408 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 830406971) ^ 25342 = 405026624 := by
        calc
          (6 : ZMod 830406971) ^ 25342 = (6 : ZMod 830406971) ^ (12671 + 12671) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 12671 * (6 : ZMod 830406971) ^ 12671 := by rw [pow_add]
          _ = 405026624 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 830406971) ^ 50684 = 360168805 := by
        calc
          (6 : ZMod 830406971) ^ 50684 = (6 : ZMod 830406971) ^ (25342 + 25342) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 25342 * (6 : ZMod 830406971) ^ 25342 := by rw [pow_add]
          _ = 360168805 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 830406971) ^ 101368 = 674604046 := by
        calc
          (6 : ZMod 830406971) ^ 101368 = (6 : ZMod 830406971) ^ (50684 + 50684) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 50684 * (6 : ZMod 830406971) ^ 50684 := by rw [pow_add]
          _ = 674604046 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 830406971) ^ 202736 = 195888931 := by
        calc
          (6 : ZMod 830406971) ^ 202736 = (6 : ZMod 830406971) ^ (101368 + 101368) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 101368 * (6 : ZMod 830406971) ^ 101368 := by rw [pow_add]
          _ = 195888931 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 830406971) ^ 405472 = 758931634 := by
        calc
          (6 : ZMod 830406971) ^ 405472 = (6 : ZMod 830406971) ^ (202736 + 202736) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 202736 * (6 : ZMod 830406971) ^ 202736 := by rw [pow_add]
          _ = 758931634 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 830406971) ^ 810944 = 324369657 := by
        calc
          (6 : ZMod 830406971) ^ 810944 = (6 : ZMod 830406971) ^ (405472 + 405472) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 405472 * (6 : ZMod 830406971) ^ 405472 := by rw [pow_add]
          _ = 324369657 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 830406971) ^ 1621888 = 452084283 := by
        calc
          (6 : ZMod 830406971) ^ 1621888 = (6 : ZMod 830406971) ^ (810944 + 810944) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 810944 * (6 : ZMod 830406971) ^ 810944 := by rw [pow_add]
          _ = 452084283 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 830406971) ^ 3243777 = 599107710 := by
        calc
          (6 : ZMod 830406971) ^ 3243777 = (6 : ZMod 830406971) ^ (1621888 + 1621888 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1621888 * (6 : ZMod 830406971) ^ 1621888) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 599107710 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 830406971) ^ 6487554 = 366892345 := by
        calc
          (6 : ZMod 830406971) ^ 6487554 = (6 : ZMod 830406971) ^ (3243777 + 3243777) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 3243777 * (6 : ZMod 830406971) ^ 3243777 := by rw [pow_add]
          _ = 366892345 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 830406971) ^ 12975108 = 589517724 := by
        calc
          (6 : ZMod 830406971) ^ 12975108 = (6 : ZMod 830406971) ^ (6487554 + 6487554) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 6487554 * (6 : ZMod 830406971) ^ 6487554 := by rw [pow_add]
          _ = 589517724 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 830406971) ^ 25950217 = 538222536 := by
        calc
          (6 : ZMod 830406971) ^ 25950217 = (6 : ZMod 830406971) ^ (12975108 + 12975108 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 12975108 * (6 : ZMod 830406971) ^ 12975108) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 538222536 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 830406971) ^ 51900435 = 364072157 := by
        calc
          (6 : ZMod 830406971) ^ 51900435 = (6 : ZMod 830406971) ^ (25950217 + 25950217 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 25950217 * (6 : ZMod 830406971) ^ 25950217) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 364072157 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 830406971) ^ 103800871 = 404517062 := by
        calc
          (6 : ZMod 830406971) ^ 103800871 = (6 : ZMod 830406971) ^ (51900435 + 51900435 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 51900435 * (6 : ZMod 830406971) ^ 51900435) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 404517062 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 830406971) ^ 207601742 = 627357233 := by
        calc
          (6 : ZMod 830406971) ^ 207601742 = (6 : ZMod 830406971) ^ (103800871 + 103800871) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 103800871 * (6 : ZMod 830406971) ^ 103800871 := by rw [pow_add]
          _ = 627357233 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 830406971) ^ 415203485 = 830406970 := by
        calc
          (6 : ZMod 830406971) ^ 415203485 = (6 : ZMod 830406971) ^ (207601742 + 207601742 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 207601742 * (6 : ZMod 830406971) ^ 207601742) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 830406970 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 830406971) ^ 830406970 = 1 := by
        calc
          (6 : ZMod 830406971) ^ 830406970 = (6 : ZMod 830406971) ^ (415203485 + 415203485) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 415203485 * (6 : ZMod 830406971) ^ 415203485 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (19, 1), (43, 1), (101641, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (19, 1), (43, 1), (101641, 1)] : List FactorBlock).map factorBlockValue).prod = 830406971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 830406971) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 830406971) ^ 3 = 216 := by
        calc
          (6 : ZMod 830406971) ^ 3 = (6 : ZMod 830406971) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1 * (6 : ZMod 830406971) ^ 1) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 830406971) ^ 6 = 46656 := by
        calc
          (6 : ZMod 830406971) ^ 6 = (6 : ZMod 830406971) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 3 * (6 : ZMod 830406971) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 830406971) ^ 12 = 515968394 := by
        calc
          (6 : ZMod 830406971) ^ 12 = (6 : ZMod 830406971) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 6 * (6 : ZMod 830406971) ^ 6 := by rw [pow_add]
          _ = 515968394 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 830406971) ^ 24 = 759885408 := by
        calc
          (6 : ZMod 830406971) ^ 24 = (6 : ZMod 830406971) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 12 * (6 : ZMod 830406971) ^ 12 := by rw [pow_add]
          _ = 759885408 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 830406971) ^ 49 = 640700334 := by
        calc
          (6 : ZMod 830406971) ^ 49 = (6 : ZMod 830406971) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 24 * (6 : ZMod 830406971) ^ 24) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 640700334 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 830406971) ^ 98 = 661840791 := by
        calc
          (6 : ZMod 830406971) ^ 98 = (6 : ZMod 830406971) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 49 * (6 : ZMod 830406971) ^ 49 := by rw [pow_add]
          _ = 661840791 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 830406971) ^ 197 = 474638701 := by
        calc
          (6 : ZMod 830406971) ^ 197 = (6 : ZMod 830406971) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 98 * (6 : ZMod 830406971) ^ 98) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 474638701 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 830406971) ^ 395 = 135308793 := by
        calc
          (6 : ZMod 830406971) ^ 395 = (6 : ZMod 830406971) ^ (197 + 197 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 197 * (6 : ZMod 830406971) ^ 197) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 135308793 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 830406971) ^ 791 = 469155116 := by
        calc
          (6 : ZMod 830406971) ^ 791 = (6 : ZMod 830406971) ^ (395 + 395 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 395 * (6 : ZMod 830406971) ^ 395) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 469155116 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 830406971) ^ 1583 = 22547007 := by
        calc
          (6 : ZMod 830406971) ^ 1583 = (6 : ZMod 830406971) ^ (791 + 791 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 791 * (6 : ZMod 830406971) ^ 791) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 22547007 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 830406971) ^ 3167 = 764861470 := by
        calc
          (6 : ZMod 830406971) ^ 3167 = (6 : ZMod 830406971) ^ (1583 + 1583 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1583 * (6 : ZMod 830406971) ^ 1583) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 764861470 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 830406971) ^ 6335 = 580890408 := by
        calc
          (6 : ZMod 830406971) ^ 6335 = (6 : ZMod 830406971) ^ (3167 + 3167 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 3167 * (6 : ZMod 830406971) ^ 3167) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 580890408 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 830406971) ^ 12671 = 652084408 := by
        calc
          (6 : ZMod 830406971) ^ 12671 = (6 : ZMod 830406971) ^ (6335 + 6335 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 6335 * (6 : ZMod 830406971) ^ 6335) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 652084408 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 830406971) ^ 25342 = 405026624 := by
        calc
          (6 : ZMod 830406971) ^ 25342 = (6 : ZMod 830406971) ^ (12671 + 12671) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 12671 * (6 : ZMod 830406971) ^ 12671 := by rw [pow_add]
          _ = 405026624 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 830406971) ^ 50684 = 360168805 := by
        calc
          (6 : ZMod 830406971) ^ 50684 = (6 : ZMod 830406971) ^ (25342 + 25342) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 25342 * (6 : ZMod 830406971) ^ 25342 := by rw [pow_add]
          _ = 360168805 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 830406971) ^ 101368 = 674604046 := by
        calc
          (6 : ZMod 830406971) ^ 101368 = (6 : ZMod 830406971) ^ (50684 + 50684) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 50684 * (6 : ZMod 830406971) ^ 50684 := by rw [pow_add]
          _ = 674604046 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 830406971) ^ 202736 = 195888931 := by
        calc
          (6 : ZMod 830406971) ^ 202736 = (6 : ZMod 830406971) ^ (101368 + 101368) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 101368 * (6 : ZMod 830406971) ^ 101368 := by rw [pow_add]
          _ = 195888931 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 830406971) ^ 405472 = 758931634 := by
        calc
          (6 : ZMod 830406971) ^ 405472 = (6 : ZMod 830406971) ^ (202736 + 202736) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 202736 * (6 : ZMod 830406971) ^ 202736 := by rw [pow_add]
          _ = 758931634 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 830406971) ^ 810944 = 324369657 := by
        calc
          (6 : ZMod 830406971) ^ 810944 = (6 : ZMod 830406971) ^ (405472 + 405472) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 405472 * (6 : ZMod 830406971) ^ 405472 := by rw [pow_add]
          _ = 324369657 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 830406971) ^ 1621888 = 452084283 := by
        calc
          (6 : ZMod 830406971) ^ 1621888 = (6 : ZMod 830406971) ^ (810944 + 810944) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 810944 * (6 : ZMod 830406971) ^ 810944 := by rw [pow_add]
          _ = 452084283 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 830406971) ^ 3243777 = 599107710 := by
        calc
          (6 : ZMod 830406971) ^ 3243777 = (6 : ZMod 830406971) ^ (1621888 + 1621888 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1621888 * (6 : ZMod 830406971) ^ 1621888) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 599107710 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 830406971) ^ 6487554 = 366892345 := by
        calc
          (6 : ZMod 830406971) ^ 6487554 = (6 : ZMod 830406971) ^ (3243777 + 3243777) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 3243777 * (6 : ZMod 830406971) ^ 3243777 := by rw [pow_add]
          _ = 366892345 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 830406971) ^ 12975108 = 589517724 := by
        calc
          (6 : ZMod 830406971) ^ 12975108 = (6 : ZMod 830406971) ^ (6487554 + 6487554) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 6487554 * (6 : ZMod 830406971) ^ 6487554 := by rw [pow_add]
          _ = 589517724 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 830406971) ^ 25950217 = 538222536 := by
        calc
          (6 : ZMod 830406971) ^ 25950217 = (6 : ZMod 830406971) ^ (12975108 + 12975108 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 12975108 * (6 : ZMod 830406971) ^ 12975108) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 538222536 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 830406971) ^ 51900435 = 364072157 := by
        calc
          (6 : ZMod 830406971) ^ 51900435 = (6 : ZMod 830406971) ^ (25950217 + 25950217 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 25950217 * (6 : ZMod 830406971) ^ 25950217) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 364072157 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 830406971) ^ 103800871 = 404517062 := by
        calc
          (6 : ZMod 830406971) ^ 103800871 = (6 : ZMod 830406971) ^ (51900435 + 51900435 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 51900435 * (6 : ZMod 830406971) ^ 51900435) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 404517062 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 830406971) ^ 207601742 = 627357233 := by
        calc
          (6 : ZMod 830406971) ^ 207601742 = (6 : ZMod 830406971) ^ (103800871 + 103800871) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 103800871 * (6 : ZMod 830406971) ^ 103800871 := by rw [pow_add]
          _ = 627357233 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 830406971) ^ 415203485 = 830406970 := by
        calc
          (6 : ZMod 830406971) ^ 415203485 = (6 : ZMod 830406971) ^ (207601742 + 207601742 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 207601742 * (6 : ZMod 830406971) ^ 207601742) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 830406970 := by rw [factor_0_27]; decide
      change (6 : ZMod 830406971) ^ 415203485 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (6 : ZMod 830406971) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 830406971) ^ 2 = 36 := by
        calc
          (6 : ZMod 830406971) ^ 2 = (6 : ZMod 830406971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 1 * (6 : ZMod 830406971) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 830406971) ^ 4 = 1296 := by
        calc
          (6 : ZMod 830406971) ^ 4 = (6 : ZMod 830406971) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 2 * (6 : ZMod 830406971) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 830406971) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 830406971) ^ 9 = (6 : ZMod 830406971) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 4 * (6 : ZMod 830406971) ^ 4) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 830406971) ^ 19 = 461434928 := by
        calc
          (6 : ZMod 830406971) ^ 19 = (6 : ZMod 830406971) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 9 * (6 : ZMod 830406971) ^ 9) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 461434928 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 830406971) ^ 39 = 245370919 := by
        calc
          (6 : ZMod 830406971) ^ 39 = (6 : ZMod 830406971) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 19 * (6 : ZMod 830406971) ^ 19) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 245370919 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 830406971) ^ 79 = 334828572 := by
        calc
          (6 : ZMod 830406971) ^ 79 = (6 : ZMod 830406971) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 39 * (6 : ZMod 830406971) ^ 39) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 334828572 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 830406971) ^ 158 = 809048855 := by
        calc
          (6 : ZMod 830406971) ^ 158 = (6 : ZMod 830406971) ^ (79 + 79) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 79 * (6 : ZMod 830406971) ^ 79 := by rw [pow_add]
          _ = 809048855 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 830406971) ^ 316 = 827283055 := by
        calc
          (6 : ZMod 830406971) ^ 316 = (6 : ZMod 830406971) ^ (158 + 158) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 158 * (6 : ZMod 830406971) ^ 158 := by rw [pow_add]
          _ = 827283055 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 830406971) ^ 633 = 281118155 := by
        calc
          (6 : ZMod 830406971) ^ 633 = (6 : ZMod 830406971) ^ (316 + 316 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 316 * (6 : ZMod 830406971) ^ 316) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 281118155 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 830406971) ^ 1267 = 292813245 := by
        calc
          (6 : ZMod 830406971) ^ 1267 = (6 : ZMod 830406971) ^ (633 + 633 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 633 * (6 : ZMod 830406971) ^ 633) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 292813245 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 830406971) ^ 2534 = 294238693 := by
        calc
          (6 : ZMod 830406971) ^ 2534 = (6 : ZMod 830406971) ^ (1267 + 1267) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 1267 * (6 : ZMod 830406971) ^ 1267 := by rw [pow_add]
          _ = 294238693 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 830406971) ^ 5068 = 405189594 := by
        calc
          (6 : ZMod 830406971) ^ 5068 = (6 : ZMod 830406971) ^ (2534 + 2534) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 2534 * (6 : ZMod 830406971) ^ 2534 := by rw [pow_add]
          _ = 405189594 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 830406971) ^ 10136 = 775978468 := by
        calc
          (6 : ZMod 830406971) ^ 10136 = (6 : ZMod 830406971) ^ (5068 + 5068) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 5068 * (6 : ZMod 830406971) ^ 5068 := by rw [pow_add]
          _ = 775978468 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 830406971) ^ 20273 = 102623922 := by
        calc
          (6 : ZMod 830406971) ^ 20273 = (6 : ZMod 830406971) ^ (10136 + 10136 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 10136 * (6 : ZMod 830406971) ^ 10136) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 102623922 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 830406971) ^ 40547 = 104868406 := by
        calc
          (6 : ZMod 830406971) ^ 40547 = (6 : ZMod 830406971) ^ (20273 + 20273 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 20273 * (6 : ZMod 830406971) ^ 20273) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 104868406 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 830406971) ^ 81094 = 791890392 := by
        calc
          (6 : ZMod 830406971) ^ 81094 = (6 : ZMod 830406971) ^ (40547 + 40547) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 40547 * (6 : ZMod 830406971) ^ 40547 := by rw [pow_add]
          _ = 791890392 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 830406971) ^ 162188 = 652136886 := by
        calc
          (6 : ZMod 830406971) ^ 162188 = (6 : ZMod 830406971) ^ (81094 + 81094) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 81094 * (6 : ZMod 830406971) ^ 81094 := by rw [pow_add]
          _ = 652136886 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 830406971) ^ 324377 = 482004248 := by
        calc
          (6 : ZMod 830406971) ^ 324377 = (6 : ZMod 830406971) ^ (162188 + 162188 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 162188 * (6 : ZMod 830406971) ^ 162188) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 482004248 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 830406971) ^ 648755 = 325524359 := by
        calc
          (6 : ZMod 830406971) ^ 648755 = (6 : ZMod 830406971) ^ (324377 + 324377 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 324377 * (6 : ZMod 830406971) ^ 324377) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 325524359 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 830406971) ^ 1297510 = 574896641 := by
        calc
          (6 : ZMod 830406971) ^ 1297510 = (6 : ZMod 830406971) ^ (648755 + 648755) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 648755 * (6 : ZMod 830406971) ^ 648755 := by rw [pow_add]
          _ = 574896641 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 830406971) ^ 2595021 = 158693752 := by
        calc
          (6 : ZMod 830406971) ^ 2595021 = (6 : ZMod 830406971) ^ (1297510 + 1297510 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1297510 * (6 : ZMod 830406971) ^ 1297510) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 158693752 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 830406971) ^ 5190043 = 659409512 := by
        calc
          (6 : ZMod 830406971) ^ 5190043 = (6 : ZMod 830406971) ^ (2595021 + 2595021 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 2595021 * (6 : ZMod 830406971) ^ 2595021) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 659409512 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 830406971) ^ 10380087 = 128051707 := by
        calc
          (6 : ZMod 830406971) ^ 10380087 = (6 : ZMod 830406971) ^ (5190043 + 5190043 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 5190043 * (6 : ZMod 830406971) ^ 5190043) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 128051707 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 830406971) ^ 20760174 = 364852661 := by
        calc
          (6 : ZMod 830406971) ^ 20760174 = (6 : ZMod 830406971) ^ (10380087 + 10380087) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 10380087 * (6 : ZMod 830406971) ^ 10380087 := by rw [pow_add]
          _ = 364852661 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 830406971) ^ 41520348 = 656398586 := by
        calc
          (6 : ZMod 830406971) ^ 41520348 = (6 : ZMod 830406971) ^ (20760174 + 20760174) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 20760174 * (6 : ZMod 830406971) ^ 20760174 := by rw [pow_add]
          _ = 656398586 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 830406971) ^ 83040697 = 31856067 := by
        calc
          (6 : ZMod 830406971) ^ 83040697 = (6 : ZMod 830406971) ^ (41520348 + 41520348 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 41520348 * (6 : ZMod 830406971) ^ 41520348) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 31856067 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 830406971) ^ 166081394 = 200914287 := by
        calc
          (6 : ZMod 830406971) ^ 166081394 = (6 : ZMod 830406971) ^ (83040697 + 83040697) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 83040697 * (6 : ZMod 830406971) ^ 83040697 := by rw [pow_add]
          _ = 200914287 := by rw [factor_1_26]; decide
      change (6 : ZMod 830406971) ^ 166081394 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (6 : ZMod 830406971) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 830406971) ^ 2 = 36 := by
        calc
          (6 : ZMod 830406971) ^ 2 = (6 : ZMod 830406971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 1 * (6 : ZMod 830406971) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 830406971) ^ 5 = 7776 := by
        calc
          (6 : ZMod 830406971) ^ 5 = (6 : ZMod 830406971) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 2 * (6 : ZMod 830406971) ^ 2) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 830406971) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 830406971) ^ 10 = (6 : ZMod 830406971) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 5 * (6 : ZMod 830406971) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 830406971) ^ 20 = 277388655 := by
        calc
          (6 : ZMod 830406971) ^ 20 = (6 : ZMod 830406971) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 10 * (6 : ZMod 830406971) ^ 10 := by rw [pow_add]
          _ = 277388655 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 830406971) ^ 41 = 529283374 := by
        calc
          (6 : ZMod 830406971) ^ 41 = (6 : ZMod 830406971) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 20 * (6 : ZMod 830406971) ^ 20) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 529283374 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 830406971) ^ 83 = 465390450 := by
        calc
          (6 : ZMod 830406971) ^ 83 = (6 : ZMod 830406971) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 41 * (6 : ZMod 830406971) ^ 41) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 465390450 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 830406971) ^ 166 = 147783744 := by
        calc
          (6 : ZMod 830406971) ^ 166 = (6 : ZMod 830406971) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 83 * (6 : ZMod 830406971) ^ 83 := by rw [pow_add]
          _ = 147783744 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 830406971) ^ 333 = 265042700 := by
        calc
          (6 : ZMod 830406971) ^ 333 = (6 : ZMod 830406971) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 166 * (6 : ZMod 830406971) ^ 166) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 265042700 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 830406971) ^ 666 = 337761467 := by
        calc
          (6 : ZMod 830406971) ^ 666 = (6 : ZMod 830406971) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 333 * (6 : ZMod 830406971) ^ 333 := by rw [pow_add]
          _ = 337761467 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 830406971) ^ 1333 = 176576604 := by
        calc
          (6 : ZMod 830406971) ^ 1333 = (6 : ZMod 830406971) ^ (666 + 666 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 666 * (6 : ZMod 830406971) ^ 666) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 176576604 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 830406971) ^ 2667 = 211087259 := by
        calc
          (6 : ZMod 830406971) ^ 2667 = (6 : ZMod 830406971) ^ (1333 + 1333 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1333 * (6 : ZMod 830406971) ^ 1333) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 211087259 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 830406971) ^ 5335 = 543865804 := by
        calc
          (6 : ZMod 830406971) ^ 5335 = (6 : ZMod 830406971) ^ (2667 + 2667 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 2667 * (6 : ZMod 830406971) ^ 2667) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 543865804 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 830406971) ^ 10670 = 506348211 := by
        calc
          (6 : ZMod 830406971) ^ 10670 = (6 : ZMod 830406971) ^ (5335 + 5335) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 5335 * (6 : ZMod 830406971) ^ 5335 := by rw [pow_add]
          _ = 506348211 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 830406971) ^ 21340 = 581246020 := by
        calc
          (6 : ZMod 830406971) ^ 21340 = (6 : ZMod 830406971) ^ (10670 + 10670) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 10670 * (6 : ZMod 830406971) ^ 10670 := by rw [pow_add]
          _ = 581246020 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 830406971) ^ 42681 = 141886836 := by
        calc
          (6 : ZMod 830406971) ^ 42681 = (6 : ZMod 830406971) ^ (21340 + 21340 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 21340 * (6 : ZMod 830406971) ^ 21340) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 141886836 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 830406971) ^ 85362 = 816674974 := by
        calc
          (6 : ZMod 830406971) ^ 85362 = (6 : ZMod 830406971) ^ (42681 + 42681) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 42681 * (6 : ZMod 830406971) ^ 42681 := by rw [pow_add]
          _ = 816674974 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 830406971) ^ 170725 = 203055742 := by
        calc
          (6 : ZMod 830406971) ^ 170725 = (6 : ZMod 830406971) ^ (85362 + 85362 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 85362 * (6 : ZMod 830406971) ^ 85362) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 203055742 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 830406971) ^ 341450 = 44033902 := by
        calc
          (6 : ZMod 830406971) ^ 341450 = (6 : ZMod 830406971) ^ (170725 + 170725) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 170725 * (6 : ZMod 830406971) ^ 170725 := by rw [pow_add]
          _ = 44033902 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 830406971) ^ 682900 = 25793053 := by
        calc
          (6 : ZMod 830406971) ^ 682900 = (6 : ZMod 830406971) ^ (341450 + 341450) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 341450 * (6 : ZMod 830406971) ^ 341450 := by rw [pow_add]
          _ = 25793053 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 830406971) ^ 1365800 = 207837188 := by
        calc
          (6 : ZMod 830406971) ^ 1365800 = (6 : ZMod 830406971) ^ (682900 + 682900) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 682900 * (6 : ZMod 830406971) ^ 682900 := by rw [pow_add]
          _ = 207837188 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 830406971) ^ 2731601 = 340205214 := by
        calc
          (6 : ZMod 830406971) ^ 2731601 = (6 : ZMod 830406971) ^ (1365800 + 1365800 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1365800 * (6 : ZMod 830406971) ^ 1365800) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 340205214 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 830406971) ^ 5463203 = 466171380 := by
        calc
          (6 : ZMod 830406971) ^ 5463203 = (6 : ZMod 830406971) ^ (2731601 + 2731601 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 2731601 * (6 : ZMod 830406971) ^ 2731601) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 466171380 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 830406971) ^ 10926407 = 344911956 := by
        calc
          (6 : ZMod 830406971) ^ 10926407 = (6 : ZMod 830406971) ^ (5463203 + 5463203 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 5463203 * (6 : ZMod 830406971) ^ 5463203) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 344911956 := by rw [factor_2_22]; decide
      have factor_2_24 : (6 : ZMod 830406971) ^ 21852815 = 793129009 := by
        calc
          (6 : ZMod 830406971) ^ 21852815 = (6 : ZMod 830406971) ^ (10926407 + 10926407 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 10926407 * (6 : ZMod 830406971) ^ 10926407) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 793129009 := by rw [factor_2_23]; decide
      have factor_2_25 : (6 : ZMod 830406971) ^ 43705630 = 244439552 := by
        calc
          (6 : ZMod 830406971) ^ 43705630 = (6 : ZMod 830406971) ^ (21852815 + 21852815) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 21852815 * (6 : ZMod 830406971) ^ 21852815 := by rw [pow_add]
          _ = 244439552 := by rw [factor_2_24]; decide
      change (6 : ZMod 830406971) ^ 43705630 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (6 : ZMod 830406971) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 830406971) ^ 2 = 36 := by
        calc
          (6 : ZMod 830406971) ^ 2 = (6 : ZMod 830406971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 1 * (6 : ZMod 830406971) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 830406971) ^ 4 = 1296 := by
        calc
          (6 : ZMod 830406971) ^ 4 = (6 : ZMod 830406971) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 2 * (6 : ZMod 830406971) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 830406971) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 830406971) ^ 9 = (6 : ZMod 830406971) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 4 * (6 : ZMod 830406971) ^ 4) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 830406971) ^ 18 = 353708145 := by
        calc
          (6 : ZMod 830406971) ^ 18 = (6 : ZMod 830406971) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 9 * (6 : ZMod 830406971) ^ 9 := by rw [pow_add]
          _ = 353708145 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 830406971) ^ 36 = 443250799 := by
        calc
          (6 : ZMod 830406971) ^ 36 = (6 : ZMod 830406971) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 18 * (6 : ZMod 830406971) ^ 18 := by rw [pow_add]
          _ = 443250799 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 830406971) ^ 73 = 29267916 := by
        calc
          (6 : ZMod 830406971) ^ 73 = (6 : ZMod 830406971) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 36 * (6 : ZMod 830406971) ^ 36) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 29267916 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 830406971) ^ 147 = 172857993 := by
        calc
          (6 : ZMod 830406971) ^ 147 = (6 : ZMod 830406971) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 73 * (6 : ZMod 830406971) ^ 73) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 172857993 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 830406971) ^ 294 = 254339400 := by
        calc
          (6 : ZMod 830406971) ^ 294 = (6 : ZMod 830406971) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 147 * (6 : ZMod 830406971) ^ 147 := by rw [pow_add]
          _ = 254339400 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 830406971) ^ 589 = 456659808 := by
        calc
          (6 : ZMod 830406971) ^ 589 = (6 : ZMod 830406971) ^ (294 + 294 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 294 * (6 : ZMod 830406971) ^ 294) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 456659808 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 830406971) ^ 1178 = 7504729 := by
        calc
          (6 : ZMod 830406971) ^ 1178 = (6 : ZMod 830406971) ^ (589 + 589) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 589 * (6 : ZMod 830406971) ^ 589 := by rw [pow_add]
          _ = 7504729 := by rw [factor_3_9]; decide
      have factor_3_11 : (6 : ZMod 830406971) ^ 2357 = 761808877 := by
        calc
          (6 : ZMod 830406971) ^ 2357 = (6 : ZMod 830406971) ^ (1178 + 1178 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1178 * (6 : ZMod 830406971) ^ 1178) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 761808877 := by rw [factor_3_10]; decide
      have factor_3_12 : (6 : ZMod 830406971) ^ 4714 = 592809209 := by
        calc
          (6 : ZMod 830406971) ^ 4714 = (6 : ZMod 830406971) ^ (2357 + 2357) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 2357 * (6 : ZMod 830406971) ^ 2357 := by rw [pow_add]
          _ = 592809209 := by rw [factor_3_11]; decide
      have factor_3_13 : (6 : ZMod 830406971) ^ 9429 = 688446513 := by
        calc
          (6 : ZMod 830406971) ^ 9429 = (6 : ZMod 830406971) ^ (4714 + 4714 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 4714 * (6 : ZMod 830406971) ^ 4714) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 688446513 := by rw [factor_3_12]; decide
      have factor_3_14 : (6 : ZMod 830406971) ^ 18859 = 371522965 := by
        calc
          (6 : ZMod 830406971) ^ 18859 = (6 : ZMod 830406971) ^ (9429 + 9429 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 9429 * (6 : ZMod 830406971) ^ 9429) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 371522965 := by rw [factor_3_13]; decide
      have factor_3_15 : (6 : ZMod 830406971) ^ 37718 = 180206629 := by
        calc
          (6 : ZMod 830406971) ^ 37718 = (6 : ZMod 830406971) ^ (18859 + 18859) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 18859 * (6 : ZMod 830406971) ^ 18859 := by rw [pow_add]
          _ = 180206629 := by rw [factor_3_14]; decide
      have factor_3_16 : (6 : ZMod 830406971) ^ 75436 = 175935288 := by
        calc
          (6 : ZMod 830406971) ^ 75436 = (6 : ZMod 830406971) ^ (37718 + 37718) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 37718 * (6 : ZMod 830406971) ^ 37718 := by rw [pow_add]
          _ = 175935288 := by rw [factor_3_15]; decide
      have factor_3_17 : (6 : ZMod 830406971) ^ 150873 = 209094948 := by
        calc
          (6 : ZMod 830406971) ^ 150873 = (6 : ZMod 830406971) ^ (75436 + 75436 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 75436 * (6 : ZMod 830406971) ^ 75436) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 209094948 := by rw [factor_3_16]; decide
      have factor_3_18 : (6 : ZMod 830406971) ^ 301746 = 278703671 := by
        calc
          (6 : ZMod 830406971) ^ 301746 = (6 : ZMod 830406971) ^ (150873 + 150873) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 150873 * (6 : ZMod 830406971) ^ 150873 := by rw [pow_add]
          _ = 278703671 := by rw [factor_3_17]; decide
      have factor_3_19 : (6 : ZMod 830406971) ^ 603493 = 223206999 := by
        calc
          (6 : ZMod 830406971) ^ 603493 = (6 : ZMod 830406971) ^ (301746 + 301746 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 301746 * (6 : ZMod 830406971) ^ 301746) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 223206999 := by rw [factor_3_18]; decide
      have factor_3_20 : (6 : ZMod 830406971) ^ 1206986 = 379425339 := by
        calc
          (6 : ZMod 830406971) ^ 1206986 = (6 : ZMod 830406971) ^ (603493 + 603493) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 603493 * (6 : ZMod 830406971) ^ 603493 := by rw [pow_add]
          _ = 379425339 := by rw [factor_3_19]; decide
      have factor_3_21 : (6 : ZMod 830406971) ^ 2413973 = 182102984 := by
        calc
          (6 : ZMod 830406971) ^ 2413973 = (6 : ZMod 830406971) ^ (1206986 + 1206986 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1206986 * (6 : ZMod 830406971) ^ 1206986) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 182102984 := by rw [factor_3_20]; decide
      have factor_3_22 : (6 : ZMod 830406971) ^ 4827947 = 167893727 := by
        calc
          (6 : ZMod 830406971) ^ 4827947 = (6 : ZMod 830406971) ^ (2413973 + 2413973 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 2413973 * (6 : ZMod 830406971) ^ 2413973) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 167893727 := by rw [factor_3_21]; decide
      have factor_3_23 : (6 : ZMod 830406971) ^ 9655895 = 713941261 := by
        calc
          (6 : ZMod 830406971) ^ 9655895 = (6 : ZMod 830406971) ^ (4827947 + 4827947 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 4827947 * (6 : ZMod 830406971) ^ 4827947) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 713941261 := by rw [factor_3_22]; decide
      have factor_3_24 : (6 : ZMod 830406971) ^ 19311790 = 528585846 := by
        calc
          (6 : ZMod 830406971) ^ 19311790 = (6 : ZMod 830406971) ^ (9655895 + 9655895) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 9655895 * (6 : ZMod 830406971) ^ 9655895 := by rw [pow_add]
          _ = 528585846 := by rw [factor_3_23]; decide
      change (6 : ZMod 830406971) ^ 19311790 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (6 : ZMod 830406971) ^ 1 = 6 := by norm_num
      have factor_4_1 : (6 : ZMod 830406971) ^ 3 = 216 := by
        calc
          (6 : ZMod 830406971) ^ 3 = (6 : ZMod 830406971) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 1 * (6 : ZMod 830406971) ^ 1) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_4_0]; decide
      have factor_4_2 : (6 : ZMod 830406971) ^ 7 = 279936 := by
        calc
          (6 : ZMod 830406971) ^ 7 = (6 : ZMod 830406971) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 3 * (6 : ZMod 830406971) ^ 3) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_4_1]; decide
      have factor_4_3 : (6 : ZMod 830406971) ^ 15 = 174638990 := by
        calc
          (6 : ZMod 830406971) ^ 15 = (6 : ZMod 830406971) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 7 * (6 : ZMod 830406971) ^ 7) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 174638990 := by rw [factor_4_2]; decide
      have factor_4_4 : (6 : ZMod 830406971) ^ 31 = 571068586 := by
        calc
          (6 : ZMod 830406971) ^ 31 = (6 : ZMod 830406971) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 15 * (6 : ZMod 830406971) ^ 15) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 571068586 := by rw [factor_4_3]; decide
      have factor_4_5 : (6 : ZMod 830406971) ^ 63 = 20002387 := by
        calc
          (6 : ZMod 830406971) ^ 63 = (6 : ZMod 830406971) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 31 * (6 : ZMod 830406971) ^ 31) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 20002387 := by rw [factor_4_4]; decide
      have factor_4_6 : (6 : ZMod 830406971) ^ 127 = 56547945 := by
        calc
          (6 : ZMod 830406971) ^ 127 = (6 : ZMod 830406971) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 63 * (6 : ZMod 830406971) ^ 63) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 56547945 := by rw [factor_4_5]; decide
      have factor_4_7 : (6 : ZMod 830406971) ^ 255 = 558658532 := by
        calc
          (6 : ZMod 830406971) ^ 255 = (6 : ZMod 830406971) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 127 * (6 : ZMod 830406971) ^ 127) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 558658532 := by rw [factor_4_6]; decide
      have factor_4_8 : (6 : ZMod 830406971) ^ 510 = 738482039 := by
        calc
          (6 : ZMod 830406971) ^ 510 = (6 : ZMod 830406971) ^ (255 + 255) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 255 * (6 : ZMod 830406971) ^ 255 := by rw [pow_add]
          _ = 738482039 := by rw [factor_4_7]; decide
      have factor_4_9 : (6 : ZMod 830406971) ^ 1021 = 120873828 := by
        calc
          (6 : ZMod 830406971) ^ 1021 = (6 : ZMod 830406971) ^ (510 + 510 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 510 * (6 : ZMod 830406971) ^ 510) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 120873828 := by rw [factor_4_8]; decide
      have factor_4_10 : (6 : ZMod 830406971) ^ 2042 = 609869111 := by
        calc
          (6 : ZMod 830406971) ^ 2042 = (6 : ZMod 830406971) ^ (1021 + 1021) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 1021 * (6 : ZMod 830406971) ^ 1021 := by rw [pow_add]
          _ = 609869111 := by rw [factor_4_9]; decide
      have factor_4_11 : (6 : ZMod 830406971) ^ 4085 = 318085978 := by
        calc
          (6 : ZMod 830406971) ^ 4085 = (6 : ZMod 830406971) ^ (2042 + 2042 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = ((6 : ZMod 830406971) ^ 2042 * (6 : ZMod 830406971) ^ 2042) * (6 : ZMod 830406971) := by rw [pow_succ, pow_add]
          _ = 318085978 := by rw [factor_4_10]; decide
      have factor_4_12 : (6 : ZMod 830406971) ^ 8170 = 760798952 := by
        calc
          (6 : ZMod 830406971) ^ 8170 = (6 : ZMod 830406971) ^ (4085 + 4085) :=
            congrArg (fun n : ℕ => (6 : ZMod 830406971) ^ n) (by norm_num)
          _ = (6 : ZMod 830406971) ^ 4085 * (6 : ZMod 830406971) ^ 4085 := by rw [pow_add]
          _ = 760798952 := by rw [factor_4_11]; decide
      change (6 : ZMod 830406971) ^ 8170 ≠ 1
      rw [factor_4_12]
      decide

#print axioms prime_lucas_830406971

end TotientTailPeriodKiller
end Erdos249257
