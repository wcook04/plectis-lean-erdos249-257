import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_20097919679 : Nat.Prime 20097919679 := by
  apply lucas_primality 20097919679 (13 : ZMod 20097919679)
  ·
      have fermat_0 : (13 : ZMod 20097919679) ^ 1 = 13 := by norm_num
      have fermat_1 : (13 : ZMod 20097919679) ^ 2 = 169 := by
        calc
          (13 : ZMod 20097919679) ^ 2 = (13 : ZMod 20097919679) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 1 * (13 : ZMod 20097919679) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [fermat_0]; decide
      have fermat_2 : (13 : ZMod 20097919679) ^ 4 = 28561 := by
        calc
          (13 : ZMod 20097919679) ^ 4 = (13 : ZMod 20097919679) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 2 * (13 : ZMod 20097919679) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [fermat_1]; decide
      have fermat_3 : (13 : ZMod 20097919679) ^ 9 = 10604499373 := by
        calc
          (13 : ZMod 20097919679) ^ 9 = (13 : ZMod 20097919679) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 4 * (13 : ZMod 20097919679) ^ 4) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 10604499373 := by rw [fermat_2]; decide
      have fermat_4 : (13 : ZMod 20097919679) ^ 18 = 1169241888 := by
        calc
          (13 : ZMod 20097919679) ^ 18 = (13 : ZMod 20097919679) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 9 * (13 : ZMod 20097919679) ^ 9 := by rw [pow_add]
          _ = 1169241888 := by rw [fermat_3]; decide
      have fermat_5 : (13 : ZMod 20097919679) ^ 37 = 2786882785 := by
        calc
          (13 : ZMod 20097919679) ^ 37 = (13 : ZMod 20097919679) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 18 * (13 : ZMod 20097919679) ^ 18) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 2786882785 := by rw [fermat_4]; decide
      have fermat_6 : (13 : ZMod 20097919679) ^ 74 = 8398603185 := by
        calc
          (13 : ZMod 20097919679) ^ 74 = (13 : ZMod 20097919679) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 37 * (13 : ZMod 20097919679) ^ 37 := by rw [pow_add]
          _ = 8398603185 := by rw [fermat_5]; decide
      have fermat_7 : (13 : ZMod 20097919679) ^ 149 = 18965316468 := by
        calc
          (13 : ZMod 20097919679) ^ 149 = (13 : ZMod 20097919679) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 74 * (13 : ZMod 20097919679) ^ 74) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 18965316468 := by rw [fermat_6]; decide
      have fermat_8 : (13 : ZMod 20097919679) ^ 299 = 17659571206 := by
        calc
          (13 : ZMod 20097919679) ^ 299 = (13 : ZMod 20097919679) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 149 * (13 : ZMod 20097919679) ^ 149) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 17659571206 := by rw [fermat_7]; decide
      have fermat_9 : (13 : ZMod 20097919679) ^ 598 = 15625673319 := by
        calc
          (13 : ZMod 20097919679) ^ 598 = (13 : ZMod 20097919679) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 299 * (13 : ZMod 20097919679) ^ 299 := by rw [pow_add]
          _ = 15625673319 := by rw [fermat_8]; decide
      have fermat_10 : (13 : ZMod 20097919679) ^ 1197 = 12108604739 := by
        calc
          (13 : ZMod 20097919679) ^ 1197 = (13 : ZMod 20097919679) ^ (598 + 598 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 598 * (13 : ZMod 20097919679) ^ 598) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 12108604739 := by rw [fermat_9]; decide
      have fermat_11 : (13 : ZMod 20097919679) ^ 2395 = 11815825467 := by
        calc
          (13 : ZMod 20097919679) ^ 2395 = (13 : ZMod 20097919679) ^ (1197 + 1197 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1197 * (13 : ZMod 20097919679) ^ 1197) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 11815825467 := by rw [fermat_10]; decide
      have fermat_12 : (13 : ZMod 20097919679) ^ 4791 = 18609572600 := by
        calc
          (13 : ZMod 20097919679) ^ 4791 = (13 : ZMod 20097919679) ^ (2395 + 2395 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 2395 * (13 : ZMod 20097919679) ^ 2395) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 18609572600 := by rw [fermat_11]; decide
      have fermat_13 : (13 : ZMod 20097919679) ^ 9583 = 231263551 := by
        calc
          (13 : ZMod 20097919679) ^ 9583 = (13 : ZMod 20097919679) ^ (4791 + 4791 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 4791 * (13 : ZMod 20097919679) ^ 4791) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 231263551 := by rw [fermat_12]; decide
      have fermat_14 : (13 : ZMod 20097919679) ^ 19166 = 14788306553 := by
        calc
          (13 : ZMod 20097919679) ^ 19166 = (13 : ZMod 20097919679) ^ (9583 + 9583) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 9583 * (13 : ZMod 20097919679) ^ 9583 := by rw [pow_add]
          _ = 14788306553 := by rw [fermat_13]; decide
      have fermat_15 : (13 : ZMod 20097919679) ^ 38333 = 11133139471 := by
        calc
          (13 : ZMod 20097919679) ^ 38333 = (13 : ZMod 20097919679) ^ (19166 + 19166 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 19166 * (13 : ZMod 20097919679) ^ 19166) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 11133139471 := by rw [fermat_14]; decide
      have fermat_16 : (13 : ZMod 20097919679) ^ 76667 = 16538000516 := by
        calc
          (13 : ZMod 20097919679) ^ 76667 = (13 : ZMod 20097919679) ^ (38333 + 38333 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 38333 * (13 : ZMod 20097919679) ^ 38333) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 16538000516 := by rw [fermat_15]; decide
      have fermat_17 : (13 : ZMod 20097919679) ^ 153334 = 3506941680 := by
        calc
          (13 : ZMod 20097919679) ^ 153334 = (13 : ZMod 20097919679) ^ (76667 + 76667) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 76667 * (13 : ZMod 20097919679) ^ 76667 := by rw [pow_add]
          _ = 3506941680 := by rw [fermat_16]; decide
      have fermat_18 : (13 : ZMod 20097919679) ^ 306669 = 12976048232 := by
        calc
          (13 : ZMod 20097919679) ^ 306669 = (13 : ZMod 20097919679) ^ (153334 + 153334 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 153334 * (13 : ZMod 20097919679) ^ 153334) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 12976048232 := by rw [fermat_17]; decide
      have fermat_19 : (13 : ZMod 20097919679) ^ 613339 = 882230908 := by
        calc
          (13 : ZMod 20097919679) ^ 613339 = (13 : ZMod 20097919679) ^ (306669 + 306669 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 306669 * (13 : ZMod 20097919679) ^ 306669) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 882230908 := by rw [fermat_18]; decide
      have fermat_20 : (13 : ZMod 20097919679) ^ 1226679 = 3260811100 := by
        calc
          (13 : ZMod 20097919679) ^ 1226679 = (13 : ZMod 20097919679) ^ (613339 + 613339 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 613339 * (13 : ZMod 20097919679) ^ 613339) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 3260811100 := by rw [fermat_19]; decide
      have fermat_21 : (13 : ZMod 20097919679) ^ 2453359 = 8377910577 := by
        calc
          (13 : ZMod 20097919679) ^ 2453359 = (13 : ZMod 20097919679) ^ (1226679 + 1226679 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1226679 * (13 : ZMod 20097919679) ^ 1226679) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 8377910577 := by rw [fermat_20]; decide
      have fermat_22 : (13 : ZMod 20097919679) ^ 4906718 = 19294664419 := by
        calc
          (13 : ZMod 20097919679) ^ 4906718 = (13 : ZMod 20097919679) ^ (2453359 + 2453359) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 2453359 * (13 : ZMod 20097919679) ^ 2453359 := by rw [pow_add]
          _ = 19294664419 := by rw [fermat_21]; decide
      have fermat_23 : (13 : ZMod 20097919679) ^ 9813437 = 2868635504 := by
        calc
          (13 : ZMod 20097919679) ^ 9813437 = (13 : ZMod 20097919679) ^ (4906718 + 4906718 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 4906718 * (13 : ZMod 20097919679) ^ 4906718) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 2868635504 := by rw [fermat_22]; decide
      have fermat_24 : (13 : ZMod 20097919679) ^ 19626874 = 17102567483 := by
        calc
          (13 : ZMod 20097919679) ^ 19626874 = (13 : ZMod 20097919679) ^ (9813437 + 9813437) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 9813437 * (13 : ZMod 20097919679) ^ 9813437 := by rw [pow_add]
          _ = 17102567483 := by rw [fermat_23]; decide
      have fermat_25 : (13 : ZMod 20097919679) ^ 39253749 = 14672610098 := by
        calc
          (13 : ZMod 20097919679) ^ 39253749 = (13 : ZMod 20097919679) ^ (19626874 + 19626874 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 19626874 * (13 : ZMod 20097919679) ^ 19626874) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 14672610098 := by rw [fermat_24]; decide
      have fermat_26 : (13 : ZMod 20097919679) ^ 78507498 = 10699529893 := by
        calc
          (13 : ZMod 20097919679) ^ 78507498 = (13 : ZMod 20097919679) ^ (39253749 + 39253749) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 39253749 * (13 : ZMod 20097919679) ^ 39253749 := by rw [pow_add]
          _ = 10699529893 := by rw [fermat_25]; decide
      have fermat_27 : (13 : ZMod 20097919679) ^ 157014997 = 970449679 := by
        calc
          (13 : ZMod 20097919679) ^ 157014997 = (13 : ZMod 20097919679) ^ (78507498 + 78507498 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 78507498 * (13 : ZMod 20097919679) ^ 78507498) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 970449679 := by rw [fermat_26]; decide
      have fermat_28 : (13 : ZMod 20097919679) ^ 314029994 = 963568488 := by
        calc
          (13 : ZMod 20097919679) ^ 314029994 = (13 : ZMod 20097919679) ^ (157014997 + 157014997) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 157014997 * (13 : ZMod 20097919679) ^ 157014997 := by rw [pow_add]
          _ = 963568488 := by rw [fermat_27]; decide
      have fermat_29 : (13 : ZMod 20097919679) ^ 628059989 = 3280972803 := by
        calc
          (13 : ZMod 20097919679) ^ 628059989 = (13 : ZMod 20097919679) ^ (314029994 + 314029994 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 314029994 * (13 : ZMod 20097919679) ^ 314029994) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 3280972803 := by rw [fermat_28]; decide
      have fermat_30 : (13 : ZMod 20097919679) ^ 1256119979 = 12234359700 := by
        calc
          (13 : ZMod 20097919679) ^ 1256119979 = (13 : ZMod 20097919679) ^ (628059989 + 628059989 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 628059989 * (13 : ZMod 20097919679) ^ 628059989) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 12234359700 := by rw [fermat_29]; decide
      have fermat_31 : (13 : ZMod 20097919679) ^ 2512239959 = 4814815387 := by
        calc
          (13 : ZMod 20097919679) ^ 2512239959 = (13 : ZMod 20097919679) ^ (1256119979 + 1256119979 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1256119979 * (13 : ZMod 20097919679) ^ 1256119979) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 4814815387 := by rw [fermat_30]; decide
      have fermat_32 : (13 : ZMod 20097919679) ^ 5024479919 = 2816748510 := by
        calc
          (13 : ZMod 20097919679) ^ 5024479919 = (13 : ZMod 20097919679) ^ (2512239959 + 2512239959 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 2512239959 * (13 : ZMod 20097919679) ^ 2512239959) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 2816748510 := by rw [fermat_31]; decide
      have fermat_33 : (13 : ZMod 20097919679) ^ 10048959839 = 20097919678 := by
        calc
          (13 : ZMod 20097919679) ^ 10048959839 = (13 : ZMod 20097919679) ^ (5024479919 + 5024479919 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 5024479919 * (13 : ZMod 20097919679) ^ 5024479919) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 20097919678 := by rw [fermat_32]; decide
      have fermat_34 : (13 : ZMod 20097919679) ^ 20097919678 = 1 := by
        calc
          (13 : ZMod 20097919679) ^ 20097919678 = (13 : ZMod 20097919679) ^ (10048959839 + 10048959839) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 10048959839 * (13 : ZMod 20097919679) ^ 10048959839 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (233, 1), (313, 1), (137791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (233, 1), (313, 1), (137791, 1)] : List FactorBlock).map factorBlockValue).prod = 20097919679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (13 : ZMod 20097919679) ^ 1 = 13 := by norm_num
      have factor_0_1 : (13 : ZMod 20097919679) ^ 2 = 169 := by
        calc
          (13 : ZMod 20097919679) ^ 2 = (13 : ZMod 20097919679) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 1 * (13 : ZMod 20097919679) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_0_0]; decide
      have factor_0_2 : (13 : ZMod 20097919679) ^ 4 = 28561 := by
        calc
          (13 : ZMod 20097919679) ^ 4 = (13 : ZMod 20097919679) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 2 * (13 : ZMod 20097919679) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_0_1]; decide
      have factor_0_3 : (13 : ZMod 20097919679) ^ 9 = 10604499373 := by
        calc
          (13 : ZMod 20097919679) ^ 9 = (13 : ZMod 20097919679) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 4 * (13 : ZMod 20097919679) ^ 4) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 10604499373 := by rw [factor_0_2]; decide
      have factor_0_4 : (13 : ZMod 20097919679) ^ 18 = 1169241888 := by
        calc
          (13 : ZMod 20097919679) ^ 18 = (13 : ZMod 20097919679) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 9 * (13 : ZMod 20097919679) ^ 9 := by rw [pow_add]
          _ = 1169241888 := by rw [factor_0_3]; decide
      have factor_0_5 : (13 : ZMod 20097919679) ^ 37 = 2786882785 := by
        calc
          (13 : ZMod 20097919679) ^ 37 = (13 : ZMod 20097919679) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 18 * (13 : ZMod 20097919679) ^ 18) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 2786882785 := by rw [factor_0_4]; decide
      have factor_0_6 : (13 : ZMod 20097919679) ^ 74 = 8398603185 := by
        calc
          (13 : ZMod 20097919679) ^ 74 = (13 : ZMod 20097919679) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 37 * (13 : ZMod 20097919679) ^ 37 := by rw [pow_add]
          _ = 8398603185 := by rw [factor_0_5]; decide
      have factor_0_7 : (13 : ZMod 20097919679) ^ 149 = 18965316468 := by
        calc
          (13 : ZMod 20097919679) ^ 149 = (13 : ZMod 20097919679) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 74 * (13 : ZMod 20097919679) ^ 74) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 18965316468 := by rw [factor_0_6]; decide
      have factor_0_8 : (13 : ZMod 20097919679) ^ 299 = 17659571206 := by
        calc
          (13 : ZMod 20097919679) ^ 299 = (13 : ZMod 20097919679) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 149 * (13 : ZMod 20097919679) ^ 149) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 17659571206 := by rw [factor_0_7]; decide
      have factor_0_9 : (13 : ZMod 20097919679) ^ 598 = 15625673319 := by
        calc
          (13 : ZMod 20097919679) ^ 598 = (13 : ZMod 20097919679) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 299 * (13 : ZMod 20097919679) ^ 299 := by rw [pow_add]
          _ = 15625673319 := by rw [factor_0_8]; decide
      have factor_0_10 : (13 : ZMod 20097919679) ^ 1197 = 12108604739 := by
        calc
          (13 : ZMod 20097919679) ^ 1197 = (13 : ZMod 20097919679) ^ (598 + 598 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 598 * (13 : ZMod 20097919679) ^ 598) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 12108604739 := by rw [factor_0_9]; decide
      have factor_0_11 : (13 : ZMod 20097919679) ^ 2395 = 11815825467 := by
        calc
          (13 : ZMod 20097919679) ^ 2395 = (13 : ZMod 20097919679) ^ (1197 + 1197 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1197 * (13 : ZMod 20097919679) ^ 1197) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 11815825467 := by rw [factor_0_10]; decide
      have factor_0_12 : (13 : ZMod 20097919679) ^ 4791 = 18609572600 := by
        calc
          (13 : ZMod 20097919679) ^ 4791 = (13 : ZMod 20097919679) ^ (2395 + 2395 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 2395 * (13 : ZMod 20097919679) ^ 2395) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 18609572600 := by rw [factor_0_11]; decide
      have factor_0_13 : (13 : ZMod 20097919679) ^ 9583 = 231263551 := by
        calc
          (13 : ZMod 20097919679) ^ 9583 = (13 : ZMod 20097919679) ^ (4791 + 4791 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 4791 * (13 : ZMod 20097919679) ^ 4791) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 231263551 := by rw [factor_0_12]; decide
      have factor_0_14 : (13 : ZMod 20097919679) ^ 19166 = 14788306553 := by
        calc
          (13 : ZMod 20097919679) ^ 19166 = (13 : ZMod 20097919679) ^ (9583 + 9583) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 9583 * (13 : ZMod 20097919679) ^ 9583 := by rw [pow_add]
          _ = 14788306553 := by rw [factor_0_13]; decide
      have factor_0_15 : (13 : ZMod 20097919679) ^ 38333 = 11133139471 := by
        calc
          (13 : ZMod 20097919679) ^ 38333 = (13 : ZMod 20097919679) ^ (19166 + 19166 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 19166 * (13 : ZMod 20097919679) ^ 19166) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 11133139471 := by rw [factor_0_14]; decide
      have factor_0_16 : (13 : ZMod 20097919679) ^ 76667 = 16538000516 := by
        calc
          (13 : ZMod 20097919679) ^ 76667 = (13 : ZMod 20097919679) ^ (38333 + 38333 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 38333 * (13 : ZMod 20097919679) ^ 38333) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 16538000516 := by rw [factor_0_15]; decide
      have factor_0_17 : (13 : ZMod 20097919679) ^ 153334 = 3506941680 := by
        calc
          (13 : ZMod 20097919679) ^ 153334 = (13 : ZMod 20097919679) ^ (76667 + 76667) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 76667 * (13 : ZMod 20097919679) ^ 76667 := by rw [pow_add]
          _ = 3506941680 := by rw [factor_0_16]; decide
      have factor_0_18 : (13 : ZMod 20097919679) ^ 306669 = 12976048232 := by
        calc
          (13 : ZMod 20097919679) ^ 306669 = (13 : ZMod 20097919679) ^ (153334 + 153334 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 153334 * (13 : ZMod 20097919679) ^ 153334) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 12976048232 := by rw [factor_0_17]; decide
      have factor_0_19 : (13 : ZMod 20097919679) ^ 613339 = 882230908 := by
        calc
          (13 : ZMod 20097919679) ^ 613339 = (13 : ZMod 20097919679) ^ (306669 + 306669 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 306669 * (13 : ZMod 20097919679) ^ 306669) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 882230908 := by rw [factor_0_18]; decide
      have factor_0_20 : (13 : ZMod 20097919679) ^ 1226679 = 3260811100 := by
        calc
          (13 : ZMod 20097919679) ^ 1226679 = (13 : ZMod 20097919679) ^ (613339 + 613339 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 613339 * (13 : ZMod 20097919679) ^ 613339) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 3260811100 := by rw [factor_0_19]; decide
      have factor_0_21 : (13 : ZMod 20097919679) ^ 2453359 = 8377910577 := by
        calc
          (13 : ZMod 20097919679) ^ 2453359 = (13 : ZMod 20097919679) ^ (1226679 + 1226679 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1226679 * (13 : ZMod 20097919679) ^ 1226679) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 8377910577 := by rw [factor_0_20]; decide
      have factor_0_22 : (13 : ZMod 20097919679) ^ 4906718 = 19294664419 := by
        calc
          (13 : ZMod 20097919679) ^ 4906718 = (13 : ZMod 20097919679) ^ (2453359 + 2453359) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 2453359 * (13 : ZMod 20097919679) ^ 2453359 := by rw [pow_add]
          _ = 19294664419 := by rw [factor_0_21]; decide
      have factor_0_23 : (13 : ZMod 20097919679) ^ 9813437 = 2868635504 := by
        calc
          (13 : ZMod 20097919679) ^ 9813437 = (13 : ZMod 20097919679) ^ (4906718 + 4906718 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 4906718 * (13 : ZMod 20097919679) ^ 4906718) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 2868635504 := by rw [factor_0_22]; decide
      have factor_0_24 : (13 : ZMod 20097919679) ^ 19626874 = 17102567483 := by
        calc
          (13 : ZMod 20097919679) ^ 19626874 = (13 : ZMod 20097919679) ^ (9813437 + 9813437) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 9813437 * (13 : ZMod 20097919679) ^ 9813437 := by rw [pow_add]
          _ = 17102567483 := by rw [factor_0_23]; decide
      have factor_0_25 : (13 : ZMod 20097919679) ^ 39253749 = 14672610098 := by
        calc
          (13 : ZMod 20097919679) ^ 39253749 = (13 : ZMod 20097919679) ^ (19626874 + 19626874 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 19626874 * (13 : ZMod 20097919679) ^ 19626874) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 14672610098 := by rw [factor_0_24]; decide
      have factor_0_26 : (13 : ZMod 20097919679) ^ 78507498 = 10699529893 := by
        calc
          (13 : ZMod 20097919679) ^ 78507498 = (13 : ZMod 20097919679) ^ (39253749 + 39253749) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 39253749 * (13 : ZMod 20097919679) ^ 39253749 := by rw [pow_add]
          _ = 10699529893 := by rw [factor_0_25]; decide
      have factor_0_27 : (13 : ZMod 20097919679) ^ 157014997 = 970449679 := by
        calc
          (13 : ZMod 20097919679) ^ 157014997 = (13 : ZMod 20097919679) ^ (78507498 + 78507498 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 78507498 * (13 : ZMod 20097919679) ^ 78507498) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 970449679 := by rw [factor_0_26]; decide
      have factor_0_28 : (13 : ZMod 20097919679) ^ 314029994 = 963568488 := by
        calc
          (13 : ZMod 20097919679) ^ 314029994 = (13 : ZMod 20097919679) ^ (157014997 + 157014997) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 157014997 * (13 : ZMod 20097919679) ^ 157014997 := by rw [pow_add]
          _ = 963568488 := by rw [factor_0_27]; decide
      have factor_0_29 : (13 : ZMod 20097919679) ^ 628059989 = 3280972803 := by
        calc
          (13 : ZMod 20097919679) ^ 628059989 = (13 : ZMod 20097919679) ^ (314029994 + 314029994 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 314029994 * (13 : ZMod 20097919679) ^ 314029994) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 3280972803 := by rw [factor_0_28]; decide
      have factor_0_30 : (13 : ZMod 20097919679) ^ 1256119979 = 12234359700 := by
        calc
          (13 : ZMod 20097919679) ^ 1256119979 = (13 : ZMod 20097919679) ^ (628059989 + 628059989 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 628059989 * (13 : ZMod 20097919679) ^ 628059989) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 12234359700 := by rw [factor_0_29]; decide
      have factor_0_31 : (13 : ZMod 20097919679) ^ 2512239959 = 4814815387 := by
        calc
          (13 : ZMod 20097919679) ^ 2512239959 = (13 : ZMod 20097919679) ^ (1256119979 + 1256119979 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1256119979 * (13 : ZMod 20097919679) ^ 1256119979) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 4814815387 := by rw [factor_0_30]; decide
      have factor_0_32 : (13 : ZMod 20097919679) ^ 5024479919 = 2816748510 := by
        calc
          (13 : ZMod 20097919679) ^ 5024479919 = (13 : ZMod 20097919679) ^ (2512239959 + 2512239959 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 2512239959 * (13 : ZMod 20097919679) ^ 2512239959) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 2816748510 := by rw [factor_0_31]; decide
      have factor_0_33 : (13 : ZMod 20097919679) ^ 10048959839 = 20097919678 := by
        calc
          (13 : ZMod 20097919679) ^ 10048959839 = (13 : ZMod 20097919679) ^ (5024479919 + 5024479919 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 5024479919 * (13 : ZMod 20097919679) ^ 5024479919) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 20097919678 := by rw [factor_0_32]; decide
      change (13 : ZMod 20097919679) ^ 10048959839 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (13 : ZMod 20097919679) ^ 1 = 13 := by norm_num
      have factor_1_1 : (13 : ZMod 20097919679) ^ 2 = 169 := by
        calc
          (13 : ZMod 20097919679) ^ 2 = (13 : ZMod 20097919679) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 1 * (13 : ZMod 20097919679) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_1_0]; decide
      have factor_1_2 : (13 : ZMod 20097919679) ^ 5 = 371293 := by
        calc
          (13 : ZMod 20097919679) ^ 5 = (13 : ZMod 20097919679) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 2 * (13 : ZMod 20097919679) ^ 2) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_1_1]; decide
      have factor_1_3 : (13 : ZMod 20097919679) ^ 10 = 17270973775 := by
        calc
          (13 : ZMod 20097919679) ^ 10 = (13 : ZMod 20097919679) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 5 * (13 : ZMod 20097919679) ^ 5 := by rw [pow_add]
          _ = 17270973775 := by rw [factor_1_2]; decide
      have factor_1_4 : (13 : ZMod 20097919679) ^ 20 = 16720601961 := by
        calc
          (13 : ZMod 20097919679) ^ 20 = (13 : ZMod 20097919679) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 10 * (13 : ZMod 20097919679) ^ 10 := by rw [pow_add]
          _ = 16720601961 := by rw [factor_1_3]; decide
      have factor_1_5 : (13 : ZMod 20097919679) ^ 41 = 8397293545 := by
        calc
          (13 : ZMod 20097919679) ^ 41 = (13 : ZMod 20097919679) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 20 * (13 : ZMod 20097919679) ^ 20) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 8397293545 := by rw [factor_1_4]; decide
      have factor_1_6 : (13 : ZMod 20097919679) ^ 82 = 15060381928 := by
        calc
          (13 : ZMod 20097919679) ^ 82 = (13 : ZMod 20097919679) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 41 * (13 : ZMod 20097919679) ^ 41 := by rw [pow_add]
          _ = 15060381928 := by rw [factor_1_5]; decide
      have factor_1_7 : (13 : ZMod 20097919679) ^ 164 = 7511476660 := by
        calc
          (13 : ZMod 20097919679) ^ 164 = (13 : ZMod 20097919679) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 82 * (13 : ZMod 20097919679) ^ 82 := by rw [pow_add]
          _ = 7511476660 := by rw [factor_1_6]; decide
      have factor_1_8 : (13 : ZMod 20097919679) ^ 329 = 18381365716 := by
        calc
          (13 : ZMod 20097919679) ^ 329 = (13 : ZMod 20097919679) ^ (164 + 164 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 164 * (13 : ZMod 20097919679) ^ 164) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 18381365716 := by rw [factor_1_7]; decide
      have factor_1_9 : (13 : ZMod 20097919679) ^ 658 = 16506759123 := by
        calc
          (13 : ZMod 20097919679) ^ 658 = (13 : ZMod 20097919679) ^ (329 + 329) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 329 * (13 : ZMod 20097919679) ^ 329 := by rw [pow_add]
          _ = 16506759123 := by rw [factor_1_8]; decide
      have factor_1_10 : (13 : ZMod 20097919679) ^ 1316 = 14355605507 := by
        calc
          (13 : ZMod 20097919679) ^ 1316 = (13 : ZMod 20097919679) ^ (658 + 658) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 658 * (13 : ZMod 20097919679) ^ 658 := by rw [pow_add]
          _ = 14355605507 := by rw [factor_1_9]; decide
      have factor_1_11 : (13 : ZMod 20097919679) ^ 2632 = 14537322743 := by
        calc
          (13 : ZMod 20097919679) ^ 2632 = (13 : ZMod 20097919679) ^ (1316 + 1316) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 1316 * (13 : ZMod 20097919679) ^ 1316 := by rw [pow_add]
          _ = 14537322743 := by rw [factor_1_10]; decide
      have factor_1_12 : (13 : ZMod 20097919679) ^ 5264 = 1653961399 := by
        calc
          (13 : ZMod 20097919679) ^ 5264 = (13 : ZMod 20097919679) ^ (2632 + 2632) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 2632 * (13 : ZMod 20097919679) ^ 2632 := by rw [pow_add]
          _ = 1653961399 := by rw [factor_1_11]; decide
      have factor_1_13 : (13 : ZMod 20097919679) ^ 10529 = 14910707281 := by
        calc
          (13 : ZMod 20097919679) ^ 10529 = (13 : ZMod 20097919679) ^ (5264 + 5264 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 5264 * (13 : ZMod 20097919679) ^ 5264) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 14910707281 := by rw [factor_1_12]; decide
      have factor_1_14 : (13 : ZMod 20097919679) ^ 21058 = 17749749464 := by
        calc
          (13 : ZMod 20097919679) ^ 21058 = (13 : ZMod 20097919679) ^ (10529 + 10529) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 10529 * (13 : ZMod 20097919679) ^ 10529 := by rw [pow_add]
          _ = 17749749464 := by rw [factor_1_13]; decide
      have factor_1_15 : (13 : ZMod 20097919679) ^ 42117 = 14738528052 := by
        calc
          (13 : ZMod 20097919679) ^ 42117 = (13 : ZMod 20097919679) ^ (21058 + 21058 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 21058 * (13 : ZMod 20097919679) ^ 21058) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 14738528052 := by rw [factor_1_14]; decide
      have factor_1_16 : (13 : ZMod 20097919679) ^ 84235 = 11741366460 := by
        calc
          (13 : ZMod 20097919679) ^ 84235 = (13 : ZMod 20097919679) ^ (42117 + 42117 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 42117 * (13 : ZMod 20097919679) ^ 42117) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 11741366460 := by rw [factor_1_15]; decide
      have factor_1_17 : (13 : ZMod 20097919679) ^ 168471 = 4610854015 := by
        calc
          (13 : ZMod 20097919679) ^ 168471 = (13 : ZMod 20097919679) ^ (84235 + 84235 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 84235 * (13 : ZMod 20097919679) ^ 84235) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 4610854015 := by rw [factor_1_16]; decide
      have factor_1_18 : (13 : ZMod 20097919679) ^ 336942 = 5213253974 := by
        calc
          (13 : ZMod 20097919679) ^ 336942 = (13 : ZMod 20097919679) ^ (168471 + 168471) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 168471 * (13 : ZMod 20097919679) ^ 168471 := by rw [pow_add]
          _ = 5213253974 := by rw [factor_1_17]; decide
      have factor_1_19 : (13 : ZMod 20097919679) ^ 673884 = 3333347344 := by
        calc
          (13 : ZMod 20097919679) ^ 673884 = (13 : ZMod 20097919679) ^ (336942 + 336942) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 336942 * (13 : ZMod 20097919679) ^ 336942 := by rw [pow_add]
          _ = 3333347344 := by rw [factor_1_18]; decide
      have factor_1_20 : (13 : ZMod 20097919679) ^ 1347768 = 2022936280 := by
        calc
          (13 : ZMod 20097919679) ^ 1347768 = (13 : ZMod 20097919679) ^ (673884 + 673884) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 673884 * (13 : ZMod 20097919679) ^ 673884 := by rw [pow_add]
          _ = 2022936280 := by rw [factor_1_19]; decide
      have factor_1_21 : (13 : ZMod 20097919679) ^ 2695536 = 15443584655 := by
        calc
          (13 : ZMod 20097919679) ^ 2695536 = (13 : ZMod 20097919679) ^ (1347768 + 1347768) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 1347768 * (13 : ZMod 20097919679) ^ 1347768 := by rw [pow_add]
          _ = 15443584655 := by rw [factor_1_20]; decide
      have factor_1_22 : (13 : ZMod 20097919679) ^ 5391072 = 8025030854 := by
        calc
          (13 : ZMod 20097919679) ^ 5391072 = (13 : ZMod 20097919679) ^ (2695536 + 2695536) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 2695536 * (13 : ZMod 20097919679) ^ 2695536 := by rw [pow_add]
          _ = 8025030854 := by rw [factor_1_21]; decide
      have factor_1_23 : (13 : ZMod 20097919679) ^ 10782145 = 5722849370 := by
        calc
          (13 : ZMod 20097919679) ^ 10782145 = (13 : ZMod 20097919679) ^ (5391072 + 5391072 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 5391072 * (13 : ZMod 20097919679) ^ 5391072) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 5722849370 := by rw [factor_1_22]; decide
      have factor_1_24 : (13 : ZMod 20097919679) ^ 21564291 = 2170927361 := by
        calc
          (13 : ZMod 20097919679) ^ 21564291 = (13 : ZMod 20097919679) ^ (10782145 + 10782145 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 10782145 * (13 : ZMod 20097919679) ^ 10782145) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 2170927361 := by rw [factor_1_23]; decide
      have factor_1_25 : (13 : ZMod 20097919679) ^ 43128583 = 1674665486 := by
        calc
          (13 : ZMod 20097919679) ^ 43128583 = (13 : ZMod 20097919679) ^ (21564291 + 21564291 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 21564291 * (13 : ZMod 20097919679) ^ 21564291) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 1674665486 := by rw [factor_1_24]; decide
      have factor_1_26 : (13 : ZMod 20097919679) ^ 86257166 = 19410847184 := by
        calc
          (13 : ZMod 20097919679) ^ 86257166 = (13 : ZMod 20097919679) ^ (43128583 + 43128583) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 43128583 * (13 : ZMod 20097919679) ^ 43128583 := by rw [pow_add]
          _ = 19410847184 := by rw [factor_1_25]; decide
      change (13 : ZMod 20097919679) ^ 86257166 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (13 : ZMod 20097919679) ^ 1 = 13 := by norm_num
      have factor_2_1 : (13 : ZMod 20097919679) ^ 3 = 2197 := by
        calc
          (13 : ZMod 20097919679) ^ 3 = (13 : ZMod 20097919679) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1 * (13 : ZMod 20097919679) ^ 1) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_2_0]; decide
      have factor_2_2 : (13 : ZMod 20097919679) ^ 7 = 62748517 := by
        calc
          (13 : ZMod 20097919679) ^ 7 = (13 : ZMod 20097919679) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 3 * (13 : ZMod 20097919679) ^ 3) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 62748517 := by rw [factor_2_1]; decide
      have factor_2_3 : (13 : ZMod 20097919679) ^ 15 = 8727621582 := by
        calc
          (13 : ZMod 20097919679) ^ 15 = (13 : ZMod 20097919679) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 7 * (13 : ZMod 20097919679) ^ 7) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 8727621582 := by rw [factor_2_2]; decide
      have factor_2_4 : (13 : ZMod 20097919679) ^ 30 = 14392781404 := by
        calc
          (13 : ZMod 20097919679) ^ 30 = (13 : ZMod 20097919679) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 15 * (13 : ZMod 20097919679) ^ 15 := by rw [pow_add]
          _ = 14392781404 := by rw [factor_2_3]; decide
      have factor_2_5 : (13 : ZMod 20097919679) ^ 61 = 15738592756 := by
        calc
          (13 : ZMod 20097919679) ^ 61 = (13 : ZMod 20097919679) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 30 * (13 : ZMod 20097919679) ^ 30) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 15738592756 := by rw [factor_2_4]; decide
      have factor_2_6 : (13 : ZMod 20097919679) ^ 122 = 11142726017 := by
        calc
          (13 : ZMod 20097919679) ^ 122 = (13 : ZMod 20097919679) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 61 * (13 : ZMod 20097919679) ^ 61 := by rw [pow_add]
          _ = 11142726017 := by rw [factor_2_5]; decide
      have factor_2_7 : (13 : ZMod 20097919679) ^ 244 = 7738099016 := by
        calc
          (13 : ZMod 20097919679) ^ 244 = (13 : ZMod 20097919679) ^ (122 + 122) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 122 * (13 : ZMod 20097919679) ^ 122 := by rw [pow_add]
          _ = 7738099016 := by rw [factor_2_6]; decide
      have factor_2_8 : (13 : ZMod 20097919679) ^ 489 = 3315415024 := by
        calc
          (13 : ZMod 20097919679) ^ 489 = (13 : ZMod 20097919679) ^ (244 + 244 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 244 * (13 : ZMod 20097919679) ^ 244) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 3315415024 := by rw [factor_2_7]; decide
      have factor_2_9 : (13 : ZMod 20097919679) ^ 979 = 8584689594 := by
        calc
          (13 : ZMod 20097919679) ^ 979 = (13 : ZMod 20097919679) ^ (489 + 489 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 489 * (13 : ZMod 20097919679) ^ 489) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 8584689594 := by rw [factor_2_8]; decide
      have factor_2_10 : (13 : ZMod 20097919679) ^ 1959 = 16982964454 := by
        calc
          (13 : ZMod 20097919679) ^ 1959 = (13 : ZMod 20097919679) ^ (979 + 979 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 979 * (13 : ZMod 20097919679) ^ 979) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 16982964454 := by rw [factor_2_9]; decide
      have factor_2_11 : (13 : ZMod 20097919679) ^ 3919 = 19662298629 := by
        calc
          (13 : ZMod 20097919679) ^ 3919 = (13 : ZMod 20097919679) ^ (1959 + 1959 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1959 * (13 : ZMod 20097919679) ^ 1959) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 19662298629 := by rw [factor_2_10]; decide
      have factor_2_12 : (13 : ZMod 20097919679) ^ 7838 = 16110482476 := by
        calc
          (13 : ZMod 20097919679) ^ 7838 = (13 : ZMod 20097919679) ^ (3919 + 3919) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 3919 * (13 : ZMod 20097919679) ^ 3919 := by rw [pow_add]
          _ = 16110482476 := by rw [factor_2_11]; decide
      have factor_2_13 : (13 : ZMod 20097919679) ^ 15676 = 18399576561 := by
        calc
          (13 : ZMod 20097919679) ^ 15676 = (13 : ZMod 20097919679) ^ (7838 + 7838) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 7838 * (13 : ZMod 20097919679) ^ 7838 := by rw [pow_add]
          _ = 18399576561 := by rw [factor_2_12]; decide
      have factor_2_14 : (13 : ZMod 20097919679) ^ 31352 = 3823818860 := by
        calc
          (13 : ZMod 20097919679) ^ 31352 = (13 : ZMod 20097919679) ^ (15676 + 15676) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 15676 * (13 : ZMod 20097919679) ^ 15676 := by rw [pow_add]
          _ = 3823818860 := by rw [factor_2_13]; decide
      have factor_2_15 : (13 : ZMod 20097919679) ^ 62705 = 10742959208 := by
        calc
          (13 : ZMod 20097919679) ^ 62705 = (13 : ZMod 20097919679) ^ (31352 + 31352 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 31352 * (13 : ZMod 20097919679) ^ 31352) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 10742959208 := by rw [factor_2_14]; decide
      have factor_2_16 : (13 : ZMod 20097919679) ^ 125411 = 13644976806 := by
        calc
          (13 : ZMod 20097919679) ^ 125411 = (13 : ZMod 20097919679) ^ (62705 + 62705 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 62705 * (13 : ZMod 20097919679) ^ 62705) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 13644976806 := by rw [factor_2_15]; decide
      have factor_2_17 : (13 : ZMod 20097919679) ^ 250822 = 7442556545 := by
        calc
          (13 : ZMod 20097919679) ^ 250822 = (13 : ZMod 20097919679) ^ (125411 + 125411) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 125411 * (13 : ZMod 20097919679) ^ 125411 := by rw [pow_add]
          _ = 7442556545 := by rw [factor_2_16]; decide
      have factor_2_18 : (13 : ZMod 20097919679) ^ 501645 = 9817996562 := by
        calc
          (13 : ZMod 20097919679) ^ 501645 = (13 : ZMod 20097919679) ^ (250822 + 250822 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 250822 * (13 : ZMod 20097919679) ^ 250822) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 9817996562 := by rw [factor_2_17]; decide
      have factor_2_19 : (13 : ZMod 20097919679) ^ 1003290 = 1480582373 := by
        calc
          (13 : ZMod 20097919679) ^ 1003290 = (13 : ZMod 20097919679) ^ (501645 + 501645) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 501645 * (13 : ZMod 20097919679) ^ 501645 := by rw [pow_add]
          _ = 1480582373 := by rw [factor_2_18]; decide
      have factor_2_20 : (13 : ZMod 20097919679) ^ 2006581 = 19238383498 := by
        calc
          (13 : ZMod 20097919679) ^ 2006581 = (13 : ZMod 20097919679) ^ (1003290 + 1003290 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1003290 * (13 : ZMod 20097919679) ^ 1003290) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 19238383498 := by rw [factor_2_19]; decide
      have factor_2_21 : (13 : ZMod 20097919679) ^ 4013162 = 4849671306 := by
        calc
          (13 : ZMod 20097919679) ^ 4013162 = (13 : ZMod 20097919679) ^ (2006581 + 2006581) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 2006581 * (13 : ZMod 20097919679) ^ 2006581 := by rw [pow_add]
          _ = 4849671306 := by rw [factor_2_20]; decide
      have factor_2_22 : (13 : ZMod 20097919679) ^ 8026325 = 8606789857 := by
        calc
          (13 : ZMod 20097919679) ^ 8026325 = (13 : ZMod 20097919679) ^ (4013162 + 4013162 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 4013162 * (13 : ZMod 20097919679) ^ 4013162) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 8606789857 := by rw [factor_2_21]; decide
      have factor_2_23 : (13 : ZMod 20097919679) ^ 16052651 = 18191127390 := by
        calc
          (13 : ZMod 20097919679) ^ 16052651 = (13 : ZMod 20097919679) ^ (8026325 + 8026325 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 8026325 * (13 : ZMod 20097919679) ^ 8026325) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 18191127390 := by rw [factor_2_22]; decide
      have factor_2_24 : (13 : ZMod 20097919679) ^ 32105303 = 17405759015 := by
        calc
          (13 : ZMod 20097919679) ^ 32105303 = (13 : ZMod 20097919679) ^ (16052651 + 16052651 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 16052651 * (13 : ZMod 20097919679) ^ 16052651) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 17405759015 := by rw [factor_2_23]; decide
      have factor_2_25 : (13 : ZMod 20097919679) ^ 64210606 = 2132856314 := by
        calc
          (13 : ZMod 20097919679) ^ 64210606 = (13 : ZMod 20097919679) ^ (32105303 + 32105303) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 32105303 * (13 : ZMod 20097919679) ^ 32105303 := by rw [pow_add]
          _ = 2132856314 := by rw [factor_2_24]; decide
      change (13 : ZMod 20097919679) ^ 64210606 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (13 : ZMod 20097919679) ^ 1 = 13 := by norm_num
      have factor_3_1 : (13 : ZMod 20097919679) ^ 2 = 169 := by
        calc
          (13 : ZMod 20097919679) ^ 2 = (13 : ZMod 20097919679) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 1 * (13 : ZMod 20097919679) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_3_0]; decide
      have factor_3_2 : (13 : ZMod 20097919679) ^ 4 = 28561 := by
        calc
          (13 : ZMod 20097919679) ^ 4 = (13 : ZMod 20097919679) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 2 * (13 : ZMod 20097919679) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_3_1]; decide
      have factor_3_3 : (13 : ZMod 20097919679) ^ 8 = 815730721 := by
        calc
          (13 : ZMod 20097919679) ^ 8 = (13 : ZMod 20097919679) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 4 * (13 : ZMod 20097919679) ^ 4 := by rw [pow_add]
          _ = 815730721 := by rw [factor_3_2]; decide
      have factor_3_4 : (13 : ZMod 20097919679) ^ 17 = 7819910791 := by
        calc
          (13 : ZMod 20097919679) ^ 17 = (13 : ZMod 20097919679) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 8 * (13 : ZMod 20097919679) ^ 8) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 7819910791 := by rw [factor_3_3]; decide
      have factor_3_5 : (13 : ZMod 20097919679) ^ 35 = 2632787667 := by
        calc
          (13 : ZMod 20097919679) ^ 35 = (13 : ZMod 20097919679) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 17 * (13 : ZMod 20097919679) ^ 17) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 2632787667 := by rw [factor_3_4]; decide
      have factor_3_6 : (13 : ZMod 20097919679) ^ 71 = 17686698836 := by
        calc
          (13 : ZMod 20097919679) ^ 71 = (13 : ZMod 20097919679) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 35 * (13 : ZMod 20097919679) ^ 35) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 17686698836 := by rw [factor_3_5]; decide
      have factor_3_7 : (13 : ZMod 20097919679) ^ 142 = 17959224661 := by
        calc
          (13 : ZMod 20097919679) ^ 142 = (13 : ZMod 20097919679) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 71 * (13 : ZMod 20097919679) ^ 71 := by rw [pow_add]
          _ = 17959224661 := by rw [factor_3_6]; decide
      have factor_3_8 : (13 : ZMod 20097919679) ^ 284 = 17313945442 := by
        calc
          (13 : ZMod 20097919679) ^ 284 = (13 : ZMod 20097919679) ^ (142 + 142) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 142 * (13 : ZMod 20097919679) ^ 142 := by rw [pow_add]
          _ = 17313945442 := by rw [factor_3_7]; decide
      have factor_3_9 : (13 : ZMod 20097919679) ^ 569 = 10316423977 := by
        calc
          (13 : ZMod 20097919679) ^ 569 = (13 : ZMod 20097919679) ^ (284 + 284 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 284 * (13 : ZMod 20097919679) ^ 284) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 10316423977 := by rw [factor_3_8]; decide
      have factor_3_10 : (13 : ZMod 20097919679) ^ 1139 = 15597371683 := by
        calc
          (13 : ZMod 20097919679) ^ 1139 = (13 : ZMod 20097919679) ^ (569 + 569 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 569 * (13 : ZMod 20097919679) ^ 569) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 15597371683 := by rw [factor_3_9]; decide
      have factor_3_11 : (13 : ZMod 20097919679) ^ 2279 = 14349189627 := by
        calc
          (13 : ZMod 20097919679) ^ 2279 = (13 : ZMod 20097919679) ^ (1139 + 1139 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 1139 * (13 : ZMod 20097919679) ^ 1139) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 14349189627 := by rw [factor_3_10]; decide
      have factor_3_12 : (13 : ZMod 20097919679) ^ 4558 = 16790563521 := by
        calc
          (13 : ZMod 20097919679) ^ 4558 = (13 : ZMod 20097919679) ^ (2279 + 2279) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 2279 * (13 : ZMod 20097919679) ^ 2279 := by rw [pow_add]
          _ = 16790563521 := by rw [factor_3_11]; decide
      have factor_3_13 : (13 : ZMod 20097919679) ^ 9116 = 10655513526 := by
        calc
          (13 : ZMod 20097919679) ^ 9116 = (13 : ZMod 20097919679) ^ (4558 + 4558) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 4558 * (13 : ZMod 20097919679) ^ 4558 := by rw [pow_add]
          _ = 10655513526 := by rw [factor_3_12]; decide
      have factor_3_14 : (13 : ZMod 20097919679) ^ 18232 = 7054884026 := by
        calc
          (13 : ZMod 20097919679) ^ 18232 = (13 : ZMod 20097919679) ^ (9116 + 9116) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 9116 * (13 : ZMod 20097919679) ^ 9116 := by rw [pow_add]
          _ = 7054884026 := by rw [factor_3_13]; decide
      have factor_3_15 : (13 : ZMod 20097919679) ^ 36464 = 726508513 := by
        calc
          (13 : ZMod 20097919679) ^ 36464 = (13 : ZMod 20097919679) ^ (18232 + 18232) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 18232 * (13 : ZMod 20097919679) ^ 18232 := by rw [pow_add]
          _ = 726508513 := by rw [factor_3_14]; decide
      have factor_3_16 : (13 : ZMod 20097919679) ^ 72929 = 13777004851 := by
        calc
          (13 : ZMod 20097919679) ^ 72929 = (13 : ZMod 20097919679) ^ (36464 + 36464 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = ((13 : ZMod 20097919679) ^ 36464 * (13 : ZMod 20097919679) ^ 36464) * (13 : ZMod 20097919679) := by rw [pow_succ, pow_add]
          _ = 13777004851 := by rw [factor_3_15]; decide
      have factor_3_17 : (13 : ZMod 20097919679) ^ 145858 = 11814448191 := by
        calc
          (13 : ZMod 20097919679) ^ 145858 = (13 : ZMod 20097919679) ^ (72929 + 72929) :=
            congrArg (fun n : ℕ => (13 : ZMod 20097919679) ^ n) (by norm_num)
          _ = (13 : ZMod 20097919679) ^ 72929 * (13 : ZMod 20097919679) ^ 72929 := by rw [pow_add]
          _ = 11814448191 := by rw [factor_3_16]; decide
      change (13 : ZMod 20097919679) ^ 145858 ≠ 1
      rw [factor_3_17]
      decide

#print axioms prime_lucas_20097919679

end TotientTailPeriodKiller
end Erdos249257
