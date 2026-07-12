import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2009428397 : Nat.Prime 2009428397 := by
  apply lucas_primality 2009428397 (2 : ZMod 2009428397)
  ·
      have fermat_0 : (2 : ZMod 2009428397) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 2009428397) ^ 3 = 8 := by
        calc
          (2 : ZMod 2009428397) ^ 3 = (2 : ZMod 2009428397) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 1 * (2 : ZMod 2009428397) ^ 1) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 2009428397) ^ 7 = 128 := by
        calc
          (2 : ZMod 2009428397) ^ 7 = (2 : ZMod 2009428397) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 3 * (2 : ZMod 2009428397) ^ 3) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 2009428397) ^ 14 = 16384 := by
        calc
          (2 : ZMod 2009428397) ^ 14 = (2 : ZMod 2009428397) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 7 * (2 : ZMod 2009428397) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 2009428397) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 2009428397) ^ 29 = (2 : ZMod 2009428397) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 14 * (2 : ZMod 2009428397) ^ 14) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 2009428397) ^ 59 = 855139016 := by
        calc
          (2 : ZMod 2009428397) ^ 59 = (2 : ZMod 2009428397) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 29 * (2 : ZMod 2009428397) ^ 29) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 855139016 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 2009428397) ^ 119 = 153521694 := by
        calc
          (2 : ZMod 2009428397) ^ 119 = (2 : ZMod 2009428397) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 59 * (2 : ZMod 2009428397) ^ 59) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 153521694 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 2009428397) ^ 239 = 675061041 := by
        calc
          (2 : ZMod 2009428397) ^ 239 = (2 : ZMod 2009428397) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 119 * (2 : ZMod 2009428397) ^ 119) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 675061041 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 2009428397) ^ 479 = 1733433741 := by
        calc
          (2 : ZMod 2009428397) ^ 479 = (2 : ZMod 2009428397) ^ (239 + 239 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 239 * (2 : ZMod 2009428397) ^ 239) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1733433741 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 2009428397) ^ 958 = 164193796 := by
        calc
          (2 : ZMod 2009428397) ^ 958 = (2 : ZMod 2009428397) ^ (479 + 479) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 479 * (2 : ZMod 2009428397) ^ 479 := by rw [pow_add]
          _ = 164193796 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 2009428397) ^ 1916 = 56834075 := by
        calc
          (2 : ZMod 2009428397) ^ 1916 = (2 : ZMod 2009428397) ^ (958 + 958) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 958 * (2 : ZMod 2009428397) ^ 958 := by rw [pow_add]
          _ = 56834075 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 2009428397) ^ 3832 = 140352859 := by
        calc
          (2 : ZMod 2009428397) ^ 3832 = (2 : ZMod 2009428397) ^ (1916 + 1916) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1916 * (2 : ZMod 2009428397) ^ 1916 := by rw [pow_add]
          _ = 140352859 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 2009428397) ^ 7665 = 230880850 := by
        calc
          (2 : ZMod 2009428397) ^ 7665 = (2 : ZMod 2009428397) ^ (3832 + 3832 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 3832 * (2 : ZMod 2009428397) ^ 3832) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 230880850 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 2009428397) ^ 15330 = 1088236275 := by
        calc
          (2 : ZMod 2009428397) ^ 15330 = (2 : ZMod 2009428397) ^ (7665 + 7665) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 7665 * (2 : ZMod 2009428397) ^ 7665 := by rw [pow_add]
          _ = 1088236275 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 2009428397) ^ 30661 = 227837121 := by
        calc
          (2 : ZMod 2009428397) ^ 30661 = (2 : ZMod 2009428397) ^ (15330 + 15330 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 15330 * (2 : ZMod 2009428397) ^ 15330) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 227837121 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 2009428397) ^ 61322 = 1039598323 := by
        calc
          (2 : ZMod 2009428397) ^ 61322 = (2 : ZMod 2009428397) ^ (30661 + 30661) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 30661 * (2 : ZMod 2009428397) ^ 30661 := by rw [pow_add]
          _ = 1039598323 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 2009428397) ^ 122645 = 1689957975 := by
        calc
          (2 : ZMod 2009428397) ^ 122645 = (2 : ZMod 2009428397) ^ (61322 + 61322 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 61322 * (2 : ZMod 2009428397) ^ 61322) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1689957975 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 2009428397) ^ 245291 = 1210315578 := by
        calc
          (2 : ZMod 2009428397) ^ 245291 = (2 : ZMod 2009428397) ^ (122645 + 122645 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 122645 * (2 : ZMod 2009428397) ^ 122645) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1210315578 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 2009428397) ^ 490583 = 1056155391 := by
        calc
          (2 : ZMod 2009428397) ^ 490583 = (2 : ZMod 2009428397) ^ (245291 + 245291 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 245291 * (2 : ZMod 2009428397) ^ 245291) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1056155391 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 2009428397) ^ 981166 = 1631168024 := by
        calc
          (2 : ZMod 2009428397) ^ 981166 = (2 : ZMod 2009428397) ^ (490583 + 490583) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 490583 * (2 : ZMod 2009428397) ^ 490583 := by rw [pow_add]
          _ = 1631168024 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 2009428397) ^ 1962332 = 838533072 := by
        calc
          (2 : ZMod 2009428397) ^ 1962332 = (2 : ZMod 2009428397) ^ (981166 + 981166) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 981166 * (2 : ZMod 2009428397) ^ 981166 := by rw [pow_add]
          _ = 838533072 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 2009428397) ^ 3924664 = 1070532185 := by
        calc
          (2 : ZMod 2009428397) ^ 3924664 = (2 : ZMod 2009428397) ^ (1962332 + 1962332) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1962332 * (2 : ZMod 2009428397) ^ 1962332 := by rw [pow_add]
          _ = 1070532185 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 2009428397) ^ 7849329 = 1458337206 := by
        calc
          (2 : ZMod 2009428397) ^ 7849329 = (2 : ZMod 2009428397) ^ (3924664 + 3924664 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 3924664 * (2 : ZMod 2009428397) ^ 3924664) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1458337206 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 2009428397) ^ 15698659 = 664970889 := by
        calc
          (2 : ZMod 2009428397) ^ 15698659 = (2 : ZMod 2009428397) ^ (7849329 + 7849329 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 7849329 * (2 : ZMod 2009428397) ^ 7849329) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 664970889 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 2009428397) ^ 31397318 = 197175586 := by
        calc
          (2 : ZMod 2009428397) ^ 31397318 = (2 : ZMod 2009428397) ^ (15698659 + 15698659) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 15698659 * (2 : ZMod 2009428397) ^ 15698659 := by rw [pow_add]
          _ = 197175586 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 2009428397) ^ 62794637 = 139681368 := by
        calc
          (2 : ZMod 2009428397) ^ 62794637 = (2 : ZMod 2009428397) ^ (31397318 + 31397318 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 31397318 * (2 : ZMod 2009428397) ^ 31397318) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 139681368 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 2009428397) ^ 125589274 = 1961709228 := by
        calc
          (2 : ZMod 2009428397) ^ 125589274 = (2 : ZMod 2009428397) ^ (62794637 + 62794637) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 62794637 * (2 : ZMod 2009428397) ^ 62794637 := by rw [pow_add]
          _ = 1961709228 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 2009428397) ^ 251178549 = 1340574824 := by
        calc
          (2 : ZMod 2009428397) ^ 251178549 = (2 : ZMod 2009428397) ^ (125589274 + 125589274 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 125589274 * (2 : ZMod 2009428397) ^ 125589274) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1340574824 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 2009428397) ^ 502357099 = 1337707145 := by
        calc
          (2 : ZMod 2009428397) ^ 502357099 = (2 : ZMod 2009428397) ^ (251178549 + 251178549 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 251178549 * (2 : ZMod 2009428397) ^ 251178549) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1337707145 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 2009428397) ^ 1004714198 = 2009428396 := by
        calc
          (2 : ZMod 2009428397) ^ 1004714198 = (2 : ZMod 2009428397) ^ (502357099 + 502357099) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 502357099 * (2 : ZMod 2009428397) ^ 502357099 := by rw [pow_add]
          _ = 2009428396 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 2009428397) ^ 2009428396 = 1 := by
        calc
          (2 : ZMod 2009428397) ^ 2009428396 = (2 : ZMod 2009428397) ^ (1004714198 + 1004714198) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1004714198 * (2 : ZMod 2009428397) ^ 1004714198 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (23, 1), (1571, 1), (13903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (23, 1), (1571, 1), (13903, 1)] : List FactorBlock).map factorBlockValue).prod = 2009428397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 2009428397) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 2009428397) ^ 3 = 8 := by
        calc
          (2 : ZMod 2009428397) ^ 3 = (2 : ZMod 2009428397) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 1 * (2 : ZMod 2009428397) ^ 1) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 2009428397) ^ 7 = 128 := by
        calc
          (2 : ZMod 2009428397) ^ 7 = (2 : ZMod 2009428397) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 3 * (2 : ZMod 2009428397) ^ 3) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 2009428397) ^ 14 = 16384 := by
        calc
          (2 : ZMod 2009428397) ^ 14 = (2 : ZMod 2009428397) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 7 * (2 : ZMod 2009428397) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 2009428397) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 2009428397) ^ 29 = (2 : ZMod 2009428397) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 14 * (2 : ZMod 2009428397) ^ 14) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 2009428397) ^ 59 = 855139016 := by
        calc
          (2 : ZMod 2009428397) ^ 59 = (2 : ZMod 2009428397) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 29 * (2 : ZMod 2009428397) ^ 29) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 855139016 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 2009428397) ^ 119 = 153521694 := by
        calc
          (2 : ZMod 2009428397) ^ 119 = (2 : ZMod 2009428397) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 59 * (2 : ZMod 2009428397) ^ 59) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 153521694 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 2009428397) ^ 239 = 675061041 := by
        calc
          (2 : ZMod 2009428397) ^ 239 = (2 : ZMod 2009428397) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 119 * (2 : ZMod 2009428397) ^ 119) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 675061041 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 2009428397) ^ 479 = 1733433741 := by
        calc
          (2 : ZMod 2009428397) ^ 479 = (2 : ZMod 2009428397) ^ (239 + 239 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 239 * (2 : ZMod 2009428397) ^ 239) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1733433741 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 2009428397) ^ 958 = 164193796 := by
        calc
          (2 : ZMod 2009428397) ^ 958 = (2 : ZMod 2009428397) ^ (479 + 479) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 479 * (2 : ZMod 2009428397) ^ 479 := by rw [pow_add]
          _ = 164193796 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 2009428397) ^ 1916 = 56834075 := by
        calc
          (2 : ZMod 2009428397) ^ 1916 = (2 : ZMod 2009428397) ^ (958 + 958) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 958 * (2 : ZMod 2009428397) ^ 958 := by rw [pow_add]
          _ = 56834075 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 2009428397) ^ 3832 = 140352859 := by
        calc
          (2 : ZMod 2009428397) ^ 3832 = (2 : ZMod 2009428397) ^ (1916 + 1916) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1916 * (2 : ZMod 2009428397) ^ 1916 := by rw [pow_add]
          _ = 140352859 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 2009428397) ^ 7665 = 230880850 := by
        calc
          (2 : ZMod 2009428397) ^ 7665 = (2 : ZMod 2009428397) ^ (3832 + 3832 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 3832 * (2 : ZMod 2009428397) ^ 3832) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 230880850 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 2009428397) ^ 15330 = 1088236275 := by
        calc
          (2 : ZMod 2009428397) ^ 15330 = (2 : ZMod 2009428397) ^ (7665 + 7665) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 7665 * (2 : ZMod 2009428397) ^ 7665 := by rw [pow_add]
          _ = 1088236275 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 2009428397) ^ 30661 = 227837121 := by
        calc
          (2 : ZMod 2009428397) ^ 30661 = (2 : ZMod 2009428397) ^ (15330 + 15330 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 15330 * (2 : ZMod 2009428397) ^ 15330) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 227837121 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 2009428397) ^ 61322 = 1039598323 := by
        calc
          (2 : ZMod 2009428397) ^ 61322 = (2 : ZMod 2009428397) ^ (30661 + 30661) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 30661 * (2 : ZMod 2009428397) ^ 30661 := by rw [pow_add]
          _ = 1039598323 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 2009428397) ^ 122645 = 1689957975 := by
        calc
          (2 : ZMod 2009428397) ^ 122645 = (2 : ZMod 2009428397) ^ (61322 + 61322 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 61322 * (2 : ZMod 2009428397) ^ 61322) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1689957975 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 2009428397) ^ 245291 = 1210315578 := by
        calc
          (2 : ZMod 2009428397) ^ 245291 = (2 : ZMod 2009428397) ^ (122645 + 122645 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 122645 * (2 : ZMod 2009428397) ^ 122645) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1210315578 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 2009428397) ^ 490583 = 1056155391 := by
        calc
          (2 : ZMod 2009428397) ^ 490583 = (2 : ZMod 2009428397) ^ (245291 + 245291 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 245291 * (2 : ZMod 2009428397) ^ 245291) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1056155391 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 2009428397) ^ 981166 = 1631168024 := by
        calc
          (2 : ZMod 2009428397) ^ 981166 = (2 : ZMod 2009428397) ^ (490583 + 490583) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 490583 * (2 : ZMod 2009428397) ^ 490583 := by rw [pow_add]
          _ = 1631168024 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 2009428397) ^ 1962332 = 838533072 := by
        calc
          (2 : ZMod 2009428397) ^ 1962332 = (2 : ZMod 2009428397) ^ (981166 + 981166) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 981166 * (2 : ZMod 2009428397) ^ 981166 := by rw [pow_add]
          _ = 838533072 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 2009428397) ^ 3924664 = 1070532185 := by
        calc
          (2 : ZMod 2009428397) ^ 3924664 = (2 : ZMod 2009428397) ^ (1962332 + 1962332) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1962332 * (2 : ZMod 2009428397) ^ 1962332 := by rw [pow_add]
          _ = 1070532185 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 2009428397) ^ 7849329 = 1458337206 := by
        calc
          (2 : ZMod 2009428397) ^ 7849329 = (2 : ZMod 2009428397) ^ (3924664 + 3924664 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 3924664 * (2 : ZMod 2009428397) ^ 3924664) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1458337206 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 2009428397) ^ 15698659 = 664970889 := by
        calc
          (2 : ZMod 2009428397) ^ 15698659 = (2 : ZMod 2009428397) ^ (7849329 + 7849329 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 7849329 * (2 : ZMod 2009428397) ^ 7849329) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 664970889 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 2009428397) ^ 31397318 = 197175586 := by
        calc
          (2 : ZMod 2009428397) ^ 31397318 = (2 : ZMod 2009428397) ^ (15698659 + 15698659) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 15698659 * (2 : ZMod 2009428397) ^ 15698659 := by rw [pow_add]
          _ = 197175586 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 2009428397) ^ 62794637 = 139681368 := by
        calc
          (2 : ZMod 2009428397) ^ 62794637 = (2 : ZMod 2009428397) ^ (31397318 + 31397318 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 31397318 * (2 : ZMod 2009428397) ^ 31397318) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 139681368 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 2009428397) ^ 125589274 = 1961709228 := by
        calc
          (2 : ZMod 2009428397) ^ 125589274 = (2 : ZMod 2009428397) ^ (62794637 + 62794637) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 62794637 * (2 : ZMod 2009428397) ^ 62794637 := by rw [pow_add]
          _ = 1961709228 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 2009428397) ^ 251178549 = 1340574824 := by
        calc
          (2 : ZMod 2009428397) ^ 251178549 = (2 : ZMod 2009428397) ^ (125589274 + 125589274 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 125589274 * (2 : ZMod 2009428397) ^ 125589274) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1340574824 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 2009428397) ^ 502357099 = 1337707145 := by
        calc
          (2 : ZMod 2009428397) ^ 502357099 = (2 : ZMod 2009428397) ^ (251178549 + 251178549 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 251178549 * (2 : ZMod 2009428397) ^ 251178549) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1337707145 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 2009428397) ^ 1004714198 = 2009428396 := by
        calc
          (2 : ZMod 2009428397) ^ 1004714198 = (2 : ZMod 2009428397) ^ (502357099 + 502357099) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 502357099 * (2 : ZMod 2009428397) ^ 502357099 := by rw [pow_add]
          _ = 2009428396 := by rw [factor_0_28]; decide
      change (2 : ZMod 2009428397) ^ 1004714198 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (2 : ZMod 2009428397) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 2009428397) ^ 2 = 4 := by
        calc
          (2 : ZMod 2009428397) ^ 2 = (2 : ZMod 2009428397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1 * (2 : ZMod 2009428397) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 2009428397) ^ 5 = 32 := by
        calc
          (2 : ZMod 2009428397) ^ 5 = (2 : ZMod 2009428397) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 2 * (2 : ZMod 2009428397) ^ 2) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 2009428397) ^ 10 = 1024 := by
        calc
          (2 : ZMod 2009428397) ^ 10 = (2 : ZMod 2009428397) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 5 * (2 : ZMod 2009428397) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 2009428397) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 2009428397) ^ 20 = (2 : ZMod 2009428397) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 10 * (2 : ZMod 2009428397) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 2009428397) ^ 41 = 708589234 := by
        calc
          (2 : ZMod 2009428397) ^ 41 = (2 : ZMod 2009428397) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 20 * (2 : ZMod 2009428397) ^ 20) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 708589234 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 2009428397) ^ 83 = 1423695957 := by
        calc
          (2 : ZMod 2009428397) ^ 83 = (2 : ZMod 2009428397) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 41 * (2 : ZMod 2009428397) ^ 41) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1423695957 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 2009428397) ^ 166 = 1083938680 := by
        calc
          (2 : ZMod 2009428397) ^ 166 = (2 : ZMod 2009428397) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 83 * (2 : ZMod 2009428397) ^ 83 := by rw [pow_add]
          _ = 1083938680 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 2009428397) ^ 333 = 95983490 := by
        calc
          (2 : ZMod 2009428397) ^ 333 = (2 : ZMod 2009428397) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 166 * (2 : ZMod 2009428397) ^ 166) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 95983490 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 2009428397) ^ 666 = 1028586103 := by
        calc
          (2 : ZMod 2009428397) ^ 666 = (2 : ZMod 2009428397) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 333 * (2 : ZMod 2009428397) ^ 333 := by rw [pow_add]
          _ = 1028586103 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 2009428397) ^ 1333 = 923420421 := by
        calc
          (2 : ZMod 2009428397) ^ 1333 = (2 : ZMod 2009428397) ^ (666 + 666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 666 * (2 : ZMod 2009428397) ^ 666) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 923420421 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 2009428397) ^ 2666 = 1325243309 := by
        calc
          (2 : ZMod 2009428397) ^ 2666 = (2 : ZMod 2009428397) ^ (1333 + 1333) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1333 * (2 : ZMod 2009428397) ^ 1333 := by rw [pow_add]
          _ = 1325243309 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 2009428397) ^ 5332 = 1086679386 := by
        calc
          (2 : ZMod 2009428397) ^ 5332 = (2 : ZMod 2009428397) ^ (2666 + 2666) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 2666 * (2 : ZMod 2009428397) ^ 2666 := by rw [pow_add]
          _ = 1086679386 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 2009428397) ^ 10664 = 707877609 := by
        calc
          (2 : ZMod 2009428397) ^ 10664 = (2 : ZMod 2009428397) ^ (5332 + 5332) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 5332 * (2 : ZMod 2009428397) ^ 5332 := by rw [pow_add]
          _ = 707877609 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 2009428397) ^ 21329 = 151255618 := by
        calc
          (2 : ZMod 2009428397) ^ 21329 = (2 : ZMod 2009428397) ^ (10664 + 10664 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 10664 * (2 : ZMod 2009428397) ^ 10664) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 151255618 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 2009428397) ^ 42659 = 726450593 := by
        calc
          (2 : ZMod 2009428397) ^ 42659 = (2 : ZMod 2009428397) ^ (21329 + 21329 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 21329 * (2 : ZMod 2009428397) ^ 21329) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 726450593 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 2009428397) ^ 85318 = 989731114 := by
        calc
          (2 : ZMod 2009428397) ^ 85318 = (2 : ZMod 2009428397) ^ (42659 + 42659) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 42659 * (2 : ZMod 2009428397) ^ 42659 := by rw [pow_add]
          _ = 989731114 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 2009428397) ^ 170637 = 1975385196 := by
        calc
          (2 : ZMod 2009428397) ^ 170637 = (2 : ZMod 2009428397) ^ (85318 + 85318 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 85318 * (2 : ZMod 2009428397) ^ 85318) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1975385196 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 2009428397) ^ 341275 = 1403284905 := by
        calc
          (2 : ZMod 2009428397) ^ 341275 = (2 : ZMod 2009428397) ^ (170637 + 170637 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 170637 * (2 : ZMod 2009428397) ^ 170637) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1403284905 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 2009428397) ^ 682550 = 425855888 := by
        calc
          (2 : ZMod 2009428397) ^ 682550 = (2 : ZMod 2009428397) ^ (341275 + 341275) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 341275 * (2 : ZMod 2009428397) ^ 341275 := by rw [pow_add]
          _ = 425855888 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 2009428397) ^ 1365100 = 1615791612 := by
        calc
          (2 : ZMod 2009428397) ^ 1365100 = (2 : ZMod 2009428397) ^ (682550 + 682550) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 682550 * (2 : ZMod 2009428397) ^ 682550 := by rw [pow_add]
          _ = 1615791612 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 2009428397) ^ 2730201 = 461720693 := by
        calc
          (2 : ZMod 2009428397) ^ 2730201 = (2 : ZMod 2009428397) ^ (1365100 + 1365100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 1365100 * (2 : ZMod 2009428397) ^ 1365100) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 461720693 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 2009428397) ^ 5460403 = 1558336834 := by
        calc
          (2 : ZMod 2009428397) ^ 5460403 = (2 : ZMod 2009428397) ^ (2730201 + 2730201 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 2730201 * (2 : ZMod 2009428397) ^ 2730201) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1558336834 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 2009428397) ^ 10920806 = 1074905023 := by
        calc
          (2 : ZMod 2009428397) ^ 10920806 = (2 : ZMod 2009428397) ^ (5460403 + 5460403) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 5460403 * (2 : ZMod 2009428397) ^ 5460403 := by rw [pow_add]
          _ = 1074905023 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 2009428397) ^ 21841613 = 1275170704 := by
        calc
          (2 : ZMod 2009428397) ^ 21841613 = (2 : ZMod 2009428397) ^ (10920806 + 10920806 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 10920806 * (2 : ZMod 2009428397) ^ 10920806) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1275170704 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 2009428397) ^ 43683226 = 667277696 := by
        calc
          (2 : ZMod 2009428397) ^ 43683226 = (2 : ZMod 2009428397) ^ (21841613 + 21841613) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 21841613 * (2 : ZMod 2009428397) ^ 21841613 := by rw [pow_add]
          _ = 667277696 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 2009428397) ^ 87366452 = 674137911 := by
        calc
          (2 : ZMod 2009428397) ^ 87366452 = (2 : ZMod 2009428397) ^ (43683226 + 43683226) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 43683226 * (2 : ZMod 2009428397) ^ 43683226 := by rw [pow_add]
          _ = 674137911 := by rw [factor_1_25]; decide
      change (2 : ZMod 2009428397) ^ 87366452 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (2 : ZMod 2009428397) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 2009428397) ^ 2 = 4 := by
        calc
          (2 : ZMod 2009428397) ^ 2 = (2 : ZMod 2009428397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1 * (2 : ZMod 2009428397) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 2009428397) ^ 4 = 16 := by
        calc
          (2 : ZMod 2009428397) ^ 4 = (2 : ZMod 2009428397) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 2 * (2 : ZMod 2009428397) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 2009428397) ^ 9 = 512 := by
        calc
          (2 : ZMod 2009428397) ^ 9 = (2 : ZMod 2009428397) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 4 * (2 : ZMod 2009428397) ^ 4) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 2009428397) ^ 19 = 524288 := by
        calc
          (2 : ZMod 2009428397) ^ 19 = (2 : ZMod 2009428397) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 9 * (2 : ZMod 2009428397) ^ 9) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 2009428397) ^ 39 = 1181861507 := by
        calc
          (2 : ZMod 2009428397) ^ 39 = (2 : ZMod 2009428397) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 19 * (2 : ZMod 2009428397) ^ 19) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1181861507 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 2009428397) ^ 78 = 1488767159 := by
        calc
          (2 : ZMod 2009428397) ^ 78 = (2 : ZMod 2009428397) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 39 * (2 : ZMod 2009428397) ^ 39 := by rw [pow_add]
          _ = 1488767159 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 2009428397) ^ 156 = 1837801678 := by
        calc
          (2 : ZMod 2009428397) ^ 156 = (2 : ZMod 2009428397) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 78 * (2 : ZMod 2009428397) ^ 78 := by rw [pow_add]
          _ = 1837801678 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 2009428397) ^ 312 = 56468844 := by
        calc
          (2 : ZMod 2009428397) ^ 312 = (2 : ZMod 2009428397) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 156 * (2 : ZMod 2009428397) ^ 156 := by rw [pow_add]
          _ = 56468844 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 2009428397) ^ 624 = 570351388 := by
        calc
          (2 : ZMod 2009428397) ^ 624 = (2 : ZMod 2009428397) ^ (312 + 312) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 312 * (2 : ZMod 2009428397) ^ 312 := by rw [pow_add]
          _ = 570351388 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 2009428397) ^ 1249 = 297696595 := by
        calc
          (2 : ZMod 2009428397) ^ 1249 = (2 : ZMod 2009428397) ^ (624 + 624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 624 * (2 : ZMod 2009428397) ^ 624) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 297696595 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 2009428397) ^ 2498 = 1321542376 := by
        calc
          (2 : ZMod 2009428397) ^ 2498 = (2 : ZMod 2009428397) ^ (1249 + 1249) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1249 * (2 : ZMod 2009428397) ^ 1249 := by rw [pow_add]
          _ = 1321542376 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 2009428397) ^ 4996 = 216829660 := by
        calc
          (2 : ZMod 2009428397) ^ 4996 = (2 : ZMod 2009428397) ^ (2498 + 2498) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 2498 * (2 : ZMod 2009428397) ^ 2498 := by rw [pow_add]
          _ = 216829660 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 2009428397) ^ 9992 = 884578953 := by
        calc
          (2 : ZMod 2009428397) ^ 9992 = (2 : ZMod 2009428397) ^ (4996 + 4996) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 4996 * (2 : ZMod 2009428397) ^ 4996 := by rw [pow_add]
          _ = 884578953 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 2009428397) ^ 19985 = 776743416 := by
        calc
          (2 : ZMod 2009428397) ^ 19985 = (2 : ZMod 2009428397) ^ (9992 + 9992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 9992 * (2 : ZMod 2009428397) ^ 9992) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 776743416 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 2009428397) ^ 39971 = 1291532492 := by
        calc
          (2 : ZMod 2009428397) ^ 39971 = (2 : ZMod 2009428397) ^ (19985 + 19985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 19985 * (2 : ZMod 2009428397) ^ 19985) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1291532492 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 2009428397) ^ 79942 = 350605153 := by
        calc
          (2 : ZMod 2009428397) ^ 79942 = (2 : ZMod 2009428397) ^ (39971 + 39971) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 39971 * (2 : ZMod 2009428397) ^ 39971 := by rw [pow_add]
          _ = 350605153 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 2009428397) ^ 159884 = 304577415 := by
        calc
          (2 : ZMod 2009428397) ^ 159884 = (2 : ZMod 2009428397) ^ (79942 + 79942) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 79942 * (2 : ZMod 2009428397) ^ 79942 := by rw [pow_add]
          _ = 304577415 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 2009428397) ^ 319769 = 1488097237 := by
        calc
          (2 : ZMod 2009428397) ^ 319769 = (2 : ZMod 2009428397) ^ (159884 + 159884 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 159884 * (2 : ZMod 2009428397) ^ 159884) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1488097237 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 2009428397) ^ 639538 = 138220804 := by
        calc
          (2 : ZMod 2009428397) ^ 639538 = (2 : ZMod 2009428397) ^ (319769 + 319769) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 319769 * (2 : ZMod 2009428397) ^ 319769 := by rw [pow_add]
          _ = 138220804 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 2009428397) ^ 1279076 = 533387838 := by
        calc
          (2 : ZMod 2009428397) ^ 1279076 = (2 : ZMod 2009428397) ^ (639538 + 639538) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 639538 * (2 : ZMod 2009428397) ^ 639538 := by rw [pow_add]
          _ = 533387838 := by rw [factor_2_19]; decide
      change (2 : ZMod 2009428397) ^ 1279076 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (2 : ZMod 2009428397) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 2009428397) ^ 2 = 4 := by
        calc
          (2 : ZMod 2009428397) ^ 2 = (2 : ZMod 2009428397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1 * (2 : ZMod 2009428397) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 2009428397) ^ 4 = 16 := by
        calc
          (2 : ZMod 2009428397) ^ 4 = (2 : ZMod 2009428397) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 2 * (2 : ZMod 2009428397) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 2009428397) ^ 8 = 256 := by
        calc
          (2 : ZMod 2009428397) ^ 8 = (2 : ZMod 2009428397) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 4 * (2 : ZMod 2009428397) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 2009428397) ^ 17 = 131072 := by
        calc
          (2 : ZMod 2009428397) ^ 17 = (2 : ZMod 2009428397) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 8 * (2 : ZMod 2009428397) ^ 8) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 2009428397) ^ 35 = 199455619 := by
        calc
          (2 : ZMod 2009428397) ^ 35 = (2 : ZMod 2009428397) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 17 * (2 : ZMod 2009428397) ^ 17) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 199455619 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 2009428397) ^ 70 = 1112570981 := by
        calc
          (2 : ZMod 2009428397) ^ 70 = (2 : ZMod 2009428397) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 35 * (2 : ZMod 2009428397) ^ 35 := by rw [pow_add]
          _ = 1112570981 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 2009428397) ^ 141 = 1353697517 := by
        calc
          (2 : ZMod 2009428397) ^ 141 = (2 : ZMod 2009428397) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 70 * (2 : ZMod 2009428397) ^ 70) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1353697517 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 2009428397) ^ 282 = 799420208 := by
        calc
          (2 : ZMod 2009428397) ^ 282 = (2 : ZMod 2009428397) ^ (141 + 141) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 141 * (2 : ZMod 2009428397) ^ 141 := by rw [pow_add]
          _ = 799420208 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 2009428397) ^ 564 = 1447224796 := by
        calc
          (2 : ZMod 2009428397) ^ 564 = (2 : ZMod 2009428397) ^ (282 + 282) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 282 * (2 : ZMod 2009428397) ^ 282 := by rw [pow_add]
          _ = 1447224796 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 2009428397) ^ 1129 = 1966192349 := by
        calc
          (2 : ZMod 2009428397) ^ 1129 = (2 : ZMod 2009428397) ^ (564 + 564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 564 * (2 : ZMod 2009428397) ^ 564) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1966192349 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 2009428397) ^ 2258 = 684356380 := by
        calc
          (2 : ZMod 2009428397) ^ 2258 = (2 : ZMod 2009428397) ^ (1129 + 1129) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 1129 * (2 : ZMod 2009428397) ^ 1129 := by rw [pow_add]
          _ = 684356380 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 2009428397) ^ 4516 = 1375022022 := by
        calc
          (2 : ZMod 2009428397) ^ 4516 = (2 : ZMod 2009428397) ^ (2258 + 2258) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 2258 * (2 : ZMod 2009428397) ^ 2258 := by rw [pow_add]
          _ = 1375022022 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 2009428397) ^ 9033 = 1537262310 := by
        calc
          (2 : ZMod 2009428397) ^ 9033 = (2 : ZMod 2009428397) ^ (4516 + 4516 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 4516 * (2 : ZMod 2009428397) ^ 4516) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1537262310 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 2009428397) ^ 18066 = 1786998503 := by
        calc
          (2 : ZMod 2009428397) ^ 18066 = (2 : ZMod 2009428397) ^ (9033 + 9033) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 9033 * (2 : ZMod 2009428397) ^ 9033 := by rw [pow_add]
          _ = 1786998503 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 2009428397) ^ 36133 = 1728216820 := by
        calc
          (2 : ZMod 2009428397) ^ 36133 = (2 : ZMod 2009428397) ^ (18066 + 18066 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = ((2 : ZMod 2009428397) ^ 18066 * (2 : ZMod 2009428397) ^ 18066) * (2 : ZMod 2009428397) := by rw [pow_succ, pow_add]
          _ = 1728216820 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 2009428397) ^ 72266 = 1660510279 := by
        calc
          (2 : ZMod 2009428397) ^ 72266 = (2 : ZMod 2009428397) ^ (36133 + 36133) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 36133 * (2 : ZMod 2009428397) ^ 36133 := by rw [pow_add]
          _ = 1660510279 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 2009428397) ^ 144532 = 1285216854 := by
        calc
          (2 : ZMod 2009428397) ^ 144532 = (2 : ZMod 2009428397) ^ (72266 + 72266) :=
            congrArg (fun n : ℕ => (2 : ZMod 2009428397) ^ n) (by norm_num)
          _ = (2 : ZMod 2009428397) ^ 72266 * (2 : ZMod 2009428397) ^ 72266 := by rw [pow_add]
          _ = 1285216854 := by rw [factor_3_16]; decide
      change (2 : ZMod 2009428397) ^ 144532 ≠ 1
      rw [factor_3_17]
      decide

#print axioms prime_lucas_2009428397

end TotientTailPeriodKiller
end Erdos249257
