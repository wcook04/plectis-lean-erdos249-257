import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_716333897 : Nat.Prime 716333897 := by
  apply lucas_primality 716333897 (3 : ZMod 716333897)
  ·
      have fermat_0 : (3 : ZMod 716333897) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 716333897) ^ 2 = 9 := by
        calc
          (3 : ZMod 716333897) ^ 2 = (3 : ZMod 716333897) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 1 * (3 : ZMod 716333897) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 716333897) ^ 5 = 243 := by
        calc
          (3 : ZMod 716333897) ^ 5 = (3 : ZMod 716333897) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 2 * (3 : ZMod 716333897) ^ 2) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 716333897) ^ 10 = 59049 := by
        calc
          (3 : ZMod 716333897) ^ 10 = (3 : ZMod 716333897) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 5 * (3 : ZMod 716333897) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 716333897) ^ 21 = 431678645 := by
        calc
          (3 : ZMod 716333897) ^ 21 = (3 : ZMod 716333897) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 10 * (3 : ZMod 716333897) ^ 10) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 431678645 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 716333897) ^ 42 = 149298913 := by
        calc
          (3 : ZMod 716333897) ^ 42 = (3 : ZMod 716333897) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 21 * (3 : ZMod 716333897) ^ 21 := by rw [pow_add]
          _ = 149298913 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 716333897) ^ 85 = 621423149 := by
        calc
          (3 : ZMod 716333897) ^ 85 = (3 : ZMod 716333897) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 42 * (3 : ZMod 716333897) ^ 42) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 621423149 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 716333897) ^ 170 = 184692237 := by
        calc
          (3 : ZMod 716333897) ^ 170 = (3 : ZMod 716333897) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 85 * (3 : ZMod 716333897) ^ 85 := by rw [pow_add]
          _ = 184692237 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 716333897) ^ 341 = 398850595 := by
        calc
          (3 : ZMod 716333897) ^ 341 = (3 : ZMod 716333897) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 170 * (3 : ZMod 716333897) ^ 170) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 398850595 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 716333897) ^ 683 = 596474834 := by
        calc
          (3 : ZMod 716333897) ^ 683 = (3 : ZMod 716333897) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 341 * (3 : ZMod 716333897) ^ 341) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 596474834 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 716333897) ^ 1366 = 483809964 := by
        calc
          (3 : ZMod 716333897) ^ 1366 = (3 : ZMod 716333897) ^ (683 + 683) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 683 * (3 : ZMod 716333897) ^ 683 := by rw [pow_add]
          _ = 483809964 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 716333897) ^ 2732 = 457078292 := by
        calc
          (3 : ZMod 716333897) ^ 2732 = (3 : ZMod 716333897) ^ (1366 + 1366) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 1366 * (3 : ZMod 716333897) ^ 1366 := by rw [pow_add]
          _ = 457078292 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 716333897) ^ 5465 = 142217305 := by
        calc
          (3 : ZMod 716333897) ^ 5465 = (3 : ZMod 716333897) ^ (2732 + 2732 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 2732 * (3 : ZMod 716333897) ^ 2732) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 142217305 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 716333897) ^ 10930 = 477276634 := by
        calc
          (3 : ZMod 716333897) ^ 10930 = (3 : ZMod 716333897) ^ (5465 + 5465) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 5465 * (3 : ZMod 716333897) ^ 5465 := by rw [pow_add]
          _ = 477276634 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 716333897) ^ 21860 = 244976255 := by
        calc
          (3 : ZMod 716333897) ^ 21860 = (3 : ZMod 716333897) ^ (10930 + 10930) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 10930 * (3 : ZMod 716333897) ^ 10930 := by rw [pow_add]
          _ = 244976255 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 716333897) ^ 43721 = 635731498 := by
        calc
          (3 : ZMod 716333897) ^ 43721 = (3 : ZMod 716333897) ^ (21860 + 21860 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 21860 * (3 : ZMod 716333897) ^ 21860) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 635731498 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 716333897) ^ 87443 = 426244254 := by
        calc
          (3 : ZMod 716333897) ^ 87443 = (3 : ZMod 716333897) ^ (43721 + 43721 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 43721 * (3 : ZMod 716333897) ^ 43721) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 426244254 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 716333897) ^ 174886 = 206593681 := by
        calc
          (3 : ZMod 716333897) ^ 174886 = (3 : ZMod 716333897) ^ (87443 + 87443) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 87443 * (3 : ZMod 716333897) ^ 87443 := by rw [pow_add]
          _ = 206593681 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 716333897) ^ 349772 = 370472995 := by
        calc
          (3 : ZMod 716333897) ^ 349772 = (3 : ZMod 716333897) ^ (174886 + 174886) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 174886 * (3 : ZMod 716333897) ^ 174886 := by rw [pow_add]
          _ = 370472995 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 716333897) ^ 699544 = 601213609 := by
        calc
          (3 : ZMod 716333897) ^ 699544 = (3 : ZMod 716333897) ^ (349772 + 349772) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 349772 * (3 : ZMod 716333897) ^ 349772 := by rw [pow_add]
          _ = 601213609 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 716333897) ^ 1399089 = 95920059 := by
        calc
          (3 : ZMod 716333897) ^ 1399089 = (3 : ZMod 716333897) ^ (699544 + 699544 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 699544 * (3 : ZMod 716333897) ^ 699544) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 95920059 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 716333897) ^ 2798179 = 593666459 := by
        calc
          (3 : ZMod 716333897) ^ 2798179 = (3 : ZMod 716333897) ^ (1399089 + 1399089 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 1399089 * (3 : ZMod 716333897) ^ 1399089) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 593666459 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 716333897) ^ 5596358 = 533776402 := by
        calc
          (3 : ZMod 716333897) ^ 5596358 = (3 : ZMod 716333897) ^ (2798179 + 2798179) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 2798179 * (3 : ZMod 716333897) ^ 2798179 := by rw [pow_add]
          _ = 533776402 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 716333897) ^ 11192717 = 662045615 := by
        calc
          (3 : ZMod 716333897) ^ 11192717 = (3 : ZMod 716333897) ^ (5596358 + 5596358 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 5596358 * (3 : ZMod 716333897) ^ 5596358) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 662045615 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 716333897) ^ 22385434 = 712081042 := by
        calc
          (3 : ZMod 716333897) ^ 22385434 = (3 : ZMod 716333897) ^ (11192717 + 11192717) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 11192717 * (3 : ZMod 716333897) ^ 11192717 := by rw [pow_add]
          _ = 712081042 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 716333897) ^ 44770868 = 61085672 := by
        calc
          (3 : ZMod 716333897) ^ 44770868 = (3 : ZMod 716333897) ^ (22385434 + 22385434) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 22385434 * (3 : ZMod 716333897) ^ 22385434 := by rw [pow_add]
          _ = 61085672 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 716333897) ^ 89541737 = 368476506 := by
        calc
          (3 : ZMod 716333897) ^ 89541737 = (3 : ZMod 716333897) ^ (44770868 + 44770868 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 44770868 * (3 : ZMod 716333897) ^ 44770868) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 368476506 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 716333897) ^ 179083474 = 38461060 := by
        calc
          (3 : ZMod 716333897) ^ 179083474 = (3 : ZMod 716333897) ^ (89541737 + 89541737) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 89541737 * (3 : ZMod 716333897) ^ 89541737 := by rw [pow_add]
          _ = 38461060 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 716333897) ^ 358166948 = 716333896 := by
        calc
          (3 : ZMod 716333897) ^ 358166948 = (3 : ZMod 716333897) ^ (179083474 + 179083474) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 179083474 * (3 : ZMod 716333897) ^ 179083474 := by rw [pow_add]
          _ = 716333896 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 716333897) ^ 716333896 = 1 := by
        calc
          (3 : ZMod 716333897) ^ 716333896 = (3 : ZMod 716333897) ^ (358166948 + 358166948) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 358166948 * (3 : ZMod 716333897) ^ 358166948 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 2), (19, 1), (23, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 2), (19, 1), (23, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod = 716333897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 716333897) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 716333897) ^ 2 = 9 := by
        calc
          (3 : ZMod 716333897) ^ 2 = (3 : ZMod 716333897) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 1 * (3 : ZMod 716333897) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 716333897) ^ 5 = 243 := by
        calc
          (3 : ZMod 716333897) ^ 5 = (3 : ZMod 716333897) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 2 * (3 : ZMod 716333897) ^ 2) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 716333897) ^ 10 = 59049 := by
        calc
          (3 : ZMod 716333897) ^ 10 = (3 : ZMod 716333897) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 5 * (3 : ZMod 716333897) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 716333897) ^ 21 = 431678645 := by
        calc
          (3 : ZMod 716333897) ^ 21 = (3 : ZMod 716333897) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 10 * (3 : ZMod 716333897) ^ 10) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 431678645 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 716333897) ^ 42 = 149298913 := by
        calc
          (3 : ZMod 716333897) ^ 42 = (3 : ZMod 716333897) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 21 * (3 : ZMod 716333897) ^ 21 := by rw [pow_add]
          _ = 149298913 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 716333897) ^ 85 = 621423149 := by
        calc
          (3 : ZMod 716333897) ^ 85 = (3 : ZMod 716333897) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 42 * (3 : ZMod 716333897) ^ 42) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 621423149 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 716333897) ^ 170 = 184692237 := by
        calc
          (3 : ZMod 716333897) ^ 170 = (3 : ZMod 716333897) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 85 * (3 : ZMod 716333897) ^ 85 := by rw [pow_add]
          _ = 184692237 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 716333897) ^ 341 = 398850595 := by
        calc
          (3 : ZMod 716333897) ^ 341 = (3 : ZMod 716333897) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 170 * (3 : ZMod 716333897) ^ 170) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 398850595 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 716333897) ^ 683 = 596474834 := by
        calc
          (3 : ZMod 716333897) ^ 683 = (3 : ZMod 716333897) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 341 * (3 : ZMod 716333897) ^ 341) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 596474834 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 716333897) ^ 1366 = 483809964 := by
        calc
          (3 : ZMod 716333897) ^ 1366 = (3 : ZMod 716333897) ^ (683 + 683) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 683 * (3 : ZMod 716333897) ^ 683 := by rw [pow_add]
          _ = 483809964 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 716333897) ^ 2732 = 457078292 := by
        calc
          (3 : ZMod 716333897) ^ 2732 = (3 : ZMod 716333897) ^ (1366 + 1366) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 1366 * (3 : ZMod 716333897) ^ 1366 := by rw [pow_add]
          _ = 457078292 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 716333897) ^ 5465 = 142217305 := by
        calc
          (3 : ZMod 716333897) ^ 5465 = (3 : ZMod 716333897) ^ (2732 + 2732 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 2732 * (3 : ZMod 716333897) ^ 2732) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 142217305 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 716333897) ^ 10930 = 477276634 := by
        calc
          (3 : ZMod 716333897) ^ 10930 = (3 : ZMod 716333897) ^ (5465 + 5465) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 5465 * (3 : ZMod 716333897) ^ 5465 := by rw [pow_add]
          _ = 477276634 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 716333897) ^ 21860 = 244976255 := by
        calc
          (3 : ZMod 716333897) ^ 21860 = (3 : ZMod 716333897) ^ (10930 + 10930) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 10930 * (3 : ZMod 716333897) ^ 10930 := by rw [pow_add]
          _ = 244976255 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 716333897) ^ 43721 = 635731498 := by
        calc
          (3 : ZMod 716333897) ^ 43721 = (3 : ZMod 716333897) ^ (21860 + 21860 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 21860 * (3 : ZMod 716333897) ^ 21860) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 635731498 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 716333897) ^ 87443 = 426244254 := by
        calc
          (3 : ZMod 716333897) ^ 87443 = (3 : ZMod 716333897) ^ (43721 + 43721 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 43721 * (3 : ZMod 716333897) ^ 43721) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 426244254 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 716333897) ^ 174886 = 206593681 := by
        calc
          (3 : ZMod 716333897) ^ 174886 = (3 : ZMod 716333897) ^ (87443 + 87443) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 87443 * (3 : ZMod 716333897) ^ 87443 := by rw [pow_add]
          _ = 206593681 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 716333897) ^ 349772 = 370472995 := by
        calc
          (3 : ZMod 716333897) ^ 349772 = (3 : ZMod 716333897) ^ (174886 + 174886) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 174886 * (3 : ZMod 716333897) ^ 174886 := by rw [pow_add]
          _ = 370472995 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 716333897) ^ 699544 = 601213609 := by
        calc
          (3 : ZMod 716333897) ^ 699544 = (3 : ZMod 716333897) ^ (349772 + 349772) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 349772 * (3 : ZMod 716333897) ^ 349772 := by rw [pow_add]
          _ = 601213609 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 716333897) ^ 1399089 = 95920059 := by
        calc
          (3 : ZMod 716333897) ^ 1399089 = (3 : ZMod 716333897) ^ (699544 + 699544 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 699544 * (3 : ZMod 716333897) ^ 699544) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 95920059 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 716333897) ^ 2798179 = 593666459 := by
        calc
          (3 : ZMod 716333897) ^ 2798179 = (3 : ZMod 716333897) ^ (1399089 + 1399089 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 1399089 * (3 : ZMod 716333897) ^ 1399089) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 593666459 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 716333897) ^ 5596358 = 533776402 := by
        calc
          (3 : ZMod 716333897) ^ 5596358 = (3 : ZMod 716333897) ^ (2798179 + 2798179) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 2798179 * (3 : ZMod 716333897) ^ 2798179 := by rw [pow_add]
          _ = 533776402 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 716333897) ^ 11192717 = 662045615 := by
        calc
          (3 : ZMod 716333897) ^ 11192717 = (3 : ZMod 716333897) ^ (5596358 + 5596358 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 5596358 * (3 : ZMod 716333897) ^ 5596358) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 662045615 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 716333897) ^ 22385434 = 712081042 := by
        calc
          (3 : ZMod 716333897) ^ 22385434 = (3 : ZMod 716333897) ^ (11192717 + 11192717) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 11192717 * (3 : ZMod 716333897) ^ 11192717 := by rw [pow_add]
          _ = 712081042 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 716333897) ^ 44770868 = 61085672 := by
        calc
          (3 : ZMod 716333897) ^ 44770868 = (3 : ZMod 716333897) ^ (22385434 + 22385434) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 22385434 * (3 : ZMod 716333897) ^ 22385434 := by rw [pow_add]
          _ = 61085672 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 716333897) ^ 89541737 = 368476506 := by
        calc
          (3 : ZMod 716333897) ^ 89541737 = (3 : ZMod 716333897) ^ (44770868 + 44770868 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 44770868 * (3 : ZMod 716333897) ^ 44770868) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 368476506 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 716333897) ^ 179083474 = 38461060 := by
        calc
          (3 : ZMod 716333897) ^ 179083474 = (3 : ZMod 716333897) ^ (89541737 + 89541737) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 89541737 * (3 : ZMod 716333897) ^ 89541737 := by rw [pow_add]
          _ = 38461060 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 716333897) ^ 358166948 = 716333896 := by
        calc
          (3 : ZMod 716333897) ^ 358166948 = (3 : ZMod 716333897) ^ (179083474 + 179083474) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 179083474 * (3 : ZMod 716333897) ^ 179083474 := by rw [pow_add]
          _ = 716333896 := by rw [factor_0_27]; decide
      change (3 : ZMod 716333897) ^ 358166948 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (3 : ZMod 716333897) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 716333897) ^ 2 = 9 := by
        calc
          (3 : ZMod 716333897) ^ 2 = (3 : ZMod 716333897) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 1 * (3 : ZMod 716333897) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 716333897) ^ 5 = 243 := by
        calc
          (3 : ZMod 716333897) ^ 5 = (3 : ZMod 716333897) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 2 * (3 : ZMod 716333897) ^ 2) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 716333897) ^ 10 = 59049 := by
        calc
          (3 : ZMod 716333897) ^ 10 = (3 : ZMod 716333897) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 5 * (3 : ZMod 716333897) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 716333897) ^ 20 = 621448813 := by
        calc
          (3 : ZMod 716333897) ^ 20 = (3 : ZMod 716333897) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 10 * (3 : ZMod 716333897) ^ 10 := by rw [pow_add]
          _ = 621448813 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 716333897) ^ 40 = 334959389 := by
        calc
          (3 : ZMod 716333897) ^ 40 = (3 : ZMod 716333897) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 20 * (3 : ZMod 716333897) ^ 20 := by rw [pow_add]
          _ = 334959389 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 716333897) ^ 80 = 671725176 := by
        calc
          (3 : ZMod 716333897) ^ 80 = (3 : ZMod 716333897) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 40 * (3 : ZMod 716333897) ^ 40 := by rw [pow_add]
          _ = 671725176 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 716333897) ^ 160 = 389086382 := by
        calc
          (3 : ZMod 716333897) ^ 160 = (3 : ZMod 716333897) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 80 * (3 : ZMod 716333897) ^ 80 := by rw [pow_add]
          _ = 389086382 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 716333897) ^ 321 = 265176242 := by
        calc
          (3 : ZMod 716333897) ^ 321 = (3 : ZMod 716333897) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 160 * (3 : ZMod 716333897) ^ 160) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 265176242 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 716333897) ^ 642 = 116946863 := by
        calc
          (3 : ZMod 716333897) ^ 642 = (3 : ZMod 716333897) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 321 * (3 : ZMod 716333897) ^ 321 := by rw [pow_add]
          _ = 116946863 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 716333897) ^ 1285 = 393957151 := by
        calc
          (3 : ZMod 716333897) ^ 1285 = (3 : ZMod 716333897) ^ (642 + 642 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 642 * (3 : ZMod 716333897) ^ 642) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 393957151 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 716333897) ^ 2571 = 509900070 := by
        calc
          (3 : ZMod 716333897) ^ 2571 = (3 : ZMod 716333897) ^ (1285 + 1285 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 1285 * (3 : ZMod 716333897) ^ 1285) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 509900070 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 716333897) ^ 5143 = 150485268 := by
        calc
          (3 : ZMod 716333897) ^ 5143 = (3 : ZMod 716333897) ^ (2571 + 2571 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 2571 * (3 : ZMod 716333897) ^ 2571) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 150485268 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 716333897) ^ 10287 = 605014397 := by
        calc
          (3 : ZMod 716333897) ^ 10287 = (3 : ZMod 716333897) ^ (5143 + 5143 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 5143 * (3 : ZMod 716333897) ^ 5143) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 605014397 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 716333897) ^ 20574 = 508579514 := by
        calc
          (3 : ZMod 716333897) ^ 20574 = (3 : ZMod 716333897) ^ (10287 + 10287) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 10287 * (3 : ZMod 716333897) ^ 10287 := by rw [pow_add]
          _ = 508579514 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 716333897) ^ 41149 = 356185322 := by
        calc
          (3 : ZMod 716333897) ^ 41149 = (3 : ZMod 716333897) ^ (20574 + 20574 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 20574 * (3 : ZMod 716333897) ^ 20574) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 356185322 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 716333897) ^ 82299 = 598903816 := by
        calc
          (3 : ZMod 716333897) ^ 82299 = (3 : ZMod 716333897) ^ (41149 + 41149 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 41149 * (3 : ZMod 716333897) ^ 41149) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 598903816 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 716333897) ^ 164598 = 273771520 := by
        calc
          (3 : ZMod 716333897) ^ 164598 = (3 : ZMod 716333897) ^ (82299 + 82299) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 82299 * (3 : ZMod 716333897) ^ 82299 := by rw [pow_add]
          _ = 273771520 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 716333897) ^ 329197 = 16043022 := by
        calc
          (3 : ZMod 716333897) ^ 329197 = (3 : ZMod 716333897) ^ (164598 + 164598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 164598 * (3 : ZMod 716333897) ^ 164598) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 16043022 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 716333897) ^ 658395 = 73435049 := by
        calc
          (3 : ZMod 716333897) ^ 658395 = (3 : ZMod 716333897) ^ (329197 + 329197 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 329197 * (3 : ZMod 716333897) ^ 329197) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 73435049 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 716333897) ^ 1316790 = 145569207 := by
        calc
          (3 : ZMod 716333897) ^ 1316790 = (3 : ZMod 716333897) ^ (658395 + 658395) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 658395 * (3 : ZMod 716333897) ^ 658395 := by rw [pow_add]
          _ = 145569207 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 716333897) ^ 2633580 = 244708730 := by
        calc
          (3 : ZMod 716333897) ^ 2633580 = (3 : ZMod 716333897) ^ (1316790 + 1316790) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 1316790 * (3 : ZMod 716333897) ^ 1316790 := by rw [pow_add]
          _ = 244708730 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 716333897) ^ 5267161 = 421811306 := by
        calc
          (3 : ZMod 716333897) ^ 5267161 = (3 : ZMod 716333897) ^ (2633580 + 2633580 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 2633580 * (3 : ZMod 716333897) ^ 2633580) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 421811306 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 716333897) ^ 10534322 = 202177325 := by
        calc
          (3 : ZMod 716333897) ^ 10534322 = (3 : ZMod 716333897) ^ (5267161 + 5267161) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 5267161 * (3 : ZMod 716333897) ^ 5267161 := by rw [pow_add]
          _ = 202177325 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 716333897) ^ 21068644 = 268364070 := by
        calc
          (3 : ZMod 716333897) ^ 21068644 = (3 : ZMod 716333897) ^ (10534322 + 10534322) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 10534322 * (3 : ZMod 716333897) ^ 10534322 := by rw [pow_add]
          _ = 268364070 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 716333897) ^ 42137288 = 310988279 := by
        calc
          (3 : ZMod 716333897) ^ 42137288 = (3 : ZMod 716333897) ^ (21068644 + 21068644) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 21068644 * (3 : ZMod 716333897) ^ 21068644 := by rw [pow_add]
          _ = 310988279 := by rw [factor_1_24]; decide
      change (3 : ZMod 716333897) ^ 42137288 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (3 : ZMod 716333897) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 716333897) ^ 2 = 9 := by
        calc
          (3 : ZMod 716333897) ^ 2 = (3 : ZMod 716333897) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 1 * (3 : ZMod 716333897) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 716333897) ^ 4 = 81 := by
        calc
          (3 : ZMod 716333897) ^ 4 = (3 : ZMod 716333897) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 2 * (3 : ZMod 716333897) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 716333897) ^ 8 = 6561 := by
        calc
          (3 : ZMod 716333897) ^ 8 = (3 : ZMod 716333897) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 4 * (3 : ZMod 716333897) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 716333897) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 716333897) ^ 17 = (3 : ZMod 716333897) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 8 * (3 : ZMod 716333897) ^ 8) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 716333897) ^ 35 = 626328171 := by
        calc
          (3 : ZMod 716333897) ^ 35 = (3 : ZMod 716333897) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 17 * (3 : ZMod 716333897) ^ 17) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 626328171 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 716333897) ^ 71 = 496150760 := by
        calc
          (3 : ZMod 716333897) ^ 71 = (3 : ZMod 716333897) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 35 * (3 : ZMod 716333897) ^ 35) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 496150760 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 716333897) ^ 143 = 139309447 := by
        calc
          (3 : ZMod 716333897) ^ 143 = (3 : ZMod 716333897) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 71 * (3 : ZMod 716333897) ^ 71) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 139309447 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 716333897) ^ 287 = 508617389 := by
        calc
          (3 : ZMod 716333897) ^ 287 = (3 : ZMod 716333897) ^ (143 + 143 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 143 * (3 : ZMod 716333897) ^ 143) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 508617389 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 716333897) ^ 575 = 312675541 := by
        calc
          (3 : ZMod 716333897) ^ 575 = (3 : ZMod 716333897) ^ (287 + 287 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 287 * (3 : ZMod 716333897) ^ 287) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 312675541 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 716333897) ^ 1150 = 122497595 := by
        calc
          (3 : ZMod 716333897) ^ 1150 = (3 : ZMod 716333897) ^ (575 + 575) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 575 * (3 : ZMod 716333897) ^ 575 := by rw [pow_add]
          _ = 122497595 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 716333897) ^ 2301 = 77524197 := by
        calc
          (3 : ZMod 716333897) ^ 2301 = (3 : ZMod 716333897) ^ (1150 + 1150 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 1150 * (3 : ZMod 716333897) ^ 1150) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 77524197 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 716333897) ^ 4602 = 555696938 := by
        calc
          (3 : ZMod 716333897) ^ 4602 = (3 : ZMod 716333897) ^ (2301 + 2301) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 2301 * (3 : ZMod 716333897) ^ 2301 := by rw [pow_add]
          _ = 555696938 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 716333897) ^ 9204 = 236010777 := by
        calc
          (3 : ZMod 716333897) ^ 9204 = (3 : ZMod 716333897) ^ (4602 + 4602) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 4602 * (3 : ZMod 716333897) ^ 4602 := by rw [pow_add]
          _ = 236010777 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 716333897) ^ 18409 = 126385858 := by
        calc
          (3 : ZMod 716333897) ^ 18409 = (3 : ZMod 716333897) ^ (9204 + 9204 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 9204 * (3 : ZMod 716333897) ^ 9204) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 126385858 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 716333897) ^ 36818 = 232640358 := by
        calc
          (3 : ZMod 716333897) ^ 36818 = (3 : ZMod 716333897) ^ (18409 + 18409) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 18409 * (3 : ZMod 716333897) ^ 18409 := by rw [pow_add]
          _ = 232640358 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 716333897) ^ 73636 = 218043076 := by
        calc
          (3 : ZMod 716333897) ^ 73636 = (3 : ZMod 716333897) ^ (36818 + 36818) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 36818 * (3 : ZMod 716333897) ^ 36818 := by rw [pow_add]
          _ = 218043076 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 716333897) ^ 147272 = 242552928 := by
        calc
          (3 : ZMod 716333897) ^ 147272 = (3 : ZMod 716333897) ^ (73636 + 73636) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 73636 * (3 : ZMod 716333897) ^ 73636 := by rw [pow_add]
          _ = 242552928 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 716333897) ^ 294545 = 453659262 := by
        calc
          (3 : ZMod 716333897) ^ 294545 = (3 : ZMod 716333897) ^ (147272 + 147272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 147272 * (3 : ZMod 716333897) ^ 147272) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 453659262 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 716333897) ^ 589090 = 247139384 := by
        calc
          (3 : ZMod 716333897) ^ 589090 = (3 : ZMod 716333897) ^ (294545 + 294545) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 294545 * (3 : ZMod 716333897) ^ 294545 := by rw [pow_add]
          _ = 247139384 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 716333897) ^ 1178180 = 640458252 := by
        calc
          (3 : ZMod 716333897) ^ 1178180 = (3 : ZMod 716333897) ^ (589090 + 589090) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 589090 * (3 : ZMod 716333897) ^ 589090 := by rw [pow_add]
          _ = 640458252 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 716333897) ^ 2356361 = 168744295 := by
        calc
          (3 : ZMod 716333897) ^ 2356361 = (3 : ZMod 716333897) ^ (1178180 + 1178180 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 1178180 * (3 : ZMod 716333897) ^ 1178180) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 168744295 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 716333897) ^ 4712723 = 226030356 := by
        calc
          (3 : ZMod 716333897) ^ 4712723 = (3 : ZMod 716333897) ^ (2356361 + 2356361 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 2356361 * (3 : ZMod 716333897) ^ 2356361) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 226030356 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 716333897) ^ 9425446 = 332160036 := by
        calc
          (3 : ZMod 716333897) ^ 9425446 = (3 : ZMod 716333897) ^ (4712723 + 4712723) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 4712723 * (3 : ZMod 716333897) ^ 4712723 := by rw [pow_add]
          _ = 332160036 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 716333897) ^ 18850892 = 434821267 := by
        calc
          (3 : ZMod 716333897) ^ 18850892 = (3 : ZMod 716333897) ^ (9425446 + 9425446) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 9425446 * (3 : ZMod 716333897) ^ 9425446 := by rw [pow_add]
          _ = 434821267 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 716333897) ^ 37701784 = 131017819 := by
        calc
          (3 : ZMod 716333897) ^ 37701784 = (3 : ZMod 716333897) ^ (18850892 + 18850892) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 18850892 * (3 : ZMod 716333897) ^ 18850892 := by rw [pow_add]
          _ = 131017819 := by rw [factor_2_24]; decide
      change (3 : ZMod 716333897) ^ 37701784 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (3 : ZMod 716333897) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 716333897) ^ 3 = 27 := by
        calc
          (3 : ZMod 716333897) ^ 3 = (3 : ZMod 716333897) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 1 * (3 : ZMod 716333897) ^ 1) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 716333897) ^ 7 = 2187 := by
        calc
          (3 : ZMod 716333897) ^ 7 = (3 : ZMod 716333897) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 3 * (3 : ZMod 716333897) ^ 3) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 716333897) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 716333897) ^ 14 = (3 : ZMod 716333897) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 7 * (3 : ZMod 716333897) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 716333897) ^ 29 = 575695004 := by
        calc
          (3 : ZMod 716333897) ^ 29 = (3 : ZMod 716333897) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 14 * (3 : ZMod 716333897) ^ 14) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 575695004 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 716333897) ^ 59 = 239505422 := by
        calc
          (3 : ZMod 716333897) ^ 59 = (3 : ZMod 716333897) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 29 * (3 : ZMod 716333897) ^ 29) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 239505422 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 716333897) ^ 118 = 617893576 := by
        calc
          (3 : ZMod 716333897) ^ 118 = (3 : ZMod 716333897) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 59 * (3 : ZMod 716333897) ^ 59 := by rw [pow_add]
          _ = 617893576 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 716333897) ^ 237 = 391395665 := by
        calc
          (3 : ZMod 716333897) ^ 237 = (3 : ZMod 716333897) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 118 * (3 : ZMod 716333897) ^ 118) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 391395665 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 716333897) ^ 475 = 426644071 := by
        calc
          (3 : ZMod 716333897) ^ 475 = (3 : ZMod 716333897) ^ (237 + 237 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 237 * (3 : ZMod 716333897) ^ 237) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 426644071 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 716333897) ^ 950 = 167705708 := by
        calc
          (3 : ZMod 716333897) ^ 950 = (3 : ZMod 716333897) ^ (475 + 475) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 475 * (3 : ZMod 716333897) ^ 475 := by rw [pow_add]
          _ = 167705708 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 716333897) ^ 1900 = 165371570 := by
        calc
          (3 : ZMod 716333897) ^ 1900 = (3 : ZMod 716333897) ^ (950 + 950) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 950 * (3 : ZMod 716333897) ^ 950 := by rw [pow_add]
          _ = 165371570 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 716333897) ^ 3801 = 704501077 := by
        calc
          (3 : ZMod 716333897) ^ 3801 = (3 : ZMod 716333897) ^ (1900 + 1900 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 1900 * (3 : ZMod 716333897) ^ 1900) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 704501077 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 716333897) ^ 7603 = 151598752 := by
        calc
          (3 : ZMod 716333897) ^ 7603 = (3 : ZMod 716333897) ^ (3801 + 3801 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 3801 * (3 : ZMod 716333897) ^ 3801) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 151598752 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 716333897) ^ 15207 = 362089228 := by
        calc
          (3 : ZMod 716333897) ^ 15207 = (3 : ZMod 716333897) ^ (7603 + 7603 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 7603 * (3 : ZMod 716333897) ^ 7603) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 362089228 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 716333897) ^ 30414 = 110620674 := by
        calc
          (3 : ZMod 716333897) ^ 30414 = (3 : ZMod 716333897) ^ (15207 + 15207) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 15207 * (3 : ZMod 716333897) ^ 15207 := by rw [pow_add]
          _ = 110620674 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 716333897) ^ 60829 = 651092132 := by
        calc
          (3 : ZMod 716333897) ^ 60829 = (3 : ZMod 716333897) ^ (30414 + 30414 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 30414 * (3 : ZMod 716333897) ^ 30414) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 651092132 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 716333897) ^ 121659 = 380615374 := by
        calc
          (3 : ZMod 716333897) ^ 121659 = (3 : ZMod 716333897) ^ (60829 + 60829 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 60829 * (3 : ZMod 716333897) ^ 60829) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 380615374 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 716333897) ^ 243319 = 132440211 := by
        calc
          (3 : ZMod 716333897) ^ 243319 = (3 : ZMod 716333897) ^ (121659 + 121659 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 121659 * (3 : ZMod 716333897) ^ 121659) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 132440211 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 716333897) ^ 486639 = 139072700 := by
        calc
          (3 : ZMod 716333897) ^ 486639 = (3 : ZMod 716333897) ^ (243319 + 243319 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 243319 * (3 : ZMod 716333897) ^ 243319) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 139072700 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 716333897) ^ 973279 = 278396520 := by
        calc
          (3 : ZMod 716333897) ^ 973279 = (3 : ZMod 716333897) ^ (486639 + 486639 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 486639 * (3 : ZMod 716333897) ^ 486639) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 278396520 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 716333897) ^ 1946559 = 141184210 := by
        calc
          (3 : ZMod 716333897) ^ 1946559 = (3 : ZMod 716333897) ^ (973279 + 973279 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 973279 * (3 : ZMod 716333897) ^ 973279) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 141184210 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 716333897) ^ 3893119 = 54892544 := by
        calc
          (3 : ZMod 716333897) ^ 3893119 = (3 : ZMod 716333897) ^ (1946559 + 1946559 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 1946559 * (3 : ZMod 716333897) ^ 1946559) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 54892544 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 716333897) ^ 7786238 = 184447754 := by
        calc
          (3 : ZMod 716333897) ^ 7786238 = (3 : ZMod 716333897) ^ (3893119 + 3893119) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 3893119 * (3 : ZMod 716333897) ^ 3893119 := by rw [pow_add]
          _ = 184447754 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 716333897) ^ 15572476 = 677989850 := by
        calc
          (3 : ZMod 716333897) ^ 15572476 = (3 : ZMod 716333897) ^ (7786238 + 7786238) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 7786238 * (3 : ZMod 716333897) ^ 7786238 := by rw [pow_add]
          _ = 677989850 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 716333897) ^ 31144952 = 645420267 := by
        calc
          (3 : ZMod 716333897) ^ 31144952 = (3 : ZMod 716333897) ^ (15572476 + 15572476) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 15572476 * (3 : ZMod 716333897) ^ 15572476 := by rw [pow_add]
          _ = 645420267 := by rw [factor_3_23]; decide
      change (3 : ZMod 716333897) ^ 31144952 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (3 : ZMod 716333897) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 716333897) ^ 3 = 27 := by
        calc
          (3 : ZMod 716333897) ^ 3 = (3 : ZMod 716333897) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 1 * (3 : ZMod 716333897) ^ 1) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 716333897) ^ 7 = 2187 := by
        calc
          (3 : ZMod 716333897) ^ 7 = (3 : ZMod 716333897) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 3 * (3 : ZMod 716333897) ^ 3) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 716333897) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 716333897) ^ 15 = (3 : ZMod 716333897) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 7 * (3 : ZMod 716333897) ^ 7) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 716333897) ^ 30 = 294417218 := by
        calc
          (3 : ZMod 716333897) ^ 30 = (3 : ZMod 716333897) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 15 * (3 : ZMod 716333897) ^ 15 := by rw [pow_add]
          _ = 294417218 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 716333897) ^ 61 = 6547107 := by
        calc
          (3 : ZMod 716333897) ^ 61 = (3 : ZMod 716333897) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 30 * (3 : ZMod 716333897) ^ 30) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 6547107 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 716333897) ^ 123 = 434354495 := by
        calc
          (3 : ZMod 716333897) ^ 123 = (3 : ZMod 716333897) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 61 * (3 : ZMod 716333897) ^ 61) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 434354495 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 716333897) ^ 246 = 386145857 := by
        calc
          (3 : ZMod 716333897) ^ 246 = (3 : ZMod 716333897) ^ (123 + 123) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 123 * (3 : ZMod 716333897) ^ 123 := by rw [pow_add]
          _ = 386145857 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 716333897) ^ 493 = 440356911 := by
        calc
          (3 : ZMod 716333897) ^ 493 = (3 : ZMod 716333897) ^ (246 + 246 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 246 * (3 : ZMod 716333897) ^ 246) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 440356911 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 716333897) ^ 986 = 649165004 := by
        calc
          (3 : ZMod 716333897) ^ 986 = (3 : ZMod 716333897) ^ (493 + 493) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 493 * (3 : ZMod 716333897) ^ 493 := by rw [pow_add]
          _ = 649165004 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 716333897) ^ 1973 = 574171923 := by
        calc
          (3 : ZMod 716333897) ^ 1973 = (3 : ZMod 716333897) ^ (986 + 986 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 986 * (3 : ZMod 716333897) ^ 986) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 574171923 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 716333897) ^ 3946 = 477771787 := by
        calc
          (3 : ZMod 716333897) ^ 3946 = (3 : ZMod 716333897) ^ (1973 + 1973) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 1973 * (3 : ZMod 716333897) ^ 1973 := by rw [pow_add]
          _ = 477771787 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 716333897) ^ 7893 = 334674547 := by
        calc
          (3 : ZMod 716333897) ^ 7893 = (3 : ZMod 716333897) ^ (3946 + 3946 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 3946 * (3 : ZMod 716333897) ^ 3946) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 334674547 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 716333897) ^ 15786 = 461549048 := by
        calc
          (3 : ZMod 716333897) ^ 15786 = (3 : ZMod 716333897) ^ (7893 + 7893) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 7893 * (3 : ZMod 716333897) ^ 7893 := by rw [pow_add]
          _ = 461549048 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 716333897) ^ 31573 = 525410743 := by
        calc
          (3 : ZMod 716333897) ^ 31573 = (3 : ZMod 716333897) ^ (15786 + 15786 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 15786 * (3 : ZMod 716333897) ^ 15786) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 525410743 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 716333897) ^ 63146 = 382342504 := by
        calc
          (3 : ZMod 716333897) ^ 63146 = (3 : ZMod 716333897) ^ (31573 + 31573) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 31573 * (3 : ZMod 716333897) ^ 31573 := by rw [pow_add]
          _ = 382342504 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 716333897) ^ 126293 = 1595624 := by
        calc
          (3 : ZMod 716333897) ^ 126293 = (3 : ZMod 716333897) ^ (63146 + 63146 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = ((3 : ZMod 716333897) ^ 63146 * (3 : ZMod 716333897) ^ 63146) * (3 : ZMod 716333897) := by rw [pow_succ, pow_add]
          _ = 1595624 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 716333897) ^ 252586 = 165279438 := by
        calc
          (3 : ZMod 716333897) ^ 252586 = (3 : ZMod 716333897) ^ (126293 + 126293) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 126293 * (3 : ZMod 716333897) ^ 126293 := by rw [pow_add]
          _ = 165279438 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 716333897) ^ 505172 = 466580321 := by
        calc
          (3 : ZMod 716333897) ^ 505172 = (3 : ZMod 716333897) ^ (252586 + 252586) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 252586 * (3 : ZMod 716333897) ^ 252586 := by rw [pow_add]
          _ = 466580321 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 716333897) ^ 1010344 = 140547064 := by
        calc
          (3 : ZMod 716333897) ^ 1010344 = (3 : ZMod 716333897) ^ (505172 + 505172) :=
            congrArg (fun n : ℕ => (3 : ZMod 716333897) ^ n) (by norm_num)
          _ = (3 : ZMod 716333897) ^ 505172 * (3 : ZMod 716333897) ^ 505172 := by rw [pow_add]
          _ = 140547064 := by rw [factor_4_18]; decide
      change (3 : ZMod 716333897) ^ 1010344 ≠ 1
      rw [factor_4_19]
      decide

#print axioms prime_lucas_716333897

end TotientTailPeriodKiller
end Erdos249257
