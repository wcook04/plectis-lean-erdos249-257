import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_191238161 : Nat.Prime 191238161 := by
  apply lucas_primality 191238161 (3 : ZMod 191238161)
  ·
      have fermat_0 : (3 : ZMod 191238161) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 191238161) ^ 2 = 9 := by
        calc
          (3 : ZMod 191238161) ^ 2 = (3 : ZMod 191238161) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 1 * (3 : ZMod 191238161) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 191238161) ^ 5 = 243 := by
        calc
          (3 : ZMod 191238161) ^ 5 = (3 : ZMod 191238161) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 2 * (3 : ZMod 191238161) ^ 2) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 191238161) ^ 11 = 177147 := by
        calc
          (3 : ZMod 191238161) ^ 11 = (3 : ZMod 191238161) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 5 * (3 : ZMod 191238161) ^ 5) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 191238161) ^ 22 = 18001205 := by
        calc
          (3 : ZMod 191238161) ^ 22 = (3 : ZMod 191238161) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 11 * (3 : ZMod 191238161) ^ 11 := by rw [pow_add]
          _ = 18001205 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 191238161) ^ 45 = 21113047 := by
        calc
          (3 : ZMod 191238161) ^ 45 = (3 : ZMod 191238161) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 22 * (3 : ZMod 191238161) ^ 22) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 21113047 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 191238161) ^ 91 = 80634589 := by
        calc
          (3 : ZMod 191238161) ^ 91 = (3 : ZMod 191238161) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 45 * (3 : ZMod 191238161) ^ 45) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 80634589 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 191238161) ^ 182 = 109254161 := by
        calc
          (3 : ZMod 191238161) ^ 182 = (3 : ZMod 191238161) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 91 * (3 : ZMod 191238161) ^ 91 := by rw [pow_add]
          _ = 109254161 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 191238161) ^ 364 = 134405214 := by
        calc
          (3 : ZMod 191238161) ^ 364 = (3 : ZMod 191238161) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 182 * (3 : ZMod 191238161) ^ 182 := by rw [pow_add]
          _ = 134405214 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 191238161) ^ 729 = 33416877 := by
        calc
          (3 : ZMod 191238161) ^ 729 = (3 : ZMod 191238161) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 364 * (3 : ZMod 191238161) ^ 364) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 33416877 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 191238161) ^ 1459 = 136727154 := by
        calc
          (3 : ZMod 191238161) ^ 1459 = (3 : ZMod 191238161) ^ (729 + 729 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 729 * (3 : ZMod 191238161) ^ 729) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 136727154 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 191238161) ^ 2918 = 135491455 := by
        calc
          (3 : ZMod 191238161) ^ 2918 = (3 : ZMod 191238161) ^ (1459 + 1459) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 1459 * (3 : ZMod 191238161) ^ 1459 := by rw [pow_add]
          _ = 135491455 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 191238161) ^ 5836 = 148241324 := by
        calc
          (3 : ZMod 191238161) ^ 5836 = (3 : ZMod 191238161) ^ (2918 + 2918) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 2918 * (3 : ZMod 191238161) ^ 2918 := by rw [pow_add]
          _ = 148241324 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 191238161) ^ 11672 = 3893419 := by
        calc
          (3 : ZMod 191238161) ^ 11672 = (3 : ZMod 191238161) ^ (5836 + 5836) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 5836 * (3 : ZMod 191238161) ^ 5836 := by rw [pow_add]
          _ = 3893419 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 191238161) ^ 23344 = 27439735 := by
        calc
          (3 : ZMod 191238161) ^ 23344 = (3 : ZMod 191238161) ^ (11672 + 11672) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 11672 * (3 : ZMod 191238161) ^ 11672 := by rw [pow_add]
          _ = 27439735 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 191238161) ^ 46689 = 173670896 := by
        calc
          (3 : ZMod 191238161) ^ 46689 = (3 : ZMod 191238161) ^ (23344 + 23344 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 23344 * (3 : ZMod 191238161) ^ 23344) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 173670896 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 191238161) ^ 93378 = 129648085 := by
        calc
          (3 : ZMod 191238161) ^ 93378 = (3 : ZMod 191238161) ^ (46689 + 46689) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 46689 * (3 : ZMod 191238161) ^ 46689 := by rw [pow_add]
          _ = 129648085 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 191238161) ^ 186756 = 26206584 := by
        calc
          (3 : ZMod 191238161) ^ 186756 = (3 : ZMod 191238161) ^ (93378 + 93378) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 93378 * (3 : ZMod 191238161) ^ 93378 := by rw [pow_add]
          _ = 26206584 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 191238161) ^ 373512 = 43067001 := by
        calc
          (3 : ZMod 191238161) ^ 373512 = (3 : ZMod 191238161) ^ (186756 + 186756) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 186756 * (3 : ZMod 191238161) ^ 186756 := by rw [pow_add]
          _ = 43067001 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 191238161) ^ 747024 = 50851115 := by
        calc
          (3 : ZMod 191238161) ^ 747024 = (3 : ZMod 191238161) ^ (373512 + 373512) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 373512 * (3 : ZMod 191238161) ^ 373512 := by rw [pow_add]
          _ = 50851115 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 191238161) ^ 1494048 = 114588158 := by
        calc
          (3 : ZMod 191238161) ^ 1494048 = (3 : ZMod 191238161) ^ (747024 + 747024) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 747024 * (3 : ZMod 191238161) ^ 747024 := by rw [pow_add]
          _ = 114588158 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 191238161) ^ 2988096 = 161656628 := by
        calc
          (3 : ZMod 191238161) ^ 2988096 = (3 : ZMod 191238161) ^ (1494048 + 1494048) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 1494048 * (3 : ZMod 191238161) ^ 1494048 := by rw [pow_add]
          _ = 161656628 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 191238161) ^ 5976192 = 91240772 := by
        calc
          (3 : ZMod 191238161) ^ 5976192 = (3 : ZMod 191238161) ^ (2988096 + 2988096) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 2988096 * (3 : ZMod 191238161) ^ 2988096 := by rw [pow_add]
          _ = 91240772 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 191238161) ^ 11952385 = 46473459 := by
        calc
          (3 : ZMod 191238161) ^ 11952385 = (3 : ZMod 191238161) ^ (5976192 + 5976192 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 5976192 * (3 : ZMod 191238161) ^ 5976192) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 46473459 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 191238161) ^ 23904770 = 179778523 := by
        calc
          (3 : ZMod 191238161) ^ 23904770 = (3 : ZMod 191238161) ^ (11952385 + 11952385) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 11952385 * (3 : ZMod 191238161) ^ 11952385 := by rw [pow_add]
          _ = 179778523 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 191238161) ^ 47809540 = 57932344 := by
        calc
          (3 : ZMod 191238161) ^ 47809540 = (3 : ZMod 191238161) ^ (23904770 + 23904770) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 23904770 * (3 : ZMod 191238161) ^ 23904770 := by rw [pow_add]
          _ = 57932344 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 191238161) ^ 95619080 = 191238160 := by
        calc
          (3 : ZMod 191238161) ^ 95619080 = (3 : ZMod 191238161) ^ (47809540 + 47809540) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 47809540 * (3 : ZMod 191238161) ^ 47809540 := by rw [pow_add]
          _ = 191238160 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 191238161) ^ 191238160 = 1 := by
        calc
          (3 : ZMod 191238161) ^ 191238160 = (3 : ZMod 191238161) ^ (95619080 + 95619080) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 95619080 * (3 : ZMod 191238161) ^ 95619080 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (2390477, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (2390477, 1)] : List FactorBlock).map factorBlockValue).prod = 191238161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 191238161) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 191238161) ^ 2 = 9 := by
        calc
          (3 : ZMod 191238161) ^ 2 = (3 : ZMod 191238161) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 1 * (3 : ZMod 191238161) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 191238161) ^ 5 = 243 := by
        calc
          (3 : ZMod 191238161) ^ 5 = (3 : ZMod 191238161) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 2 * (3 : ZMod 191238161) ^ 2) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 191238161) ^ 11 = 177147 := by
        calc
          (3 : ZMod 191238161) ^ 11 = (3 : ZMod 191238161) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 5 * (3 : ZMod 191238161) ^ 5) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 191238161) ^ 22 = 18001205 := by
        calc
          (3 : ZMod 191238161) ^ 22 = (3 : ZMod 191238161) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 11 * (3 : ZMod 191238161) ^ 11 := by rw [pow_add]
          _ = 18001205 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 191238161) ^ 45 = 21113047 := by
        calc
          (3 : ZMod 191238161) ^ 45 = (3 : ZMod 191238161) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 22 * (3 : ZMod 191238161) ^ 22) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 21113047 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 191238161) ^ 91 = 80634589 := by
        calc
          (3 : ZMod 191238161) ^ 91 = (3 : ZMod 191238161) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 45 * (3 : ZMod 191238161) ^ 45) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 80634589 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 191238161) ^ 182 = 109254161 := by
        calc
          (3 : ZMod 191238161) ^ 182 = (3 : ZMod 191238161) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 91 * (3 : ZMod 191238161) ^ 91 := by rw [pow_add]
          _ = 109254161 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 191238161) ^ 364 = 134405214 := by
        calc
          (3 : ZMod 191238161) ^ 364 = (3 : ZMod 191238161) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 182 * (3 : ZMod 191238161) ^ 182 := by rw [pow_add]
          _ = 134405214 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 191238161) ^ 729 = 33416877 := by
        calc
          (3 : ZMod 191238161) ^ 729 = (3 : ZMod 191238161) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 364 * (3 : ZMod 191238161) ^ 364) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 33416877 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 191238161) ^ 1459 = 136727154 := by
        calc
          (3 : ZMod 191238161) ^ 1459 = (3 : ZMod 191238161) ^ (729 + 729 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 729 * (3 : ZMod 191238161) ^ 729) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 136727154 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 191238161) ^ 2918 = 135491455 := by
        calc
          (3 : ZMod 191238161) ^ 2918 = (3 : ZMod 191238161) ^ (1459 + 1459) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 1459 * (3 : ZMod 191238161) ^ 1459 := by rw [pow_add]
          _ = 135491455 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 191238161) ^ 5836 = 148241324 := by
        calc
          (3 : ZMod 191238161) ^ 5836 = (3 : ZMod 191238161) ^ (2918 + 2918) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 2918 * (3 : ZMod 191238161) ^ 2918 := by rw [pow_add]
          _ = 148241324 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 191238161) ^ 11672 = 3893419 := by
        calc
          (3 : ZMod 191238161) ^ 11672 = (3 : ZMod 191238161) ^ (5836 + 5836) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 5836 * (3 : ZMod 191238161) ^ 5836 := by rw [pow_add]
          _ = 3893419 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 191238161) ^ 23344 = 27439735 := by
        calc
          (3 : ZMod 191238161) ^ 23344 = (3 : ZMod 191238161) ^ (11672 + 11672) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 11672 * (3 : ZMod 191238161) ^ 11672 := by rw [pow_add]
          _ = 27439735 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 191238161) ^ 46689 = 173670896 := by
        calc
          (3 : ZMod 191238161) ^ 46689 = (3 : ZMod 191238161) ^ (23344 + 23344 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 23344 * (3 : ZMod 191238161) ^ 23344) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 173670896 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 191238161) ^ 93378 = 129648085 := by
        calc
          (3 : ZMod 191238161) ^ 93378 = (3 : ZMod 191238161) ^ (46689 + 46689) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 46689 * (3 : ZMod 191238161) ^ 46689 := by rw [pow_add]
          _ = 129648085 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 191238161) ^ 186756 = 26206584 := by
        calc
          (3 : ZMod 191238161) ^ 186756 = (3 : ZMod 191238161) ^ (93378 + 93378) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 93378 * (3 : ZMod 191238161) ^ 93378 := by rw [pow_add]
          _ = 26206584 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 191238161) ^ 373512 = 43067001 := by
        calc
          (3 : ZMod 191238161) ^ 373512 = (3 : ZMod 191238161) ^ (186756 + 186756) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 186756 * (3 : ZMod 191238161) ^ 186756 := by rw [pow_add]
          _ = 43067001 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 191238161) ^ 747024 = 50851115 := by
        calc
          (3 : ZMod 191238161) ^ 747024 = (3 : ZMod 191238161) ^ (373512 + 373512) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 373512 * (3 : ZMod 191238161) ^ 373512 := by rw [pow_add]
          _ = 50851115 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 191238161) ^ 1494048 = 114588158 := by
        calc
          (3 : ZMod 191238161) ^ 1494048 = (3 : ZMod 191238161) ^ (747024 + 747024) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 747024 * (3 : ZMod 191238161) ^ 747024 := by rw [pow_add]
          _ = 114588158 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 191238161) ^ 2988096 = 161656628 := by
        calc
          (3 : ZMod 191238161) ^ 2988096 = (3 : ZMod 191238161) ^ (1494048 + 1494048) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 1494048 * (3 : ZMod 191238161) ^ 1494048 := by rw [pow_add]
          _ = 161656628 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 191238161) ^ 5976192 = 91240772 := by
        calc
          (3 : ZMod 191238161) ^ 5976192 = (3 : ZMod 191238161) ^ (2988096 + 2988096) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 2988096 * (3 : ZMod 191238161) ^ 2988096 := by rw [pow_add]
          _ = 91240772 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 191238161) ^ 11952385 = 46473459 := by
        calc
          (3 : ZMod 191238161) ^ 11952385 = (3 : ZMod 191238161) ^ (5976192 + 5976192 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 5976192 * (3 : ZMod 191238161) ^ 5976192) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 46473459 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 191238161) ^ 23904770 = 179778523 := by
        calc
          (3 : ZMod 191238161) ^ 23904770 = (3 : ZMod 191238161) ^ (11952385 + 11952385) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 11952385 * (3 : ZMod 191238161) ^ 11952385 := by rw [pow_add]
          _ = 179778523 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 191238161) ^ 47809540 = 57932344 := by
        calc
          (3 : ZMod 191238161) ^ 47809540 = (3 : ZMod 191238161) ^ (23904770 + 23904770) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 23904770 * (3 : ZMod 191238161) ^ 23904770 := by rw [pow_add]
          _ = 57932344 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 191238161) ^ 95619080 = 191238160 := by
        calc
          (3 : ZMod 191238161) ^ 95619080 = (3 : ZMod 191238161) ^ (47809540 + 47809540) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 47809540 * (3 : ZMod 191238161) ^ 47809540 := by rw [pow_add]
          _ = 191238160 := by rw [factor_0_25]; decide
      change (3 : ZMod 191238161) ^ 95619080 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (3 : ZMod 191238161) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 191238161) ^ 2 = 9 := by
        calc
          (3 : ZMod 191238161) ^ 2 = (3 : ZMod 191238161) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 1 * (3 : ZMod 191238161) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 191238161) ^ 4 = 81 := by
        calc
          (3 : ZMod 191238161) ^ 4 = (3 : ZMod 191238161) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 2 * (3 : ZMod 191238161) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 191238161) ^ 9 = 19683 := by
        calc
          (3 : ZMod 191238161) ^ 9 = (3 : ZMod 191238161) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 4 * (3 : ZMod 191238161) ^ 4) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 191238161) ^ 18 = 4944167 := by
        calc
          (3 : ZMod 191238161) ^ 18 = (3 : ZMod 191238161) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 9 * (3 : ZMod 191238161) ^ 9 := by rw [pow_add]
          _ = 4944167 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 191238161) ^ 36 = 151870386 := by
        calc
          (3 : ZMod 191238161) ^ 36 = (3 : ZMod 191238161) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 18 * (3 : ZMod 191238161) ^ 18 := by rw [pow_add]
          _ = 151870386 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 191238161) ^ 72 = 113411441 := by
        calc
          (3 : ZMod 191238161) ^ 72 = (3 : ZMod 191238161) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 36 * (3 : ZMod 191238161) ^ 36 := by rw [pow_add]
          _ = 113411441 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 191238161) ^ 145 = 126478380 := by
        calc
          (3 : ZMod 191238161) ^ 145 = (3 : ZMod 191238161) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 72 * (3 : ZMod 191238161) ^ 72) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 126478380 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 191238161) ^ 291 = 42671614 := by
        calc
          (3 : ZMod 191238161) ^ 291 = (3 : ZMod 191238161) ^ (145 + 145 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 145 * (3 : ZMod 191238161) ^ 145) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 42671614 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 191238161) ^ 583 = 40313486 := by
        calc
          (3 : ZMod 191238161) ^ 583 = (3 : ZMod 191238161) ^ (291 + 291 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 291 * (3 : ZMod 191238161) ^ 291) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 40313486 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 191238161) ^ 1167 = 29179555 := by
        calc
          (3 : ZMod 191238161) ^ 1167 = (3 : ZMod 191238161) ^ (583 + 583 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 583 * (3 : ZMod 191238161) ^ 583) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 29179555 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 191238161) ^ 2334 = 16826462 := by
        calc
          (3 : ZMod 191238161) ^ 2334 = (3 : ZMod 191238161) ^ (1167 + 1167) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 1167 * (3 : ZMod 191238161) ^ 1167 := by rw [pow_add]
          _ = 16826462 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 191238161) ^ 4668 = 4933495 := by
        calc
          (3 : ZMod 191238161) ^ 4668 = (3 : ZMod 191238161) ^ (2334 + 2334) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 2334 * (3 : ZMod 191238161) ^ 2334 := by rw [pow_add]
          _ = 4933495 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 191238161) ^ 9337 = 137826538 := by
        calc
          (3 : ZMod 191238161) ^ 9337 = (3 : ZMod 191238161) ^ (4668 + 4668 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 4668 * (3 : ZMod 191238161) ^ 4668) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 137826538 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 191238161) ^ 18675 = 64228270 := by
        calc
          (3 : ZMod 191238161) ^ 18675 = (3 : ZMod 191238161) ^ (9337 + 9337 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 9337 * (3 : ZMod 191238161) ^ 9337) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 64228270 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 191238161) ^ 37351 = 24711126 := by
        calc
          (3 : ZMod 191238161) ^ 37351 = (3 : ZMod 191238161) ^ (18675 + 18675 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 18675 * (3 : ZMod 191238161) ^ 18675) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 24711126 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 191238161) ^ 74702 = 44871191 := by
        calc
          (3 : ZMod 191238161) ^ 74702 = (3 : ZMod 191238161) ^ (37351 + 37351) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 37351 * (3 : ZMod 191238161) ^ 37351 := by rw [pow_add]
          _ = 44871191 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 191238161) ^ 149404 = 150727004 := by
        calc
          (3 : ZMod 191238161) ^ 149404 = (3 : ZMod 191238161) ^ (74702 + 74702) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 74702 * (3 : ZMod 191238161) ^ 74702 := by rw [pow_add]
          _ = 150727004 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 191238161) ^ 298809 = 72907484 := by
        calc
          (3 : ZMod 191238161) ^ 298809 = (3 : ZMod 191238161) ^ (149404 + 149404 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 149404 * (3 : ZMod 191238161) ^ 149404) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 72907484 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 191238161) ^ 597619 = 35179515 := by
        calc
          (3 : ZMod 191238161) ^ 597619 = (3 : ZMod 191238161) ^ (298809 + 298809 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 298809 * (3 : ZMod 191238161) ^ 298809) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 35179515 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 191238161) ^ 1195238 = 134247403 := by
        calc
          (3 : ZMod 191238161) ^ 1195238 = (3 : ZMod 191238161) ^ (597619 + 597619) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 597619 * (3 : ZMod 191238161) ^ 597619 := by rw [pow_add]
          _ = 134247403 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 191238161) ^ 2390477 = 77586918 := by
        calc
          (3 : ZMod 191238161) ^ 2390477 = (3 : ZMod 191238161) ^ (1195238 + 1195238 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 1195238 * (3 : ZMod 191238161) ^ 1195238) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 77586918 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 191238161) ^ 4780954 = 33755464 := by
        calc
          (3 : ZMod 191238161) ^ 4780954 = (3 : ZMod 191238161) ^ (2390477 + 2390477) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 2390477 * (3 : ZMod 191238161) ^ 2390477 := by rw [pow_add]
          _ = 33755464 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 191238161) ^ 9561908 = 154986477 := by
        calc
          (3 : ZMod 191238161) ^ 9561908 = (3 : ZMod 191238161) ^ (4780954 + 4780954) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 4780954 * (3 : ZMod 191238161) ^ 4780954 := by rw [pow_add]
          _ = 154986477 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 191238161) ^ 19123816 = 157683398 := by
        calc
          (3 : ZMod 191238161) ^ 19123816 = (3 : ZMod 191238161) ^ (9561908 + 9561908) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 9561908 * (3 : ZMod 191238161) ^ 9561908 := by rw [pow_add]
          _ = 157683398 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 191238161) ^ 38247632 = 180048551 := by
        calc
          (3 : ZMod 191238161) ^ 38247632 = (3 : ZMod 191238161) ^ (19123816 + 19123816) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 19123816 * (3 : ZMod 191238161) ^ 19123816 := by rw [pow_add]
          _ = 180048551 := by rw [factor_1_24]; decide
      change (3 : ZMod 191238161) ^ 38247632 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (3 : ZMod 191238161) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 191238161) ^ 2 = 9 := by
        calc
          (3 : ZMod 191238161) ^ 2 = (3 : ZMod 191238161) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 1 * (3 : ZMod 191238161) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 191238161) ^ 5 = 243 := by
        calc
          (3 : ZMod 191238161) ^ 5 = (3 : ZMod 191238161) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = ((3 : ZMod 191238161) ^ 2 * (3 : ZMod 191238161) ^ 2) * (3 : ZMod 191238161) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 191238161) ^ 10 = 59049 := by
        calc
          (3 : ZMod 191238161) ^ 10 = (3 : ZMod 191238161) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 5 * (3 : ZMod 191238161) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 191238161) ^ 20 = 44497503 := by
        calc
          (3 : ZMod 191238161) ^ 20 = (3 : ZMod 191238161) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 10 * (3 : ZMod 191238161) ^ 10 := by rw [pow_add]
          _ = 44497503 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 191238161) ^ 40 = 62258962 := by
        calc
          (3 : ZMod 191238161) ^ 40 = (3 : ZMod 191238161) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 20 * (3 : ZMod 191238161) ^ 20 := by rw [pow_add]
          _ = 62258962 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 191238161) ^ 80 = 176018111 := by
        calc
          (3 : ZMod 191238161) ^ 80 = (3 : ZMod 191238161) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 191238161) ^ n) (by norm_num)
          _ = (3 : ZMod 191238161) ^ 40 * (3 : ZMod 191238161) ^ 40 := by rw [pow_add]
          _ = 176018111 := by rw [factor_2_5]; decide
      change (3 : ZMod 191238161) ^ 80 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_191238161

end TotientTailPeriodKiller
end Erdos249257
