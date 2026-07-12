import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_95930590621 : Nat.Prime 95930590621 := by
  apply lucas_primality 95930590621 (7 : ZMod 95930590621)
  ·
      have fermat_0 : (7 : ZMod 95930590621) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 95930590621) ^ 2 = 49 := by
        calc
          (7 : ZMod 95930590621) ^ 2 = (7 : ZMod 95930590621) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1 * (7 : ZMod 95930590621) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 95930590621) ^ 5 = 16807 := by
        calc
          (7 : ZMod 95930590621) ^ 5 = (7 : ZMod 95930590621) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 2 * (7 : ZMod 95930590621) ^ 2) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 95930590621) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 95930590621) ^ 11 = (7 : ZMod 95930590621) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 5 * (7 : ZMod 95930590621) ^ 5) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 95930590621) ^ 22 = 30678733879 := by
        calc
          (7 : ZMod 95930590621) ^ 22 = (7 : ZMod 95930590621) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 11 * (7 : ZMod 95930590621) ^ 11 := by rw [pow_add]
          _ = 30678733879 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 95930590621) ^ 44 = 93316343714 := by
        calc
          (7 : ZMod 95930590621) ^ 44 = (7 : ZMod 95930590621) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 22 * (7 : ZMod 95930590621) ^ 22 := by rw [pow_add]
          _ = 93316343714 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 95930590621) ^ 89 = 2915123721 := by
        calc
          (7 : ZMod 95930590621) ^ 89 = (7 : ZMod 95930590621) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 44 * (7 : ZMod 95930590621) ^ 44) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 2915123721 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 95930590621) ^ 178 = 75446632500 := by
        calc
          (7 : ZMod 95930590621) ^ 178 = (7 : ZMod 95930590621) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 89 * (7 : ZMod 95930590621) ^ 89 := by rw [pow_add]
          _ = 75446632500 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 95930590621) ^ 357 = 5792021931 := by
        calc
          (7 : ZMod 95930590621) ^ 357 = (7 : ZMod 95930590621) ^ (178 + 178 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 178 * (7 : ZMod 95930590621) ^ 178) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 5792021931 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 95930590621) ^ 714 = 56235996506 := by
        calc
          (7 : ZMod 95930590621) ^ 714 = (7 : ZMod 95930590621) ^ (357 + 357) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 357 * (7 : ZMod 95930590621) ^ 357 := by rw [pow_add]
          _ = 56235996506 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 95930590621) ^ 1429 = 30787640338 := by
        calc
          (7 : ZMod 95930590621) ^ 1429 = (7 : ZMod 95930590621) ^ (714 + 714 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 714 * (7 : ZMod 95930590621) ^ 714) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 30787640338 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 95930590621) ^ 2858 = 6515886470 := by
        calc
          (7 : ZMod 95930590621) ^ 2858 = (7 : ZMod 95930590621) ^ (1429 + 1429) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1429 * (7 : ZMod 95930590621) ^ 1429 := by rw [pow_add]
          _ = 6515886470 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 95930590621) ^ 5717 = 20721428129 := by
        calc
          (7 : ZMod 95930590621) ^ 5717 = (7 : ZMod 95930590621) ^ (2858 + 2858 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 2858 * (7 : ZMod 95930590621) ^ 2858) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 20721428129 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 95930590621) ^ 11435 = 87124831625 := by
        calc
          (7 : ZMod 95930590621) ^ 11435 = (7 : ZMod 95930590621) ^ (5717 + 5717 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 5717 * (7 : ZMod 95930590621) ^ 5717) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 87124831625 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 95930590621) ^ 22871 = 77208098992 := by
        calc
          (7 : ZMod 95930590621) ^ 22871 = (7 : ZMod 95930590621) ^ (11435 + 11435 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 11435 * (7 : ZMod 95930590621) ^ 11435) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 77208098992 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 95930590621) ^ 45743 = 60329242957 := by
        calc
          (7 : ZMod 95930590621) ^ 45743 = (7 : ZMod 95930590621) ^ (22871 + 22871 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 22871 * (7 : ZMod 95930590621) ^ 22871) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 60329242957 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 95930590621) ^ 91486 = 4992435329 := by
        calc
          (7 : ZMod 95930590621) ^ 91486 = (7 : ZMod 95930590621) ^ (45743 + 45743) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 45743 * (7 : ZMod 95930590621) ^ 45743 := by rw [pow_add]
          _ = 4992435329 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 95930590621) ^ 182973 = 90079444134 := by
        calc
          (7 : ZMod 95930590621) ^ 182973 = (7 : ZMod 95930590621) ^ (91486 + 91486 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 91486 * (7 : ZMod 95930590621) ^ 91486) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 90079444134 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 95930590621) ^ 365946 = 68531897882 := by
        calc
          (7 : ZMod 95930590621) ^ 365946 = (7 : ZMod 95930590621) ^ (182973 + 182973) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 182973 * (7 : ZMod 95930590621) ^ 182973 := by rw [pow_add]
          _ = 68531897882 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 95930590621) ^ 731892 = 6586669620 := by
        calc
          (7 : ZMod 95930590621) ^ 731892 = (7 : ZMod 95930590621) ^ (365946 + 365946) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 365946 * (7 : ZMod 95930590621) ^ 365946 := by rw [pow_add]
          _ = 6586669620 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 95930590621) ^ 1463784 = 6382878016 := by
        calc
          (7 : ZMod 95930590621) ^ 1463784 = (7 : ZMod 95930590621) ^ (731892 + 731892) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 731892 * (7 : ZMod 95930590621) ^ 731892 := by rw [pow_add]
          _ = 6382878016 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 95930590621) ^ 2927569 = 92152732810 := by
        calc
          (7 : ZMod 95930590621) ^ 2927569 = (7 : ZMod 95930590621) ^ (1463784 + 1463784 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 1463784 * (7 : ZMod 95930590621) ^ 1463784) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 92152732810 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 95930590621) ^ 5855138 = 86847526764 := by
        calc
          (7 : ZMod 95930590621) ^ 5855138 = (7 : ZMod 95930590621) ^ (2927569 + 2927569) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 2927569 * (7 : ZMod 95930590621) ^ 2927569 := by rw [pow_add]
          _ = 86847526764 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 95930590621) ^ 11710277 = 76141979577 := by
        calc
          (7 : ZMod 95930590621) ^ 11710277 = (7 : ZMod 95930590621) ^ (5855138 + 5855138 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 5855138 * (7 : ZMod 95930590621) ^ 5855138) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 76141979577 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 95930590621) ^ 23420554 = 81768957702 := by
        calc
          (7 : ZMod 95930590621) ^ 23420554 = (7 : ZMod 95930590621) ^ (11710277 + 11710277) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 11710277 * (7 : ZMod 95930590621) ^ 11710277 := by rw [pow_add]
          _ = 81768957702 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 95930590621) ^ 46841108 = 80908511754 := by
        calc
          (7 : ZMod 95930590621) ^ 46841108 = (7 : ZMod 95930590621) ^ (23420554 + 23420554) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 23420554 * (7 : ZMod 95930590621) ^ 23420554 := by rw [pow_add]
          _ = 80908511754 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 95930590621) ^ 93682217 = 46807961369 := by
        calc
          (7 : ZMod 95930590621) ^ 93682217 = (7 : ZMod 95930590621) ^ (46841108 + 46841108 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 46841108 * (7 : ZMod 95930590621) ^ 46841108) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 46807961369 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 95930590621) ^ 187364434 = 70025674262 := by
        calc
          (7 : ZMod 95930590621) ^ 187364434 = (7 : ZMod 95930590621) ^ (93682217 + 93682217) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 93682217 * (7 : ZMod 95930590621) ^ 93682217 := by rw [pow_add]
          _ = 70025674262 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 95930590621) ^ 374728869 = 89520154589 := by
        calc
          (7 : ZMod 95930590621) ^ 374728869 = (7 : ZMod 95930590621) ^ (187364434 + 187364434 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 187364434 * (7 : ZMod 95930590621) ^ 187364434) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 89520154589 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 95930590621) ^ 749457739 = 13112769985 := by
        calc
          (7 : ZMod 95930590621) ^ 749457739 = (7 : ZMod 95930590621) ^ (374728869 + 374728869 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 374728869 * (7 : ZMod 95930590621) ^ 374728869) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 13112769985 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 95930590621) ^ 1498915478 = 55117097937 := by
        calc
          (7 : ZMod 95930590621) ^ 1498915478 = (7 : ZMod 95930590621) ^ (749457739 + 749457739) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 749457739 * (7 : ZMod 95930590621) ^ 749457739 := by rw [pow_add]
          _ = 55117097937 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 95930590621) ^ 2997830956 = 35232896199 := by
        calc
          (7 : ZMod 95930590621) ^ 2997830956 = (7 : ZMod 95930590621) ^ (1498915478 + 1498915478) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1498915478 * (7 : ZMod 95930590621) ^ 1498915478 := by rw [pow_add]
          _ = 35232896199 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 95930590621) ^ 5995661913 = 47995724879 := by
        calc
          (7 : ZMod 95930590621) ^ 5995661913 = (7 : ZMod 95930590621) ^ (2997830956 + 2997830956 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 2997830956 * (7 : ZMod 95930590621) ^ 2997830956) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 47995724879 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 95930590621) ^ 11991323827 = 88170422515 := by
        calc
          (7 : ZMod 95930590621) ^ 11991323827 = (7 : ZMod 95930590621) ^ (5995661913 + 5995661913 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 5995661913 * (7 : ZMod 95930590621) ^ 5995661913) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 88170422515 := by rw [fermat_32]; decide
      have fermat_34 : (7 : ZMod 95930590621) ^ 23982647655 = 94916895410 := by
        calc
          (7 : ZMod 95930590621) ^ 23982647655 = (7 : ZMod 95930590621) ^ (11991323827 + 11991323827 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 11991323827 * (7 : ZMod 95930590621) ^ 11991323827) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 94916895410 := by rw [fermat_33]; decide
      have fermat_35 : (7 : ZMod 95930590621) ^ 47965295310 = 95930590620 := by
        calc
          (7 : ZMod 95930590621) ^ 47965295310 = (7 : ZMod 95930590621) ^ (23982647655 + 23982647655) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 23982647655 * (7 : ZMod 95930590621) ^ 23982647655 := by rw [pow_add]
          _ = 95930590620 := by rw [fermat_34]; decide
      have fermat_36 : (7 : ZMod 95930590621) ^ 95930590620 = 1 := by
        calc
          (7 : ZMod 95930590621) ^ 95930590620 = (7 : ZMod 95930590621) ^ (47965295310 + 47965295310) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 47965295310 * (7 : ZMod 95930590621) ^ 47965295310 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (67, 1), (23863331, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (67, 1), (23863331, 1)] : List FactorBlock).map factorBlockValue).prod = 95930590621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 95930590621) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 95930590621) ^ 2 = 49 := by
        calc
          (7 : ZMod 95930590621) ^ 2 = (7 : ZMod 95930590621) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1 * (7 : ZMod 95930590621) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 95930590621) ^ 5 = 16807 := by
        calc
          (7 : ZMod 95930590621) ^ 5 = (7 : ZMod 95930590621) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 2 * (7 : ZMod 95930590621) ^ 2) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 95930590621) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 95930590621) ^ 11 = (7 : ZMod 95930590621) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 5 * (7 : ZMod 95930590621) ^ 5) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 95930590621) ^ 22 = 30678733879 := by
        calc
          (7 : ZMod 95930590621) ^ 22 = (7 : ZMod 95930590621) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 11 * (7 : ZMod 95930590621) ^ 11 := by rw [pow_add]
          _ = 30678733879 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 95930590621) ^ 44 = 93316343714 := by
        calc
          (7 : ZMod 95930590621) ^ 44 = (7 : ZMod 95930590621) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 22 * (7 : ZMod 95930590621) ^ 22 := by rw [pow_add]
          _ = 93316343714 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 95930590621) ^ 89 = 2915123721 := by
        calc
          (7 : ZMod 95930590621) ^ 89 = (7 : ZMod 95930590621) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 44 * (7 : ZMod 95930590621) ^ 44) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 2915123721 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 95930590621) ^ 178 = 75446632500 := by
        calc
          (7 : ZMod 95930590621) ^ 178 = (7 : ZMod 95930590621) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 89 * (7 : ZMod 95930590621) ^ 89 := by rw [pow_add]
          _ = 75446632500 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 95930590621) ^ 357 = 5792021931 := by
        calc
          (7 : ZMod 95930590621) ^ 357 = (7 : ZMod 95930590621) ^ (178 + 178 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 178 * (7 : ZMod 95930590621) ^ 178) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 5792021931 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 95930590621) ^ 714 = 56235996506 := by
        calc
          (7 : ZMod 95930590621) ^ 714 = (7 : ZMod 95930590621) ^ (357 + 357) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 357 * (7 : ZMod 95930590621) ^ 357 := by rw [pow_add]
          _ = 56235996506 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 95930590621) ^ 1429 = 30787640338 := by
        calc
          (7 : ZMod 95930590621) ^ 1429 = (7 : ZMod 95930590621) ^ (714 + 714 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 714 * (7 : ZMod 95930590621) ^ 714) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 30787640338 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 95930590621) ^ 2858 = 6515886470 := by
        calc
          (7 : ZMod 95930590621) ^ 2858 = (7 : ZMod 95930590621) ^ (1429 + 1429) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1429 * (7 : ZMod 95930590621) ^ 1429 := by rw [pow_add]
          _ = 6515886470 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 95930590621) ^ 5717 = 20721428129 := by
        calc
          (7 : ZMod 95930590621) ^ 5717 = (7 : ZMod 95930590621) ^ (2858 + 2858 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 2858 * (7 : ZMod 95930590621) ^ 2858) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 20721428129 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 95930590621) ^ 11435 = 87124831625 := by
        calc
          (7 : ZMod 95930590621) ^ 11435 = (7 : ZMod 95930590621) ^ (5717 + 5717 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 5717 * (7 : ZMod 95930590621) ^ 5717) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 87124831625 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 95930590621) ^ 22871 = 77208098992 := by
        calc
          (7 : ZMod 95930590621) ^ 22871 = (7 : ZMod 95930590621) ^ (11435 + 11435 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 11435 * (7 : ZMod 95930590621) ^ 11435) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 77208098992 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 95930590621) ^ 45743 = 60329242957 := by
        calc
          (7 : ZMod 95930590621) ^ 45743 = (7 : ZMod 95930590621) ^ (22871 + 22871 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 22871 * (7 : ZMod 95930590621) ^ 22871) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 60329242957 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 95930590621) ^ 91486 = 4992435329 := by
        calc
          (7 : ZMod 95930590621) ^ 91486 = (7 : ZMod 95930590621) ^ (45743 + 45743) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 45743 * (7 : ZMod 95930590621) ^ 45743 := by rw [pow_add]
          _ = 4992435329 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 95930590621) ^ 182973 = 90079444134 := by
        calc
          (7 : ZMod 95930590621) ^ 182973 = (7 : ZMod 95930590621) ^ (91486 + 91486 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 91486 * (7 : ZMod 95930590621) ^ 91486) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 90079444134 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 95930590621) ^ 365946 = 68531897882 := by
        calc
          (7 : ZMod 95930590621) ^ 365946 = (7 : ZMod 95930590621) ^ (182973 + 182973) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 182973 * (7 : ZMod 95930590621) ^ 182973 := by rw [pow_add]
          _ = 68531897882 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 95930590621) ^ 731892 = 6586669620 := by
        calc
          (7 : ZMod 95930590621) ^ 731892 = (7 : ZMod 95930590621) ^ (365946 + 365946) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 365946 * (7 : ZMod 95930590621) ^ 365946 := by rw [pow_add]
          _ = 6586669620 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 95930590621) ^ 1463784 = 6382878016 := by
        calc
          (7 : ZMod 95930590621) ^ 1463784 = (7 : ZMod 95930590621) ^ (731892 + 731892) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 731892 * (7 : ZMod 95930590621) ^ 731892 := by rw [pow_add]
          _ = 6382878016 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 95930590621) ^ 2927569 = 92152732810 := by
        calc
          (7 : ZMod 95930590621) ^ 2927569 = (7 : ZMod 95930590621) ^ (1463784 + 1463784 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 1463784 * (7 : ZMod 95930590621) ^ 1463784) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 92152732810 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 95930590621) ^ 5855138 = 86847526764 := by
        calc
          (7 : ZMod 95930590621) ^ 5855138 = (7 : ZMod 95930590621) ^ (2927569 + 2927569) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 2927569 * (7 : ZMod 95930590621) ^ 2927569 := by rw [pow_add]
          _ = 86847526764 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 95930590621) ^ 11710277 = 76141979577 := by
        calc
          (7 : ZMod 95930590621) ^ 11710277 = (7 : ZMod 95930590621) ^ (5855138 + 5855138 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 5855138 * (7 : ZMod 95930590621) ^ 5855138) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 76141979577 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 95930590621) ^ 23420554 = 81768957702 := by
        calc
          (7 : ZMod 95930590621) ^ 23420554 = (7 : ZMod 95930590621) ^ (11710277 + 11710277) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 11710277 * (7 : ZMod 95930590621) ^ 11710277 := by rw [pow_add]
          _ = 81768957702 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 95930590621) ^ 46841108 = 80908511754 := by
        calc
          (7 : ZMod 95930590621) ^ 46841108 = (7 : ZMod 95930590621) ^ (23420554 + 23420554) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 23420554 * (7 : ZMod 95930590621) ^ 23420554 := by rw [pow_add]
          _ = 80908511754 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 95930590621) ^ 93682217 = 46807961369 := by
        calc
          (7 : ZMod 95930590621) ^ 93682217 = (7 : ZMod 95930590621) ^ (46841108 + 46841108 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 46841108 * (7 : ZMod 95930590621) ^ 46841108) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 46807961369 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 95930590621) ^ 187364434 = 70025674262 := by
        calc
          (7 : ZMod 95930590621) ^ 187364434 = (7 : ZMod 95930590621) ^ (93682217 + 93682217) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 93682217 * (7 : ZMod 95930590621) ^ 93682217 := by rw [pow_add]
          _ = 70025674262 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 95930590621) ^ 374728869 = 89520154589 := by
        calc
          (7 : ZMod 95930590621) ^ 374728869 = (7 : ZMod 95930590621) ^ (187364434 + 187364434 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 187364434 * (7 : ZMod 95930590621) ^ 187364434) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 89520154589 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 95930590621) ^ 749457739 = 13112769985 := by
        calc
          (7 : ZMod 95930590621) ^ 749457739 = (7 : ZMod 95930590621) ^ (374728869 + 374728869 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 374728869 * (7 : ZMod 95930590621) ^ 374728869) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 13112769985 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 95930590621) ^ 1498915478 = 55117097937 := by
        calc
          (7 : ZMod 95930590621) ^ 1498915478 = (7 : ZMod 95930590621) ^ (749457739 + 749457739) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 749457739 * (7 : ZMod 95930590621) ^ 749457739 := by rw [pow_add]
          _ = 55117097937 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 95930590621) ^ 2997830956 = 35232896199 := by
        calc
          (7 : ZMod 95930590621) ^ 2997830956 = (7 : ZMod 95930590621) ^ (1498915478 + 1498915478) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1498915478 * (7 : ZMod 95930590621) ^ 1498915478 := by rw [pow_add]
          _ = 35232896199 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 95930590621) ^ 5995661913 = 47995724879 := by
        calc
          (7 : ZMod 95930590621) ^ 5995661913 = (7 : ZMod 95930590621) ^ (2997830956 + 2997830956 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 2997830956 * (7 : ZMod 95930590621) ^ 2997830956) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 47995724879 := by rw [factor_0_31]; decide
      have factor_0_33 : (7 : ZMod 95930590621) ^ 11991323827 = 88170422515 := by
        calc
          (7 : ZMod 95930590621) ^ 11991323827 = (7 : ZMod 95930590621) ^ (5995661913 + 5995661913 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 5995661913 * (7 : ZMod 95930590621) ^ 5995661913) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 88170422515 := by rw [factor_0_32]; decide
      have factor_0_34 : (7 : ZMod 95930590621) ^ 23982647655 = 94916895410 := by
        calc
          (7 : ZMod 95930590621) ^ 23982647655 = (7 : ZMod 95930590621) ^ (11991323827 + 11991323827 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 11991323827 * (7 : ZMod 95930590621) ^ 11991323827) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 94916895410 := by rw [factor_0_33]; decide
      have factor_0_35 : (7 : ZMod 95930590621) ^ 47965295310 = 95930590620 := by
        calc
          (7 : ZMod 95930590621) ^ 47965295310 = (7 : ZMod 95930590621) ^ (23982647655 + 23982647655) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 23982647655 * (7 : ZMod 95930590621) ^ 23982647655 := by rw [pow_add]
          _ = 95930590620 := by rw [factor_0_34]; decide
      change (7 : ZMod 95930590621) ^ 47965295310 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (7 : ZMod 95930590621) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 95930590621) ^ 3 = 343 := by
        calc
          (7 : ZMod 95930590621) ^ 3 = (7 : ZMod 95930590621) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 1 * (7 : ZMod 95930590621) ^ 1) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 95930590621) ^ 7 = 823543 := by
        calc
          (7 : ZMod 95930590621) ^ 7 = (7 : ZMod 95930590621) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 3 * (7 : ZMod 95930590621) ^ 3) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 95930590621) ^ 14 = 6708938502 := by
        calc
          (7 : ZMod 95930590621) ^ 14 = (7 : ZMod 95930590621) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 7 * (7 : ZMod 95930590621) ^ 7 := by rw [pow_add]
          _ = 6708938502 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 95930590621) ^ 29 = 16883060527 := by
        calc
          (7 : ZMod 95930590621) ^ 29 = (7 : ZMod 95930590621) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 14 * (7 : ZMod 95930590621) ^ 14) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 16883060527 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 95930590621) ^ 59 = 17568097132 := by
        calc
          (7 : ZMod 95930590621) ^ 59 = (7 : ZMod 95930590621) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 29 * (7 : ZMod 95930590621) ^ 29) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 17568097132 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 95930590621) ^ 119 = 54702062808 := by
        calc
          (7 : ZMod 95930590621) ^ 119 = (7 : ZMod 95930590621) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 59 * (7 : ZMod 95930590621) ^ 59) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 54702062808 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 95930590621) ^ 238 = 63165665821 := by
        calc
          (7 : ZMod 95930590621) ^ 238 = (7 : ZMod 95930590621) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 119 * (7 : ZMod 95930590621) ^ 119 := by rw [pow_add]
          _ = 63165665821 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 95930590621) ^ 476 = 60398653281 := by
        calc
          (7 : ZMod 95930590621) ^ 476 = (7 : ZMod 95930590621) ^ (238 + 238) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 238 * (7 : ZMod 95930590621) ^ 238 := by rw [pow_add]
          _ = 60398653281 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 95930590621) ^ 952 = 62939268333 := by
        calc
          (7 : ZMod 95930590621) ^ 952 = (7 : ZMod 95930590621) ^ (476 + 476) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 476 * (7 : ZMod 95930590621) ^ 476 := by rw [pow_add]
          _ = 62939268333 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 95930590621) ^ 1905 = 77807390860 := by
        calc
          (7 : ZMod 95930590621) ^ 1905 = (7 : ZMod 95930590621) ^ (952 + 952 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 952 * (7 : ZMod 95930590621) ^ 952) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 77807390860 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 95930590621) ^ 3811 = 57625787767 := by
        calc
          (7 : ZMod 95930590621) ^ 3811 = (7 : ZMod 95930590621) ^ (1905 + 1905 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 1905 * (7 : ZMod 95930590621) ^ 1905) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 57625787767 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 95930590621) ^ 7623 = 2045926154 := by
        calc
          (7 : ZMod 95930590621) ^ 7623 = (7 : ZMod 95930590621) ^ (3811 + 3811 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 3811 * (7 : ZMod 95930590621) ^ 3811) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 2045926154 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 95930590621) ^ 15247 = 50001261466 := by
        calc
          (7 : ZMod 95930590621) ^ 15247 = (7 : ZMod 95930590621) ^ (7623 + 7623 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 7623 * (7 : ZMod 95930590621) ^ 7623) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 50001261466 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 95930590621) ^ 30495 = 1912328149 := by
        calc
          (7 : ZMod 95930590621) ^ 30495 = (7 : ZMod 95930590621) ^ (15247 + 15247 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 15247 * (7 : ZMod 95930590621) ^ 15247) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 1912328149 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 95930590621) ^ 60991 = 13146756718 := by
        calc
          (7 : ZMod 95930590621) ^ 60991 = (7 : ZMod 95930590621) ^ (30495 + 30495 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 30495 * (7 : ZMod 95930590621) ^ 30495) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 13146756718 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 95930590621) ^ 121982 = 5416220749 := by
        calc
          (7 : ZMod 95930590621) ^ 121982 = (7 : ZMod 95930590621) ^ (60991 + 60991) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 60991 * (7 : ZMod 95930590621) ^ 60991 := by rw [pow_add]
          _ = 5416220749 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 95930590621) ^ 243964 = 81751256310 := by
        calc
          (7 : ZMod 95930590621) ^ 243964 = (7 : ZMod 95930590621) ^ (121982 + 121982) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 121982 * (7 : ZMod 95930590621) ^ 121982 := by rw [pow_add]
          _ = 81751256310 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 95930590621) ^ 487928 = 63879120396 := by
        calc
          (7 : ZMod 95930590621) ^ 487928 = (7 : ZMod 95930590621) ^ (243964 + 243964) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 243964 * (7 : ZMod 95930590621) ^ 243964 := by rw [pow_add]
          _ = 63879120396 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 95930590621) ^ 975856 = 93985848800 := by
        calc
          (7 : ZMod 95930590621) ^ 975856 = (7 : ZMod 95930590621) ^ (487928 + 487928) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 487928 * (7 : ZMod 95930590621) ^ 487928 := by rw [pow_add]
          _ = 93985848800 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 95930590621) ^ 1951712 = 156888007 := by
        calc
          (7 : ZMod 95930590621) ^ 1951712 = (7 : ZMod 95930590621) ^ (975856 + 975856) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 975856 * (7 : ZMod 95930590621) ^ 975856 := by rw [pow_add]
          _ = 156888007 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 95930590621) ^ 3903425 = 22453452325 := by
        calc
          (7 : ZMod 95930590621) ^ 3903425 = (7 : ZMod 95930590621) ^ (1951712 + 1951712 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 1951712 * (7 : ZMod 95930590621) ^ 1951712) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 22453452325 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 95930590621) ^ 7806851 = 27172245093 := by
        calc
          (7 : ZMod 95930590621) ^ 7806851 = (7 : ZMod 95930590621) ^ (3903425 + 3903425 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 3903425 * (7 : ZMod 95930590621) ^ 3903425) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 27172245093 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 95930590621) ^ 15613702 = 76546056291 := by
        calc
          (7 : ZMod 95930590621) ^ 15613702 = (7 : ZMod 95930590621) ^ (7806851 + 7806851) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 7806851 * (7 : ZMod 95930590621) ^ 7806851 := by rw [pow_add]
          _ = 76546056291 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 95930590621) ^ 31227405 = 69124299978 := by
        calc
          (7 : ZMod 95930590621) ^ 31227405 = (7 : ZMod 95930590621) ^ (15613702 + 15613702 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 15613702 * (7 : ZMod 95930590621) ^ 15613702) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 69124299978 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 95930590621) ^ 62454811 = 16877473066 := by
        calc
          (7 : ZMod 95930590621) ^ 62454811 = (7 : ZMod 95930590621) ^ (31227405 + 31227405 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 31227405 * (7 : ZMod 95930590621) ^ 31227405) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 16877473066 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 95930590621) ^ 124909623 = 25200634477 := by
        calc
          (7 : ZMod 95930590621) ^ 124909623 = (7 : ZMod 95930590621) ^ (62454811 + 62454811 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 62454811 * (7 : ZMod 95930590621) ^ 62454811) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 25200634477 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 95930590621) ^ 249819246 = 13954685463 := by
        calc
          (7 : ZMod 95930590621) ^ 249819246 = (7 : ZMod 95930590621) ^ (124909623 + 124909623) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 124909623 * (7 : ZMod 95930590621) ^ 124909623 := by rw [pow_add]
          _ = 13954685463 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 95930590621) ^ 499638492 = 40036720958 := by
        calc
          (7 : ZMod 95930590621) ^ 499638492 = (7 : ZMod 95930590621) ^ (249819246 + 249819246) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 249819246 * (7 : ZMod 95930590621) ^ 249819246 := by rw [pow_add]
          _ = 40036720958 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 95930590621) ^ 999276985 = 30013973966 := by
        calc
          (7 : ZMod 95930590621) ^ 999276985 = (7 : ZMod 95930590621) ^ (499638492 + 499638492 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 499638492 * (7 : ZMod 95930590621) ^ 499638492) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 30013973966 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 95930590621) ^ 1998553971 = 31435253520 := by
        calc
          (7 : ZMod 95930590621) ^ 1998553971 = (7 : ZMod 95930590621) ^ (999276985 + 999276985 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 999276985 * (7 : ZMod 95930590621) ^ 999276985) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 31435253520 := by rw [factor_1_29]; decide
      have factor_1_31 : (7 : ZMod 95930590621) ^ 3997107942 = 14959230843 := by
        calc
          (7 : ZMod 95930590621) ^ 3997107942 = (7 : ZMod 95930590621) ^ (1998553971 + 1998553971) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1998553971 * (7 : ZMod 95930590621) ^ 1998553971 := by rw [pow_add]
          _ = 14959230843 := by rw [factor_1_30]; decide
      have factor_1_32 : (7 : ZMod 95930590621) ^ 7994215885 = 37331516720 := by
        calc
          (7 : ZMod 95930590621) ^ 7994215885 = (7 : ZMod 95930590621) ^ (3997107942 + 3997107942 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 3997107942 * (7 : ZMod 95930590621) ^ 3997107942) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 37331516720 := by rw [factor_1_31]; decide
      have factor_1_33 : (7 : ZMod 95930590621) ^ 15988431770 = 59576592479 := by
        calc
          (7 : ZMod 95930590621) ^ 15988431770 = (7 : ZMod 95930590621) ^ (7994215885 + 7994215885) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 7994215885 * (7 : ZMod 95930590621) ^ 7994215885 := by rw [pow_add]
          _ = 59576592479 := by rw [factor_1_32]; decide
      have factor_1_34 : (7 : ZMod 95930590621) ^ 31976863540 = 59576592478 := by
        calc
          (7 : ZMod 95930590621) ^ 31976863540 = (7 : ZMod 95930590621) ^ (15988431770 + 15988431770) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 15988431770 * (7 : ZMod 95930590621) ^ 15988431770 := by rw [pow_add]
          _ = 59576592478 := by rw [factor_1_33]; decide
      change (7 : ZMod 95930590621) ^ 31976863540 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (7 : ZMod 95930590621) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 95930590621) ^ 2 = 49 := by
        calc
          (7 : ZMod 95930590621) ^ 2 = (7 : ZMod 95930590621) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1 * (7 : ZMod 95930590621) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 95930590621) ^ 4 = 2401 := by
        calc
          (7 : ZMod 95930590621) ^ 4 = (7 : ZMod 95930590621) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 2 * (7 : ZMod 95930590621) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 95930590621) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 95930590621) ^ 8 = (7 : ZMod 95930590621) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 4 * (7 : ZMod 95930590621) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 95930590621) ^ 17 = 94762321903 := by
        calc
          (7 : ZMod 95930590621) ^ 17 = (7 : ZMod 95930590621) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 8 * (7 : ZMod 95930590621) ^ 8) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 94762321903 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 95930590621) ^ 35 = 32309133218 := by
        calc
          (7 : ZMod 95930590621) ^ 35 = (7 : ZMod 95930590621) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 17 * (7 : ZMod 95930590621) ^ 17) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 32309133218 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 95930590621) ^ 71 = 69830804072 := by
        calc
          (7 : ZMod 95930590621) ^ 71 = (7 : ZMod 95930590621) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 35 * (7 : ZMod 95930590621) ^ 35) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 69830804072 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 95930590621) ^ 142 = 32935835892 := by
        calc
          (7 : ZMod 95930590621) ^ 142 = (7 : ZMod 95930590621) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 71 * (7 : ZMod 95930590621) ^ 71 := by rw [pow_add]
          _ = 32935835892 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 95930590621) ^ 285 = 77320121523 := by
        calc
          (7 : ZMod 95930590621) ^ 285 = (7 : ZMod 95930590621) ^ (142 + 142 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 142 * (7 : ZMod 95930590621) ^ 142) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 77320121523 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 95930590621) ^ 571 = 18917278918 := by
        calc
          (7 : ZMod 95930590621) ^ 571 = (7 : ZMod 95930590621) ^ (285 + 285 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 285 * (7 : ZMod 95930590621) ^ 285) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 18917278918 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 95930590621) ^ 1143 = 54680881522 := by
        calc
          (7 : ZMod 95930590621) ^ 1143 = (7 : ZMod 95930590621) ^ (571 + 571 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 571 * (7 : ZMod 95930590621) ^ 571) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 54680881522 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 95930590621) ^ 2287 = 63400630878 := by
        calc
          (7 : ZMod 95930590621) ^ 2287 = (7 : ZMod 95930590621) ^ (1143 + 1143 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 1143 * (7 : ZMod 95930590621) ^ 1143) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 63400630878 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 95930590621) ^ 4574 = 67956713630 := by
        calc
          (7 : ZMod 95930590621) ^ 4574 = (7 : ZMod 95930590621) ^ (2287 + 2287) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 2287 * (7 : ZMod 95930590621) ^ 2287 := by rw [pow_add]
          _ = 67956713630 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 95930590621) ^ 9148 = 28834303219 := by
        calc
          (7 : ZMod 95930590621) ^ 9148 = (7 : ZMod 95930590621) ^ (4574 + 4574) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 4574 * (7 : ZMod 95930590621) ^ 4574 := by rw [pow_add]
          _ = 28834303219 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 95930590621) ^ 18297 = 82231873294 := by
        calc
          (7 : ZMod 95930590621) ^ 18297 = (7 : ZMod 95930590621) ^ (9148 + 9148 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 9148 * (7 : ZMod 95930590621) ^ 9148) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 82231873294 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 95930590621) ^ 36594 = 81265706456 := by
        calc
          (7 : ZMod 95930590621) ^ 36594 = (7 : ZMod 95930590621) ^ (18297 + 18297) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 18297 * (7 : ZMod 95930590621) ^ 18297 := by rw [pow_add]
          _ = 81265706456 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 95930590621) ^ 73189 = 4091840570 := by
        calc
          (7 : ZMod 95930590621) ^ 73189 = (7 : ZMod 95930590621) ^ (36594 + 36594 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 36594 * (7 : ZMod 95930590621) ^ 36594) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 4091840570 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 95930590621) ^ 146378 = 49723839421 := by
        calc
          (7 : ZMod 95930590621) ^ 146378 = (7 : ZMod 95930590621) ^ (73189 + 73189) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 73189 * (7 : ZMod 95930590621) ^ 73189 := by rw [pow_add]
          _ = 49723839421 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 95930590621) ^ 292756 = 39880981882 := by
        calc
          (7 : ZMod 95930590621) ^ 292756 = (7 : ZMod 95930590621) ^ (146378 + 146378) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 146378 * (7 : ZMod 95930590621) ^ 146378 := by rw [pow_add]
          _ = 39880981882 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 95930590621) ^ 585513 = 72139346127 := by
        calc
          (7 : ZMod 95930590621) ^ 585513 = (7 : ZMod 95930590621) ^ (292756 + 292756 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 292756 * (7 : ZMod 95930590621) ^ 292756) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 72139346127 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 95930590621) ^ 1171027 = 57347947693 := by
        calc
          (7 : ZMod 95930590621) ^ 1171027 = (7 : ZMod 95930590621) ^ (585513 + 585513 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 585513 * (7 : ZMod 95930590621) ^ 585513) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 57347947693 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 95930590621) ^ 2342055 = 52534619600 := by
        calc
          (7 : ZMod 95930590621) ^ 2342055 = (7 : ZMod 95930590621) ^ (1171027 + 1171027 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 1171027 * (7 : ZMod 95930590621) ^ 1171027) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 52534619600 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 95930590621) ^ 4684110 = 66512583443 := by
        calc
          (7 : ZMod 95930590621) ^ 4684110 = (7 : ZMod 95930590621) ^ (2342055 + 2342055) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 2342055 * (7 : ZMod 95930590621) ^ 2342055 := by rw [pow_add]
          _ = 66512583443 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 95930590621) ^ 9368221 = 76122814396 := by
        calc
          (7 : ZMod 95930590621) ^ 9368221 = (7 : ZMod 95930590621) ^ (4684110 + 4684110 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 4684110 * (7 : ZMod 95930590621) ^ 4684110) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 76122814396 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 95930590621) ^ 18736443 = 93473263424 := by
        calc
          (7 : ZMod 95930590621) ^ 18736443 = (7 : ZMod 95930590621) ^ (9368221 + 9368221 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 9368221 * (7 : ZMod 95930590621) ^ 9368221) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 93473263424 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 95930590621) ^ 37472886 = 19104986225 := by
        calc
          (7 : ZMod 95930590621) ^ 37472886 = (7 : ZMod 95930590621) ^ (18736443 + 18736443) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 18736443 * (7 : ZMod 95930590621) ^ 18736443 := by rw [pow_add]
          _ = 19104986225 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 95930590621) ^ 74945773 = 93143909847 := by
        calc
          (7 : ZMod 95930590621) ^ 74945773 = (7 : ZMod 95930590621) ^ (37472886 + 37472886 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 37472886 * (7 : ZMod 95930590621) ^ 37472886) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 93143909847 := by rw [factor_2_25]; decide
      have factor_2_27 : (7 : ZMod 95930590621) ^ 149891547 = 76496382238 := by
        calc
          (7 : ZMod 95930590621) ^ 149891547 = (7 : ZMod 95930590621) ^ (74945773 + 74945773 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 74945773 * (7 : ZMod 95930590621) ^ 74945773) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 76496382238 := by rw [factor_2_26]; decide
      have factor_2_28 : (7 : ZMod 95930590621) ^ 299783095 = 31409431806 := by
        calc
          (7 : ZMod 95930590621) ^ 299783095 = (7 : ZMod 95930590621) ^ (149891547 + 149891547 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 149891547 * (7 : ZMod 95930590621) ^ 149891547) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 31409431806 := by rw [factor_2_27]; decide
      have factor_2_29 : (7 : ZMod 95930590621) ^ 599566191 = 67183687833 := by
        calc
          (7 : ZMod 95930590621) ^ 599566191 = (7 : ZMod 95930590621) ^ (299783095 + 299783095 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 299783095 * (7 : ZMod 95930590621) ^ 299783095) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 67183687833 := by rw [factor_2_28]; decide
      have factor_2_30 : (7 : ZMod 95930590621) ^ 1199132382 = 13798911069 := by
        calc
          (7 : ZMod 95930590621) ^ 1199132382 = (7 : ZMod 95930590621) ^ (599566191 + 599566191) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 599566191 * (7 : ZMod 95930590621) ^ 599566191 := by rw [pow_add]
          _ = 13798911069 := by rw [factor_2_29]; decide
      have factor_2_31 : (7 : ZMod 95930590621) ^ 2398264765 = 74879410698 := by
        calc
          (7 : ZMod 95930590621) ^ 2398264765 = (7 : ZMod 95930590621) ^ (1199132382 + 1199132382 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 1199132382 * (7 : ZMod 95930590621) ^ 1199132382) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 74879410698 := by rw [factor_2_30]; decide
      have factor_2_32 : (7 : ZMod 95930590621) ^ 4796529531 = 82123541856 := by
        calc
          (7 : ZMod 95930590621) ^ 4796529531 = (7 : ZMod 95930590621) ^ (2398264765 + 2398264765 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 2398264765 * (7 : ZMod 95930590621) ^ 2398264765) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 82123541856 := by rw [factor_2_31]; decide
      have factor_2_33 : (7 : ZMod 95930590621) ^ 9593059062 = 60343852384 := by
        calc
          (7 : ZMod 95930590621) ^ 9593059062 = (7 : ZMod 95930590621) ^ (4796529531 + 4796529531) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 4796529531 * (7 : ZMod 95930590621) ^ 4796529531 := by rw [pow_add]
          _ = 60343852384 := by rw [factor_2_32]; decide
      have factor_2_34 : (7 : ZMod 95930590621) ^ 19186118124 = 65311615573 := by
        calc
          (7 : ZMod 95930590621) ^ 19186118124 = (7 : ZMod 95930590621) ^ (9593059062 + 9593059062) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 9593059062 * (7 : ZMod 95930590621) ^ 9593059062 := by rw [pow_add]
          _ = 65311615573 := by rw [factor_2_33]; decide
      change (7 : ZMod 95930590621) ^ 19186118124 ≠ 1
      rw [factor_2_34]
      decide
    ·
      have factor_3_0 : (7 : ZMod 95930590621) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 95930590621) ^ 2 = 49 := by
        calc
          (7 : ZMod 95930590621) ^ 2 = (7 : ZMod 95930590621) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1 * (7 : ZMod 95930590621) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 95930590621) ^ 5 = 16807 := by
        calc
          (7 : ZMod 95930590621) ^ 5 = (7 : ZMod 95930590621) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 2 * (7 : ZMod 95930590621) ^ 2) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 95930590621) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 95930590621) ^ 10 = (7 : ZMod 95930590621) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 5 * (7 : ZMod 95930590621) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 95930590621) ^ 21 = 72904526712 := by
        calc
          (7 : ZMod 95930590621) ^ 21 = (7 : ZMod 95930590621) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 10 * (7 : ZMod 95930590621) ^ 10) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 72904526712 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 95930590621) ^ 42 = 76299567088 := by
        calc
          (7 : ZMod 95930590621) ^ 42 = (7 : ZMod 95930590621) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 21 * (7 : ZMod 95930590621) ^ 21 := by rw [pow_add]
          _ = 76299567088 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 95930590621) ^ 85 = 44590359957 := by
        calc
          (7 : ZMod 95930590621) ^ 85 = (7 : ZMod 95930590621) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 42 * (7 : ZMod 95930590621) ^ 42) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 44590359957 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 95930590621) ^ 170 = 20817969383 := by
        calc
          (7 : ZMod 95930590621) ^ 170 = (7 : ZMod 95930590621) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 85 * (7 : ZMod 95930590621) ^ 85 := by rw [pow_add]
          _ = 20817969383 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 95930590621) ^ 341 = 84861209033 := by
        calc
          (7 : ZMod 95930590621) ^ 341 = (7 : ZMod 95930590621) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 170 * (7 : ZMod 95930590621) ^ 170) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 84861209033 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 95930590621) ^ 682 = 88225112768 := by
        calc
          (7 : ZMod 95930590621) ^ 682 = (7 : ZMod 95930590621) ^ (341 + 341) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 341 * (7 : ZMod 95930590621) ^ 341 := by rw [pow_add]
          _ = 88225112768 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 95930590621) ^ 1365 = 64964384126 := by
        calc
          (7 : ZMod 95930590621) ^ 1365 = (7 : ZMod 95930590621) ^ (682 + 682 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 682 * (7 : ZMod 95930590621) ^ 682) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 64964384126 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 95930590621) ^ 2730 = 69775098526 := by
        calc
          (7 : ZMod 95930590621) ^ 2730 = (7 : ZMod 95930590621) ^ (1365 + 1365) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1365 * (7 : ZMod 95930590621) ^ 1365 := by rw [pow_add]
          _ = 69775098526 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 95930590621) ^ 5461 = 66116047988 := by
        calc
          (7 : ZMod 95930590621) ^ 5461 = (7 : ZMod 95930590621) ^ (2730 + 2730 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 2730 * (7 : ZMod 95930590621) ^ 2730) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 66116047988 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 95930590621) ^ 10923 = 49220774215 := by
        calc
          (7 : ZMod 95930590621) ^ 10923 = (7 : ZMod 95930590621) ^ (5461 + 5461 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 5461 * (7 : ZMod 95930590621) ^ 5461) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 49220774215 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 95930590621) ^ 21847 = 86184875960 := by
        calc
          (7 : ZMod 95930590621) ^ 21847 = (7 : ZMod 95930590621) ^ (10923 + 10923 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 10923 * (7 : ZMod 95930590621) ^ 10923) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 86184875960 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 95930590621) ^ 43695 = 80216687386 := by
        calc
          (7 : ZMod 95930590621) ^ 43695 = (7 : ZMod 95930590621) ^ (21847 + 21847 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 21847 * (7 : ZMod 95930590621) ^ 21847) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 80216687386 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 95930590621) ^ 87390 = 28000167959 := by
        calc
          (7 : ZMod 95930590621) ^ 87390 = (7 : ZMod 95930590621) ^ (43695 + 43695) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 43695 * (7 : ZMod 95930590621) ^ 43695 := by rw [pow_add]
          _ = 28000167959 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 95930590621) ^ 174780 = 43764148218 := by
        calc
          (7 : ZMod 95930590621) ^ 174780 = (7 : ZMod 95930590621) ^ (87390 + 87390) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 87390 * (7 : ZMod 95930590621) ^ 87390 := by rw [pow_add]
          _ = 43764148218 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 95930590621) ^ 349560 = 66795320775 := by
        calc
          (7 : ZMod 95930590621) ^ 349560 = (7 : ZMod 95930590621) ^ (174780 + 174780) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 174780 * (7 : ZMod 95930590621) ^ 174780 := by rw [pow_add]
          _ = 66795320775 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 95930590621) ^ 699121 = 63038186103 := by
        calc
          (7 : ZMod 95930590621) ^ 699121 = (7 : ZMod 95930590621) ^ (349560 + 349560 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 349560 * (7 : ZMod 95930590621) ^ 349560) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 63038186103 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 95930590621) ^ 1398242 = 87240277013 := by
        calc
          (7 : ZMod 95930590621) ^ 1398242 = (7 : ZMod 95930590621) ^ (699121 + 699121) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 699121 * (7 : ZMod 95930590621) ^ 699121 := by rw [pow_add]
          _ = 87240277013 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 95930590621) ^ 2796484 = 30728807591 := by
        calc
          (7 : ZMod 95930590621) ^ 2796484 = (7 : ZMod 95930590621) ^ (1398242 + 1398242) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1398242 * (7 : ZMod 95930590621) ^ 1398242 := by rw [pow_add]
          _ = 30728807591 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 95930590621) ^ 5592968 = 31559615913 := by
        calc
          (7 : ZMod 95930590621) ^ 5592968 = (7 : ZMod 95930590621) ^ (2796484 + 2796484) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 2796484 * (7 : ZMod 95930590621) ^ 2796484 := by rw [pow_add]
          _ = 31559615913 := by rw [factor_3_21]; decide
      have factor_3_23 : (7 : ZMod 95930590621) ^ 11185936 = 32506353013 := by
        calc
          (7 : ZMod 95930590621) ^ 11185936 = (7 : ZMod 95930590621) ^ (5592968 + 5592968) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 5592968 * (7 : ZMod 95930590621) ^ 5592968 := by rw [pow_add]
          _ = 32506353013 := by rw [factor_3_22]; decide
      have factor_3_24 : (7 : ZMod 95930590621) ^ 22371872 = 53281048854 := by
        calc
          (7 : ZMod 95930590621) ^ 22371872 = (7 : ZMod 95930590621) ^ (11185936 + 11185936) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 11185936 * (7 : ZMod 95930590621) ^ 11185936 := by rw [pow_add]
          _ = 53281048854 := by rw [factor_3_23]; decide
      have factor_3_25 : (7 : ZMod 95930590621) ^ 44743745 = 85006674329 := by
        calc
          (7 : ZMod 95930590621) ^ 44743745 = (7 : ZMod 95930590621) ^ (22371872 + 22371872 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 22371872 * (7 : ZMod 95930590621) ^ 22371872) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 85006674329 := by rw [factor_3_24]; decide
      have factor_3_26 : (7 : ZMod 95930590621) ^ 89487491 = 31144448307 := by
        calc
          (7 : ZMod 95930590621) ^ 89487491 = (7 : ZMod 95930590621) ^ (44743745 + 44743745 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 44743745 * (7 : ZMod 95930590621) ^ 44743745) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 31144448307 := by rw [factor_3_25]; decide
      have factor_3_27 : (7 : ZMod 95930590621) ^ 178974982 = 76032702697 := by
        calc
          (7 : ZMod 95930590621) ^ 178974982 = (7 : ZMod 95930590621) ^ (89487491 + 89487491) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 89487491 * (7 : ZMod 95930590621) ^ 89487491 := by rw [pow_add]
          _ = 76032702697 := by rw [factor_3_26]; decide
      have factor_3_28 : (7 : ZMod 95930590621) ^ 357949965 = 40989658543 := by
        calc
          (7 : ZMod 95930590621) ^ 357949965 = (7 : ZMod 95930590621) ^ (178974982 + 178974982 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 178974982 * (7 : ZMod 95930590621) ^ 178974982) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 40989658543 := by rw [factor_3_27]; decide
      have factor_3_29 : (7 : ZMod 95930590621) ^ 715899930 = 34707232244 := by
        calc
          (7 : ZMod 95930590621) ^ 715899930 = (7 : ZMod 95930590621) ^ (357949965 + 357949965) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 357949965 * (7 : ZMod 95930590621) ^ 357949965 := by rw [pow_add]
          _ = 34707232244 := by rw [factor_3_28]; decide
      have factor_3_30 : (7 : ZMod 95930590621) ^ 1431799860 = 84480697928 := by
        calc
          (7 : ZMod 95930590621) ^ 1431799860 = (7 : ZMod 95930590621) ^ (715899930 + 715899930) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 715899930 * (7 : ZMod 95930590621) ^ 715899930 := by rw [pow_add]
          _ = 84480697928 := by rw [factor_3_29]; decide
      change (7 : ZMod 95930590621) ^ 1431799860 ≠ 1
      rw [factor_3_30]
      decide
    ·
      have factor_4_0 : (7 : ZMod 95930590621) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 95930590621) ^ 3 = 343 := by
        calc
          (7 : ZMod 95930590621) ^ 3 = (7 : ZMod 95930590621) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 1 * (7 : ZMod 95930590621) ^ 1) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 95930590621) ^ 7 = 823543 := by
        calc
          (7 : ZMod 95930590621) ^ 7 = (7 : ZMod 95930590621) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 3 * (7 : ZMod 95930590621) ^ 3) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 95930590621) ^ 15 = 46962569514 := by
        calc
          (7 : ZMod 95930590621) ^ 15 = (7 : ZMod 95930590621) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 7 * (7 : ZMod 95930590621) ^ 7) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 46962569514 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 95930590621) ^ 31 = 59825240855 := by
        calc
          (7 : ZMod 95930590621) ^ 31 = (7 : ZMod 95930590621) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 15 * (7 : ZMod 95930590621) ^ 15) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 59825240855 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 95930590621) ^ 62 = 78160697774 := by
        calc
          (7 : ZMod 95930590621) ^ 62 = (7 : ZMod 95930590621) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 31 * (7 : ZMod 95930590621) ^ 31 := by rw [pow_add]
          _ = 78160697774 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 95930590621) ^ 125 = 43384897986 := by
        calc
          (7 : ZMod 95930590621) ^ 125 = (7 : ZMod 95930590621) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 62 * (7 : ZMod 95930590621) ^ 62) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 43384897986 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 95930590621) ^ 251 = 76931783316 := by
        calc
          (7 : ZMod 95930590621) ^ 251 = (7 : ZMod 95930590621) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 125 * (7 : ZMod 95930590621) ^ 125) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 76931783316 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 95930590621) ^ 502 = 87846907532 := by
        calc
          (7 : ZMod 95930590621) ^ 502 = (7 : ZMod 95930590621) ^ (251 + 251) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 251 * (7 : ZMod 95930590621) ^ 251 := by rw [pow_add]
          _ = 87846907532 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 95930590621) ^ 1005 = 23639059388 := by
        calc
          (7 : ZMod 95930590621) ^ 1005 = (7 : ZMod 95930590621) ^ (502 + 502 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = ((7 : ZMod 95930590621) ^ 502 * (7 : ZMod 95930590621) ^ 502) * (7 : ZMod 95930590621) := by rw [pow_succ, pow_add]
          _ = 23639059388 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 95930590621) ^ 2010 = 59046506217 := by
        calc
          (7 : ZMod 95930590621) ^ 2010 = (7 : ZMod 95930590621) ^ (1005 + 1005) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 1005 * (7 : ZMod 95930590621) ^ 1005 := by rw [pow_add]
          _ = 59046506217 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 95930590621) ^ 4020 = 31781375154 := by
        calc
          (7 : ZMod 95930590621) ^ 4020 = (7 : ZMod 95930590621) ^ (2010 + 2010) :=
            congrArg (fun n : ℕ => (7 : ZMod 95930590621) ^ n) (by norm_num)
          _ = (7 : ZMod 95930590621) ^ 2010 * (7 : ZMod 95930590621) ^ 2010 := by rw [pow_add]
          _ = 31781375154 := by rw [factor_4_10]; decide
      change (7 : ZMod 95930590621) ^ 4020 ≠ 1
      rw [factor_4_11]
      decide

#print axioms prime_lucas_95930590621

end TotientTailPeriodKiller
end Erdos249257
