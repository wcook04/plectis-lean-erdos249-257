import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_38763509 : Nat.Prime 38763509 := by
  apply lucas_primality 38763509 (2 : ZMod 38763509)
  ·
      have fermat_0 : (2 : ZMod 38763509) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 38763509) ^ 2 = 4 := by
        calc
          (2 : ZMod 38763509) ^ 2 = (2 : ZMod 38763509) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 1 * (2 : ZMod 38763509) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 38763509) ^ 4 = 16 := by
        calc
          (2 : ZMod 38763509) ^ 4 = (2 : ZMod 38763509) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 2 * (2 : ZMod 38763509) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 38763509) ^ 9 = 512 := by
        calc
          (2 : ZMod 38763509) ^ 9 = (2 : ZMod 38763509) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 4 * (2 : ZMod 38763509) ^ 4) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 38763509) ^ 18 = 262144 := by
        calc
          (2 : ZMod 38763509) ^ 18 = (2 : ZMod 38763509) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 9 * (2 : ZMod 38763509) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 38763509) ^ 36 = 30538788 := by
        calc
          (2 : ZMod 38763509) ^ 36 = (2 : ZMod 38763509) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 18 * (2 : ZMod 38763509) ^ 18 := by rw [pow_add]
          _ = 30538788 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 38763509) ^ 73 = 20815463 := by
        calc
          (2 : ZMod 38763509) ^ 73 = (2 : ZMod 38763509) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 36 * (2 : ZMod 38763509) ^ 36) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 20815463 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 38763509) ^ 147 = 34324213 := by
        calc
          (2 : ZMod 38763509) ^ 147 = (2 : ZMod 38763509) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 73 * (2 : ZMod 38763509) ^ 73) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 34324213 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 38763509) ^ 295 = 763541 := by
        calc
          (2 : ZMod 38763509) ^ 295 = (2 : ZMod 38763509) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 147 * (2 : ZMod 38763509) ^ 147) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 763541 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 38763509) ^ 591 = 22130151 := by
        calc
          (2 : ZMod 38763509) ^ 591 = (2 : ZMod 38763509) ^ (295 + 295 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 295 * (2 : ZMod 38763509) ^ 295) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 22130151 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 38763509) ^ 1182 = 22449050 := by
        calc
          (2 : ZMod 38763509) ^ 1182 = (2 : ZMod 38763509) ^ (591 + 591) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 591 * (2 : ZMod 38763509) ^ 591 := by rw [pow_add]
          _ = 22449050 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 38763509) ^ 2365 = 1448106 := by
        calc
          (2 : ZMod 38763509) ^ 2365 = (2 : ZMod 38763509) ^ (1182 + 1182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 1182 * (2 : ZMod 38763509) ^ 1182) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 1448106 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 38763509) ^ 4731 = 4118217 := by
        calc
          (2 : ZMod 38763509) ^ 4731 = (2 : ZMod 38763509) ^ (2365 + 2365 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 2365 * (2 : ZMod 38763509) ^ 2365) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 4118217 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 38763509) ^ 9463 = 34183872 := by
        calc
          (2 : ZMod 38763509) ^ 9463 = (2 : ZMod 38763509) ^ (4731 + 4731 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 4731 * (2 : ZMod 38763509) ^ 4731) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 34183872 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 38763509) ^ 18927 = 1960602 := by
        calc
          (2 : ZMod 38763509) ^ 18927 = (2 : ZMod 38763509) ^ (9463 + 9463 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 9463 * (2 : ZMod 38763509) ^ 9463) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 1960602 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 38763509) ^ 37854 = 15595928 := by
        calc
          (2 : ZMod 38763509) ^ 37854 = (2 : ZMod 38763509) ^ (18927 + 18927) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 18927 * (2 : ZMod 38763509) ^ 18927 := by rw [pow_add]
          _ = 15595928 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 38763509) ^ 75709 = 28032112 := by
        calc
          (2 : ZMod 38763509) ^ 75709 = (2 : ZMod 38763509) ^ (37854 + 37854 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 37854 * (2 : ZMod 38763509) ^ 37854) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 28032112 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 38763509) ^ 151419 = 8860347 := by
        calc
          (2 : ZMod 38763509) ^ 151419 = (2 : ZMod 38763509) ^ (75709 + 75709 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 75709 * (2 : ZMod 38763509) ^ 75709) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 8860347 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 38763509) ^ 302839 = 21006845 := by
        calc
          (2 : ZMod 38763509) ^ 302839 = (2 : ZMod 38763509) ^ (151419 + 151419 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 151419 * (2 : ZMod 38763509) ^ 151419) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 21006845 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 38763509) ^ 605679 = 19438813 := by
        calc
          (2 : ZMod 38763509) ^ 605679 = (2 : ZMod 38763509) ^ (302839 + 302839 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 302839 * (2 : ZMod 38763509) ^ 302839) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 19438813 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 38763509) ^ 1211359 = 18457087 := by
        calc
          (2 : ZMod 38763509) ^ 1211359 = (2 : ZMod 38763509) ^ (605679 + 605679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 605679 * (2 : ZMod 38763509) ^ 605679) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 18457087 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 38763509) ^ 2422719 = 25916841 := by
        calc
          (2 : ZMod 38763509) ^ 2422719 = (2 : ZMod 38763509) ^ (1211359 + 1211359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 1211359 * (2 : ZMod 38763509) ^ 1211359) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 25916841 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 38763509) ^ 4845438 = 37465945 := by
        calc
          (2 : ZMod 38763509) ^ 4845438 = (2 : ZMod 38763509) ^ (2422719 + 2422719) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 2422719 * (2 : ZMod 38763509) ^ 2422719 := by rw [pow_add]
          _ = 37465945 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 38763509) ^ 9690877 = 36168380 := by
        calc
          (2 : ZMod 38763509) ^ 9690877 = (2 : ZMod 38763509) ^ (4845438 + 4845438 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 4845438 * (2 : ZMod 38763509) ^ 4845438) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 36168380 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 38763509) ^ 19381754 = 38763508 := by
        calc
          (2 : ZMod 38763509) ^ 19381754 = (2 : ZMod 38763509) ^ (9690877 + 9690877) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 9690877 * (2 : ZMod 38763509) ^ 9690877 := by rw [pow_add]
          _ = 38763508 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 38763509) ^ 38763508 = 1 := by
        calc
          (2 : ZMod 38763509) ^ 38763508 = (2 : ZMod 38763509) ^ (19381754 + 19381754) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 19381754 * (2 : ZMod 38763509) ^ 19381754 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 2), (197773, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 2), (197773, 1)] : List FactorBlock).map factorBlockValue).prod = 38763509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 38763509) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 38763509) ^ 2 = 4 := by
        calc
          (2 : ZMod 38763509) ^ 2 = (2 : ZMod 38763509) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 1 * (2 : ZMod 38763509) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 38763509) ^ 4 = 16 := by
        calc
          (2 : ZMod 38763509) ^ 4 = (2 : ZMod 38763509) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 2 * (2 : ZMod 38763509) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 38763509) ^ 9 = 512 := by
        calc
          (2 : ZMod 38763509) ^ 9 = (2 : ZMod 38763509) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 4 * (2 : ZMod 38763509) ^ 4) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 38763509) ^ 18 = 262144 := by
        calc
          (2 : ZMod 38763509) ^ 18 = (2 : ZMod 38763509) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 9 * (2 : ZMod 38763509) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 38763509) ^ 36 = 30538788 := by
        calc
          (2 : ZMod 38763509) ^ 36 = (2 : ZMod 38763509) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 18 * (2 : ZMod 38763509) ^ 18 := by rw [pow_add]
          _ = 30538788 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 38763509) ^ 73 = 20815463 := by
        calc
          (2 : ZMod 38763509) ^ 73 = (2 : ZMod 38763509) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 36 * (2 : ZMod 38763509) ^ 36) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 20815463 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 38763509) ^ 147 = 34324213 := by
        calc
          (2 : ZMod 38763509) ^ 147 = (2 : ZMod 38763509) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 73 * (2 : ZMod 38763509) ^ 73) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 34324213 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 38763509) ^ 295 = 763541 := by
        calc
          (2 : ZMod 38763509) ^ 295 = (2 : ZMod 38763509) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 147 * (2 : ZMod 38763509) ^ 147) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 763541 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 38763509) ^ 591 = 22130151 := by
        calc
          (2 : ZMod 38763509) ^ 591 = (2 : ZMod 38763509) ^ (295 + 295 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 295 * (2 : ZMod 38763509) ^ 295) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 22130151 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 38763509) ^ 1182 = 22449050 := by
        calc
          (2 : ZMod 38763509) ^ 1182 = (2 : ZMod 38763509) ^ (591 + 591) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 591 * (2 : ZMod 38763509) ^ 591 := by rw [pow_add]
          _ = 22449050 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 38763509) ^ 2365 = 1448106 := by
        calc
          (2 : ZMod 38763509) ^ 2365 = (2 : ZMod 38763509) ^ (1182 + 1182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 1182 * (2 : ZMod 38763509) ^ 1182) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 1448106 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 38763509) ^ 4731 = 4118217 := by
        calc
          (2 : ZMod 38763509) ^ 4731 = (2 : ZMod 38763509) ^ (2365 + 2365 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 2365 * (2 : ZMod 38763509) ^ 2365) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 4118217 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 38763509) ^ 9463 = 34183872 := by
        calc
          (2 : ZMod 38763509) ^ 9463 = (2 : ZMod 38763509) ^ (4731 + 4731 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 4731 * (2 : ZMod 38763509) ^ 4731) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 34183872 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 38763509) ^ 18927 = 1960602 := by
        calc
          (2 : ZMod 38763509) ^ 18927 = (2 : ZMod 38763509) ^ (9463 + 9463 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 9463 * (2 : ZMod 38763509) ^ 9463) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 1960602 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 38763509) ^ 37854 = 15595928 := by
        calc
          (2 : ZMod 38763509) ^ 37854 = (2 : ZMod 38763509) ^ (18927 + 18927) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 18927 * (2 : ZMod 38763509) ^ 18927 := by rw [pow_add]
          _ = 15595928 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 38763509) ^ 75709 = 28032112 := by
        calc
          (2 : ZMod 38763509) ^ 75709 = (2 : ZMod 38763509) ^ (37854 + 37854 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 37854 * (2 : ZMod 38763509) ^ 37854) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 28032112 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 38763509) ^ 151419 = 8860347 := by
        calc
          (2 : ZMod 38763509) ^ 151419 = (2 : ZMod 38763509) ^ (75709 + 75709 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 75709 * (2 : ZMod 38763509) ^ 75709) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 8860347 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 38763509) ^ 302839 = 21006845 := by
        calc
          (2 : ZMod 38763509) ^ 302839 = (2 : ZMod 38763509) ^ (151419 + 151419 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 151419 * (2 : ZMod 38763509) ^ 151419) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 21006845 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 38763509) ^ 605679 = 19438813 := by
        calc
          (2 : ZMod 38763509) ^ 605679 = (2 : ZMod 38763509) ^ (302839 + 302839 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 302839 * (2 : ZMod 38763509) ^ 302839) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 19438813 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 38763509) ^ 1211359 = 18457087 := by
        calc
          (2 : ZMod 38763509) ^ 1211359 = (2 : ZMod 38763509) ^ (605679 + 605679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 605679 * (2 : ZMod 38763509) ^ 605679) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 18457087 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 38763509) ^ 2422719 = 25916841 := by
        calc
          (2 : ZMod 38763509) ^ 2422719 = (2 : ZMod 38763509) ^ (1211359 + 1211359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 1211359 * (2 : ZMod 38763509) ^ 1211359) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 25916841 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 38763509) ^ 4845438 = 37465945 := by
        calc
          (2 : ZMod 38763509) ^ 4845438 = (2 : ZMod 38763509) ^ (2422719 + 2422719) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 2422719 * (2 : ZMod 38763509) ^ 2422719 := by rw [pow_add]
          _ = 37465945 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 38763509) ^ 9690877 = 36168380 := by
        calc
          (2 : ZMod 38763509) ^ 9690877 = (2 : ZMod 38763509) ^ (4845438 + 4845438 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 4845438 * (2 : ZMod 38763509) ^ 4845438) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 36168380 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 38763509) ^ 19381754 = 38763508 := by
        calc
          (2 : ZMod 38763509) ^ 19381754 = (2 : ZMod 38763509) ^ (9690877 + 9690877) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 9690877 * (2 : ZMod 38763509) ^ 9690877 := by rw [pow_add]
          _ = 38763508 := by rw [factor_0_23]; decide
      change (2 : ZMod 38763509) ^ 19381754 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 38763509) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 38763509) ^ 2 = 4 := by
        calc
          (2 : ZMod 38763509) ^ 2 = (2 : ZMod 38763509) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 1 * (2 : ZMod 38763509) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 38763509) ^ 5 = 32 := by
        calc
          (2 : ZMod 38763509) ^ 5 = (2 : ZMod 38763509) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 2 * (2 : ZMod 38763509) ^ 2) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 38763509) ^ 10 = 1024 := by
        calc
          (2 : ZMod 38763509) ^ 10 = (2 : ZMod 38763509) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 5 * (2 : ZMod 38763509) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 38763509) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 38763509) ^ 21 = (2 : ZMod 38763509) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 10 * (2 : ZMod 38763509) ^ 10) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 38763509) ^ 42 = 16306982 := by
        calc
          (2 : ZMod 38763509) ^ 42 = (2 : ZMod 38763509) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 21 * (2 : ZMod 38763509) ^ 21 := by rw [pow_add]
          _ = 16306982 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 38763509) ^ 84 = 28971833 := by
        calc
          (2 : ZMod 38763509) ^ 84 = (2 : ZMod 38763509) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 42 * (2 : ZMod 38763509) ^ 42 := by rw [pow_add]
          _ = 28971833 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 38763509) ^ 168 = 30998556 := by
        calc
          (2 : ZMod 38763509) ^ 168 = (2 : ZMod 38763509) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 84 * (2 : ZMod 38763509) ^ 84 := by rw [pow_add]
          _ = 30998556 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 38763509) ^ 337 = 16434917 := by
        calc
          (2 : ZMod 38763509) ^ 337 = (2 : ZMod 38763509) ^ (168 + 168 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 168 * (2 : ZMod 38763509) ^ 168) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 16434917 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 38763509) ^ 675 = 3021680 := by
        calc
          (2 : ZMod 38763509) ^ 675 = (2 : ZMod 38763509) ^ (337 + 337 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 337 * (2 : ZMod 38763509) ^ 337) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 3021680 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 38763509) ^ 1351 = 37353499 := by
        calc
          (2 : ZMod 38763509) ^ 1351 = (2 : ZMod 38763509) ^ (675 + 675 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 675 * (2 : ZMod 38763509) ^ 675) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 37353499 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 38763509) ^ 2703 = 11937507 := by
        calc
          (2 : ZMod 38763509) ^ 2703 = (2 : ZMod 38763509) ^ (1351 + 1351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 1351 * (2 : ZMod 38763509) ^ 1351) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 11937507 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 38763509) ^ 5407 = 28280233 := by
        calc
          (2 : ZMod 38763509) ^ 5407 = (2 : ZMod 38763509) ^ (2703 + 2703 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 2703 * (2 : ZMod 38763509) ^ 2703) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 28280233 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 38763509) ^ 10815 = 23456755 := by
        calc
          (2 : ZMod 38763509) ^ 10815 = (2 : ZMod 38763509) ^ (5407 + 5407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 5407 * (2 : ZMod 38763509) ^ 5407) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 23456755 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 38763509) ^ 21631 = 20979861 := by
        calc
          (2 : ZMod 38763509) ^ 21631 = (2 : ZMod 38763509) ^ (10815 + 10815 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 10815 * (2 : ZMod 38763509) ^ 10815) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 20979861 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 38763509) ^ 43262 = 904000 := by
        calc
          (2 : ZMod 38763509) ^ 43262 = (2 : ZMod 38763509) ^ (21631 + 21631) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 21631 * (2 : ZMod 38763509) ^ 21631 := by rw [pow_add]
          _ = 904000 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 38763509) ^ 86525 = 7406524 := by
        calc
          (2 : ZMod 38763509) ^ 86525 = (2 : ZMod 38763509) ^ (43262 + 43262 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 43262 * (2 : ZMod 38763509) ^ 43262) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 7406524 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 38763509) ^ 173051 = 21968763 := by
        calc
          (2 : ZMod 38763509) ^ 173051 = (2 : ZMod 38763509) ^ (86525 + 86525 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 86525 * (2 : ZMod 38763509) ^ 86525) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 21968763 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 38763509) ^ 346102 = 5932327 := by
        calc
          (2 : ZMod 38763509) ^ 346102 = (2 : ZMod 38763509) ^ (173051 + 173051) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 173051 * (2 : ZMod 38763509) ^ 173051 := by rw [pow_add]
          _ = 5932327 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 38763509) ^ 692205 = 10749072 := by
        calc
          (2 : ZMod 38763509) ^ 692205 = (2 : ZMod 38763509) ^ (346102 + 346102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 346102 * (2 : ZMod 38763509) ^ 346102) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 10749072 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 38763509) ^ 1384411 = 5061696 := by
        calc
          (2 : ZMod 38763509) ^ 1384411 = (2 : ZMod 38763509) ^ (692205 + 692205 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 692205 * (2 : ZMod 38763509) ^ 692205) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 5061696 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 38763509) ^ 2768822 = 25122866 := by
        calc
          (2 : ZMod 38763509) ^ 2768822 = (2 : ZMod 38763509) ^ (1384411 + 1384411) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 1384411 * (2 : ZMod 38763509) ^ 1384411 := by rw [pow_add]
          _ = 25122866 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 38763509) ^ 5537644 = 11206418 := by
        calc
          (2 : ZMod 38763509) ^ 5537644 = (2 : ZMod 38763509) ^ (2768822 + 2768822) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 2768822 * (2 : ZMod 38763509) ^ 2768822 := by rw [pow_add]
          _ = 11206418 := by rw [factor_1_21]; decide
      change (2 : ZMod 38763509) ^ 5537644 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (2 : ZMod 38763509) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 38763509) ^ 3 = 8 := by
        calc
          (2 : ZMod 38763509) ^ 3 = (2 : ZMod 38763509) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 1 * (2 : ZMod 38763509) ^ 1) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 38763509) ^ 6 = 64 := by
        calc
          (2 : ZMod 38763509) ^ 6 = (2 : ZMod 38763509) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 3 * (2 : ZMod 38763509) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 38763509) ^ 12 = 4096 := by
        calc
          (2 : ZMod 38763509) ^ 12 = (2 : ZMod 38763509) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 6 * (2 : ZMod 38763509) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 38763509) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 38763509) ^ 24 = (2 : ZMod 38763509) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 12 * (2 : ZMod 38763509) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 38763509) ^ 49 = 32827719 := by
        calc
          (2 : ZMod 38763509) ^ 49 = (2 : ZMod 38763509) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = ((2 : ZMod 38763509) ^ 24 * (2 : ZMod 38763509) ^ 24) * (2 : ZMod 38763509) := by rw [pow_succ, pow_add]
          _ = 32827719 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 38763509) ^ 98 = 15344167 := by
        calc
          (2 : ZMod 38763509) ^ 98 = (2 : ZMod 38763509) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 49 * (2 : ZMod 38763509) ^ 49 := by rw [pow_add]
          _ = 15344167 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 38763509) ^ 196 = 31892311 := by
        calc
          (2 : ZMod 38763509) ^ 196 = (2 : ZMod 38763509) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (2 : ZMod 38763509) ^ n) (by norm_num)
          _ = (2 : ZMod 38763509) ^ 98 * (2 : ZMod 38763509) ^ 98 := by rw [pow_add]
          _ = 31892311 := by rw [factor_2_6]; decide
      change (2 : ZMod 38763509) ^ 196 ≠ 1
      rw [factor_2_7]
      decide

#print axioms prime_lucas_38763509

end TotientTailPeriodKiller
end Erdos249257
