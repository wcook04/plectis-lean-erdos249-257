import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1202644063 : Nat.Prime 1202644063 := by
  apply lucas_primality 1202644063 (5 : ZMod 1202644063)
  ·
      have fermat_0 : (5 : ZMod 1202644063) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 1202644063) ^ 2 = 25 := by
        calc
          (5 : ZMod 1202644063) ^ 2 = (5 : ZMod 1202644063) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 1 * (5 : ZMod 1202644063) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 1202644063) ^ 4 = 625 := by
        calc
          (5 : ZMod 1202644063) ^ 4 = (5 : ZMod 1202644063) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 2 * (5 : ZMod 1202644063) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 1202644063) ^ 8 = 390625 := by
        calc
          (5 : ZMod 1202644063) ^ 8 = (5 : ZMod 1202644063) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 4 * (5 : ZMod 1202644063) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 1202644063) ^ 17 = 463117183 := by
        calc
          (5 : ZMod 1202644063) ^ 17 = (5 : ZMod 1202644063) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 8 * (5 : ZMod 1202644063) ^ 8) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 463117183 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 1202644063) ^ 35 = 345289763 := by
        calc
          (5 : ZMod 1202644063) ^ 35 = (5 : ZMod 1202644063) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 17 * (5 : ZMod 1202644063) ^ 17) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 345289763 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 1202644063) ^ 71 = 1130795847 := by
        calc
          (5 : ZMod 1202644063) ^ 71 = (5 : ZMod 1202644063) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 35 * (5 : ZMod 1202644063) ^ 35) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1130795847 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 1202644063) ^ 143 = 127195849 := by
        calc
          (5 : ZMod 1202644063) ^ 143 = (5 : ZMod 1202644063) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 71 * (5 : ZMod 1202644063) ^ 71) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 127195849 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 1202644063) ^ 286 = 674680087 := by
        calc
          (5 : ZMod 1202644063) ^ 286 = (5 : ZMod 1202644063) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 143 * (5 : ZMod 1202644063) ^ 143 := by rw [pow_add]
          _ = 674680087 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 1202644063) ^ 573 = 428529494 := by
        calc
          (5 : ZMod 1202644063) ^ 573 = (5 : ZMod 1202644063) ^ (286 + 286 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 286 * (5 : ZMod 1202644063) ^ 286) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 428529494 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 1202644063) ^ 1146 = 85533935 := by
        calc
          (5 : ZMod 1202644063) ^ 1146 = (5 : ZMod 1202644063) ^ (573 + 573) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 573 * (5 : ZMod 1202644063) ^ 573 := by rw [pow_add]
          _ = 85533935 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 1202644063) ^ 2293 = 137563168 := by
        calc
          (5 : ZMod 1202644063) ^ 2293 = (5 : ZMod 1202644063) ^ (1146 + 1146 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 1146 * (5 : ZMod 1202644063) ^ 1146) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 137563168 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 1202644063) ^ 4587 = 867066702 := by
        calc
          (5 : ZMod 1202644063) ^ 4587 = (5 : ZMod 1202644063) ^ (2293 + 2293 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 2293 * (5 : ZMod 1202644063) ^ 2293) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 867066702 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 1202644063) ^ 9175 = 230834662 := by
        calc
          (5 : ZMod 1202644063) ^ 9175 = (5 : ZMod 1202644063) ^ (4587 + 4587 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 4587 * (5 : ZMod 1202644063) ^ 4587) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 230834662 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 1202644063) ^ 18350 = 1082868935 := by
        calc
          (5 : ZMod 1202644063) ^ 18350 = (5 : ZMod 1202644063) ^ (9175 + 9175) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 9175 * (5 : ZMod 1202644063) ^ 9175 := by rw [pow_add]
          _ = 1082868935 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 1202644063) ^ 36701 = 155034960 := by
        calc
          (5 : ZMod 1202644063) ^ 36701 = (5 : ZMod 1202644063) ^ (18350 + 18350 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 18350 * (5 : ZMod 1202644063) ^ 18350) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 155034960 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 1202644063) ^ 73403 = 1156091865 := by
        calc
          (5 : ZMod 1202644063) ^ 73403 = (5 : ZMod 1202644063) ^ (36701 + 36701 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 36701 * (5 : ZMod 1202644063) ^ 36701) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1156091865 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 1202644063) ^ 146807 = 117457077 := by
        calc
          (5 : ZMod 1202644063) ^ 146807 = (5 : ZMod 1202644063) ^ (73403 + 73403 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 73403 * (5 : ZMod 1202644063) ^ 73403) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 117457077 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 1202644063) ^ 293614 = 1097289728 := by
        calc
          (5 : ZMod 1202644063) ^ 293614 = (5 : ZMod 1202644063) ^ (146807 + 146807) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 146807 * (5 : ZMod 1202644063) ^ 146807 := by rw [pow_add]
          _ = 1097289728 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 1202644063) ^ 587228 = 713459774 := by
        calc
          (5 : ZMod 1202644063) ^ 587228 = (5 : ZMod 1202644063) ^ (293614 + 293614) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 293614 * (5 : ZMod 1202644063) ^ 293614 := by rw [pow_add]
          _ = 713459774 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 1202644063) ^ 1174457 = 455867491 := by
        calc
          (5 : ZMod 1202644063) ^ 1174457 = (5 : ZMod 1202644063) ^ (587228 + 587228 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 587228 * (5 : ZMod 1202644063) ^ 587228) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 455867491 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 1202644063) ^ 2348914 = 1058465486 := by
        calc
          (5 : ZMod 1202644063) ^ 2348914 = (5 : ZMod 1202644063) ^ (1174457 + 1174457) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 1174457 * (5 : ZMod 1202644063) ^ 1174457 := by rw [pow_add]
          _ = 1058465486 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 1202644063) ^ 4697828 = 1168246592 := by
        calc
          (5 : ZMod 1202644063) ^ 4697828 = (5 : ZMod 1202644063) ^ (2348914 + 2348914) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 2348914 * (5 : ZMod 1202644063) ^ 2348914 := by rw [pow_add]
          _ = 1168246592 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 1202644063) ^ 9395656 = 729135181 := by
        calc
          (5 : ZMod 1202644063) ^ 9395656 = (5 : ZMod 1202644063) ^ (4697828 + 4697828) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 4697828 * (5 : ZMod 1202644063) ^ 4697828 := by rw [pow_add]
          _ = 729135181 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 1202644063) ^ 18791313 = 1138762902 := by
        calc
          (5 : ZMod 1202644063) ^ 18791313 = (5 : ZMod 1202644063) ^ (9395656 + 9395656 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 9395656 * (5 : ZMod 1202644063) ^ 9395656) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1138762902 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 1202644063) ^ 37582626 = 517288825 := by
        calc
          (5 : ZMod 1202644063) ^ 37582626 = (5 : ZMod 1202644063) ^ (18791313 + 18791313) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 18791313 * (5 : ZMod 1202644063) ^ 18791313 := by rw [pow_add]
          _ = 517288825 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 1202644063) ^ 75165253 = 189145884 := by
        calc
          (5 : ZMod 1202644063) ^ 75165253 = (5 : ZMod 1202644063) ^ (37582626 + 37582626 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 37582626 * (5 : ZMod 1202644063) ^ 37582626) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 189145884 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 1202644063) ^ 150330507 = 231610905 := by
        calc
          (5 : ZMod 1202644063) ^ 150330507 = (5 : ZMod 1202644063) ^ (75165253 + 75165253 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 75165253 * (5 : ZMod 1202644063) ^ 75165253) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 231610905 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 1202644063) ^ 300661015 = 19945805 := by
        calc
          (5 : ZMod 1202644063) ^ 300661015 = (5 : ZMod 1202644063) ^ (150330507 + 150330507 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 150330507 * (5 : ZMod 1202644063) ^ 150330507) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 19945805 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 1202644063) ^ 601322031 = 1202644062 := by
        calc
          (5 : ZMod 1202644063) ^ 601322031 = (5 : ZMod 1202644063) ^ (300661015 + 300661015 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 300661015 * (5 : ZMod 1202644063) ^ 300661015) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1202644062 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 1202644063) ^ 1202644062 = 1 := by
        calc
          (5 : ZMod 1202644063) ^ 1202644062 = (5 : ZMod 1202644063) ^ (601322031 + 601322031) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 601322031 * (5 : ZMod 1202644063) ^ 601322031 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (41, 1), (1629599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (41, 1), (1629599, 1)] : List FactorBlock).map factorBlockValue).prod = 1202644063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 1202644063) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 1202644063) ^ 2 = 25 := by
        calc
          (5 : ZMod 1202644063) ^ 2 = (5 : ZMod 1202644063) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 1 * (5 : ZMod 1202644063) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 1202644063) ^ 4 = 625 := by
        calc
          (5 : ZMod 1202644063) ^ 4 = (5 : ZMod 1202644063) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 2 * (5 : ZMod 1202644063) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 1202644063) ^ 8 = 390625 := by
        calc
          (5 : ZMod 1202644063) ^ 8 = (5 : ZMod 1202644063) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 4 * (5 : ZMod 1202644063) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 1202644063) ^ 17 = 463117183 := by
        calc
          (5 : ZMod 1202644063) ^ 17 = (5 : ZMod 1202644063) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 8 * (5 : ZMod 1202644063) ^ 8) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 463117183 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 1202644063) ^ 35 = 345289763 := by
        calc
          (5 : ZMod 1202644063) ^ 35 = (5 : ZMod 1202644063) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 17 * (5 : ZMod 1202644063) ^ 17) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 345289763 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 1202644063) ^ 71 = 1130795847 := by
        calc
          (5 : ZMod 1202644063) ^ 71 = (5 : ZMod 1202644063) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 35 * (5 : ZMod 1202644063) ^ 35) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1130795847 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 1202644063) ^ 143 = 127195849 := by
        calc
          (5 : ZMod 1202644063) ^ 143 = (5 : ZMod 1202644063) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 71 * (5 : ZMod 1202644063) ^ 71) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 127195849 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 1202644063) ^ 286 = 674680087 := by
        calc
          (5 : ZMod 1202644063) ^ 286 = (5 : ZMod 1202644063) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 143 * (5 : ZMod 1202644063) ^ 143 := by rw [pow_add]
          _ = 674680087 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 1202644063) ^ 573 = 428529494 := by
        calc
          (5 : ZMod 1202644063) ^ 573 = (5 : ZMod 1202644063) ^ (286 + 286 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 286 * (5 : ZMod 1202644063) ^ 286) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 428529494 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 1202644063) ^ 1146 = 85533935 := by
        calc
          (5 : ZMod 1202644063) ^ 1146 = (5 : ZMod 1202644063) ^ (573 + 573) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 573 * (5 : ZMod 1202644063) ^ 573 := by rw [pow_add]
          _ = 85533935 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 1202644063) ^ 2293 = 137563168 := by
        calc
          (5 : ZMod 1202644063) ^ 2293 = (5 : ZMod 1202644063) ^ (1146 + 1146 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 1146 * (5 : ZMod 1202644063) ^ 1146) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 137563168 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 1202644063) ^ 4587 = 867066702 := by
        calc
          (5 : ZMod 1202644063) ^ 4587 = (5 : ZMod 1202644063) ^ (2293 + 2293 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 2293 * (5 : ZMod 1202644063) ^ 2293) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 867066702 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 1202644063) ^ 9175 = 230834662 := by
        calc
          (5 : ZMod 1202644063) ^ 9175 = (5 : ZMod 1202644063) ^ (4587 + 4587 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 4587 * (5 : ZMod 1202644063) ^ 4587) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 230834662 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 1202644063) ^ 18350 = 1082868935 := by
        calc
          (5 : ZMod 1202644063) ^ 18350 = (5 : ZMod 1202644063) ^ (9175 + 9175) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 9175 * (5 : ZMod 1202644063) ^ 9175 := by rw [pow_add]
          _ = 1082868935 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 1202644063) ^ 36701 = 155034960 := by
        calc
          (5 : ZMod 1202644063) ^ 36701 = (5 : ZMod 1202644063) ^ (18350 + 18350 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 18350 * (5 : ZMod 1202644063) ^ 18350) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 155034960 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 1202644063) ^ 73403 = 1156091865 := by
        calc
          (5 : ZMod 1202644063) ^ 73403 = (5 : ZMod 1202644063) ^ (36701 + 36701 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 36701 * (5 : ZMod 1202644063) ^ 36701) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1156091865 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 1202644063) ^ 146807 = 117457077 := by
        calc
          (5 : ZMod 1202644063) ^ 146807 = (5 : ZMod 1202644063) ^ (73403 + 73403 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 73403 * (5 : ZMod 1202644063) ^ 73403) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 117457077 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 1202644063) ^ 293614 = 1097289728 := by
        calc
          (5 : ZMod 1202644063) ^ 293614 = (5 : ZMod 1202644063) ^ (146807 + 146807) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 146807 * (5 : ZMod 1202644063) ^ 146807 := by rw [pow_add]
          _ = 1097289728 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 1202644063) ^ 587228 = 713459774 := by
        calc
          (5 : ZMod 1202644063) ^ 587228 = (5 : ZMod 1202644063) ^ (293614 + 293614) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 293614 * (5 : ZMod 1202644063) ^ 293614 := by rw [pow_add]
          _ = 713459774 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 1202644063) ^ 1174457 = 455867491 := by
        calc
          (5 : ZMod 1202644063) ^ 1174457 = (5 : ZMod 1202644063) ^ (587228 + 587228 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 587228 * (5 : ZMod 1202644063) ^ 587228) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 455867491 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 1202644063) ^ 2348914 = 1058465486 := by
        calc
          (5 : ZMod 1202644063) ^ 2348914 = (5 : ZMod 1202644063) ^ (1174457 + 1174457) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 1174457 * (5 : ZMod 1202644063) ^ 1174457 := by rw [pow_add]
          _ = 1058465486 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 1202644063) ^ 4697828 = 1168246592 := by
        calc
          (5 : ZMod 1202644063) ^ 4697828 = (5 : ZMod 1202644063) ^ (2348914 + 2348914) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 2348914 * (5 : ZMod 1202644063) ^ 2348914 := by rw [pow_add]
          _ = 1168246592 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 1202644063) ^ 9395656 = 729135181 := by
        calc
          (5 : ZMod 1202644063) ^ 9395656 = (5 : ZMod 1202644063) ^ (4697828 + 4697828) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 4697828 * (5 : ZMod 1202644063) ^ 4697828 := by rw [pow_add]
          _ = 729135181 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 1202644063) ^ 18791313 = 1138762902 := by
        calc
          (5 : ZMod 1202644063) ^ 18791313 = (5 : ZMod 1202644063) ^ (9395656 + 9395656 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 9395656 * (5 : ZMod 1202644063) ^ 9395656) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1138762902 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 1202644063) ^ 37582626 = 517288825 := by
        calc
          (5 : ZMod 1202644063) ^ 37582626 = (5 : ZMod 1202644063) ^ (18791313 + 18791313) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 18791313 * (5 : ZMod 1202644063) ^ 18791313 := by rw [pow_add]
          _ = 517288825 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 1202644063) ^ 75165253 = 189145884 := by
        calc
          (5 : ZMod 1202644063) ^ 75165253 = (5 : ZMod 1202644063) ^ (37582626 + 37582626 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 37582626 * (5 : ZMod 1202644063) ^ 37582626) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 189145884 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 1202644063) ^ 150330507 = 231610905 := by
        calc
          (5 : ZMod 1202644063) ^ 150330507 = (5 : ZMod 1202644063) ^ (75165253 + 75165253 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 75165253 * (5 : ZMod 1202644063) ^ 75165253) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 231610905 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 1202644063) ^ 300661015 = 19945805 := by
        calc
          (5 : ZMod 1202644063) ^ 300661015 = (5 : ZMod 1202644063) ^ (150330507 + 150330507 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 150330507 * (5 : ZMod 1202644063) ^ 150330507) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 19945805 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 1202644063) ^ 601322031 = 1202644062 := by
        calc
          (5 : ZMod 1202644063) ^ 601322031 = (5 : ZMod 1202644063) ^ (300661015 + 300661015 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 300661015 * (5 : ZMod 1202644063) ^ 300661015) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1202644062 := by rw [factor_0_28]; decide
      change (5 : ZMod 1202644063) ^ 601322031 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (5 : ZMod 1202644063) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 1202644063) ^ 2 = 25 := by
        calc
          (5 : ZMod 1202644063) ^ 2 = (5 : ZMod 1202644063) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 1 * (5 : ZMod 1202644063) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 1202644063) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1202644063) ^ 5 = (5 : ZMod 1202644063) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 2 * (5 : ZMod 1202644063) ^ 2) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 1202644063) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 1202644063) ^ 11 = (5 : ZMod 1202644063) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 5 * (5 : ZMod 1202644063) ^ 5) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 1202644063) ^ 23 = 1099301367 := by
        calc
          (5 : ZMod 1202644063) ^ 23 = (5 : ZMod 1202644063) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 11 * (5 : ZMod 1202644063) ^ 11) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1099301367 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 1202644063) ^ 47 = 1120800970 := by
        calc
          (5 : ZMod 1202644063) ^ 47 = (5 : ZMod 1202644063) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 23 * (5 : ZMod 1202644063) ^ 23) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1120800970 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 1202644063) ^ 95 = 192881338 := by
        calc
          (5 : ZMod 1202644063) ^ 95 = (5 : ZMod 1202644063) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 47 * (5 : ZMod 1202644063) ^ 47) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 192881338 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 1202644063) ^ 191 = 1115967121 := by
        calc
          (5 : ZMod 1202644063) ^ 191 = (5 : ZMod 1202644063) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 95 * (5 : ZMod 1202644063) ^ 95) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1115967121 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 1202644063) ^ 382 = 68435687 := by
        calc
          (5 : ZMod 1202644063) ^ 382 = (5 : ZMod 1202644063) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 191 * (5 : ZMod 1202644063) ^ 191 := by rw [pow_add]
          _ = 68435687 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 1202644063) ^ 764 = 912349825 := by
        calc
          (5 : ZMod 1202644063) ^ 764 = (5 : ZMod 1202644063) ^ (382 + 382) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 382 * (5 : ZMod 1202644063) ^ 382 := by rw [pow_add]
          _ = 912349825 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 1202644063) ^ 1529 = 994558904 := by
        calc
          (5 : ZMod 1202644063) ^ 1529 = (5 : ZMod 1202644063) ^ (764 + 764 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 764 * (5 : ZMod 1202644063) ^ 764) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 994558904 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 1202644063) ^ 3058 = 591868828 := by
        calc
          (5 : ZMod 1202644063) ^ 3058 = (5 : ZMod 1202644063) ^ (1529 + 1529) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 1529 * (5 : ZMod 1202644063) ^ 1529 := by rw [pow_add]
          _ = 591868828 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 1202644063) ^ 6116 = 889972213 := by
        calc
          (5 : ZMod 1202644063) ^ 6116 = (5 : ZMod 1202644063) ^ (3058 + 3058) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 3058 * (5 : ZMod 1202644063) ^ 3058 := by rw [pow_add]
          _ = 889972213 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 1202644063) ^ 12233 = 864218129 := by
        calc
          (5 : ZMod 1202644063) ^ 12233 = (5 : ZMod 1202644063) ^ (6116 + 6116 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 6116 * (5 : ZMod 1202644063) ^ 6116) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 864218129 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 1202644063) ^ 24467 = 1149904678 := by
        calc
          (5 : ZMod 1202644063) ^ 24467 = (5 : ZMod 1202644063) ^ (12233 + 12233 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 12233 * (5 : ZMod 1202644063) ^ 12233) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1149904678 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 1202644063) ^ 48935 = 63307630 := by
        calc
          (5 : ZMod 1202644063) ^ 48935 = (5 : ZMod 1202644063) ^ (24467 + 24467 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 24467 * (5 : ZMod 1202644063) ^ 24467) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 63307630 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 1202644063) ^ 97871 = 892195345 := by
        calc
          (5 : ZMod 1202644063) ^ 97871 = (5 : ZMod 1202644063) ^ (48935 + 48935 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 48935 * (5 : ZMod 1202644063) ^ 48935) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 892195345 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 1202644063) ^ 195742 = 172373518 := by
        calc
          (5 : ZMod 1202644063) ^ 195742 = (5 : ZMod 1202644063) ^ (97871 + 97871) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 97871 * (5 : ZMod 1202644063) ^ 97871 := by rw [pow_add]
          _ = 172373518 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 1202644063) ^ 391485 = 677992026 := by
        calc
          (5 : ZMod 1202644063) ^ 391485 = (5 : ZMod 1202644063) ^ (195742 + 195742 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 195742 * (5 : ZMod 1202644063) ^ 195742) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 677992026 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 1202644063) ^ 782971 = 680561033 := by
        calc
          (5 : ZMod 1202644063) ^ 782971 = (5 : ZMod 1202644063) ^ (391485 + 391485 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 391485 * (5 : ZMod 1202644063) ^ 391485) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 680561033 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 1202644063) ^ 1565942 = 213640720 := by
        calc
          (5 : ZMod 1202644063) ^ 1565942 = (5 : ZMod 1202644063) ^ (782971 + 782971) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 782971 * (5 : ZMod 1202644063) ^ 782971 := by rw [pow_add]
          _ = 213640720 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 1202644063) ^ 3131885 = 707026249 := by
        calc
          (5 : ZMod 1202644063) ^ 3131885 = (5 : ZMod 1202644063) ^ (1565942 + 1565942 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 1565942 * (5 : ZMod 1202644063) ^ 1565942) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 707026249 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 1202644063) ^ 6263771 = 165645221 := by
        calc
          (5 : ZMod 1202644063) ^ 6263771 = (5 : ZMod 1202644063) ^ (3131885 + 3131885 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 3131885 * (5 : ZMod 1202644063) ^ 3131885) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 165645221 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 1202644063) ^ 12527542 = 511065085 := by
        calc
          (5 : ZMod 1202644063) ^ 12527542 = (5 : ZMod 1202644063) ^ (6263771 + 6263771) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 6263771 * (5 : ZMod 1202644063) ^ 6263771 := by rw [pow_add]
          _ = 511065085 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 1202644063) ^ 25055084 = 276655542 := by
        calc
          (5 : ZMod 1202644063) ^ 25055084 = (5 : ZMod 1202644063) ^ (12527542 + 12527542) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 12527542 * (5 : ZMod 1202644063) ^ 12527542 := by rw [pow_add]
          _ = 276655542 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 1202644063) ^ 50110169 = 337195557 := by
        calc
          (5 : ZMod 1202644063) ^ 50110169 = (5 : ZMod 1202644063) ^ (25055084 + 25055084 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 25055084 * (5 : ZMod 1202644063) ^ 25055084) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 337195557 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 1202644063) ^ 100220338 = 827853742 := by
        calc
          (5 : ZMod 1202644063) ^ 100220338 = (5 : ZMod 1202644063) ^ (50110169 + 50110169) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 50110169 * (5 : ZMod 1202644063) ^ 50110169 := by rw [pow_add]
          _ = 827853742 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 1202644063) ^ 200440677 = 638496121 := by
        calc
          (5 : ZMod 1202644063) ^ 200440677 = (5 : ZMod 1202644063) ^ (100220338 + 100220338 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 100220338 * (5 : ZMod 1202644063) ^ 100220338) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 638496121 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 1202644063) ^ 400881354 = 638496120 := by
        calc
          (5 : ZMod 1202644063) ^ 400881354 = (5 : ZMod 1202644063) ^ (200440677 + 200440677) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 200440677 * (5 : ZMod 1202644063) ^ 200440677 := by rw [pow_add]
          _ = 638496120 := by rw [factor_1_27]; decide
      change (5 : ZMod 1202644063) ^ 400881354 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (5 : ZMod 1202644063) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 1202644063) ^ 3 = 125 := by
        calc
          (5 : ZMod 1202644063) ^ 3 = (5 : ZMod 1202644063) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 1 * (5 : ZMod 1202644063) ^ 1) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 1202644063) ^ 6 = 15625 := by
        calc
          (5 : ZMod 1202644063) ^ 6 = (5 : ZMod 1202644063) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 3 * (5 : ZMod 1202644063) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 1202644063) ^ 13 = 18059062 := by
        calc
          (5 : ZMod 1202644063) ^ 13 = (5 : ZMod 1202644063) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 6 * (5 : ZMod 1202644063) ^ 6) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 18059062 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 1202644063) ^ 27 = 353594402 := by
        calc
          (5 : ZMod 1202644063) ^ 27 = (5 : ZMod 1202644063) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 13 * (5 : ZMod 1202644063) ^ 13) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 353594402 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 1202644063) ^ 55 = 1131567667 := by
        calc
          (5 : ZMod 1202644063) ^ 55 = (5 : ZMod 1202644063) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 27 * (5 : ZMod 1202644063) ^ 27) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1131567667 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 1202644063) ^ 111 = 1187775961 := by
        calc
          (5 : ZMod 1202644063) ^ 111 = (5 : ZMod 1202644063) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 55 * (5 : ZMod 1202644063) ^ 55) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1187775961 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 1202644063) ^ 223 = 232871240 := by
        calc
          (5 : ZMod 1202644063) ^ 223 = (5 : ZMod 1202644063) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 111 * (5 : ZMod 1202644063) ^ 111) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 232871240 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 1202644063) ^ 447 = 1178204272 := by
        calc
          (5 : ZMod 1202644063) ^ 447 = (5 : ZMod 1202644063) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 223 * (5 : ZMod 1202644063) ^ 223) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1178204272 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 1202644063) ^ 895 = 540123009 := by
        calc
          (5 : ZMod 1202644063) ^ 895 = (5 : ZMod 1202644063) ^ (447 + 447 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 447 * (5 : ZMod 1202644063) ^ 447) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 540123009 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 1202644063) ^ 1790 = 814147528 := by
        calc
          (5 : ZMod 1202644063) ^ 1790 = (5 : ZMod 1202644063) ^ (895 + 895) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 895 * (5 : ZMod 1202644063) ^ 895 := by rw [pow_add]
          _ = 814147528 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 1202644063) ^ 3580 = 797785295 := by
        calc
          (5 : ZMod 1202644063) ^ 3580 = (5 : ZMod 1202644063) ^ (1790 + 1790) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 1790 * (5 : ZMod 1202644063) ^ 1790 := by rw [pow_add]
          _ = 797785295 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 1202644063) ^ 7161 = 128338479 := by
        calc
          (5 : ZMod 1202644063) ^ 7161 = (5 : ZMod 1202644063) ^ (3580 + 3580 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 3580 * (5 : ZMod 1202644063) ^ 3580) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 128338479 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 1202644063) ^ 14322 = 330335398 := by
        calc
          (5 : ZMod 1202644063) ^ 14322 = (5 : ZMod 1202644063) ^ (7161 + 7161) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 7161 * (5 : ZMod 1202644063) ^ 7161 := by rw [pow_add]
          _ = 330335398 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 1202644063) ^ 28645 = 147456672 := by
        calc
          (5 : ZMod 1202644063) ^ 28645 = (5 : ZMod 1202644063) ^ (14322 + 14322 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 14322 * (5 : ZMod 1202644063) ^ 14322) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 147456672 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 1202644063) ^ 57290 = 995969161 := by
        calc
          (5 : ZMod 1202644063) ^ 57290 = (5 : ZMod 1202644063) ^ (28645 + 28645) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 28645 * (5 : ZMod 1202644063) ^ 28645 := by rw [pow_add]
          _ = 995969161 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 1202644063) ^ 114581 = 192375092 := by
        calc
          (5 : ZMod 1202644063) ^ 114581 = (5 : ZMod 1202644063) ^ (57290 + 57290 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 57290 * (5 : ZMod 1202644063) ^ 57290) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 192375092 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 1202644063) ^ 229162 = 408458855 := by
        calc
          (5 : ZMod 1202644063) ^ 229162 = (5 : ZMod 1202644063) ^ (114581 + 114581) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 114581 * (5 : ZMod 1202644063) ^ 114581 := by rw [pow_add]
          _ = 408458855 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 1202644063) ^ 458324 = 948107761 := by
        calc
          (5 : ZMod 1202644063) ^ 458324 = (5 : ZMod 1202644063) ^ (229162 + 229162) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 229162 * (5 : ZMod 1202644063) ^ 229162 := by rw [pow_add]
          _ = 948107761 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 1202644063) ^ 916649 = 801629378 := by
        calc
          (5 : ZMod 1202644063) ^ 916649 = (5 : ZMod 1202644063) ^ (458324 + 458324 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 458324 * (5 : ZMod 1202644063) ^ 458324) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 801629378 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 1202644063) ^ 1833298 = 4659965 := by
        calc
          (5 : ZMod 1202644063) ^ 1833298 = (5 : ZMod 1202644063) ^ (916649 + 916649) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 916649 * (5 : ZMod 1202644063) ^ 916649 := by rw [pow_add]
          _ = 4659965 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 1202644063) ^ 3666597 = 460354422 := by
        calc
          (5 : ZMod 1202644063) ^ 3666597 = (5 : ZMod 1202644063) ^ (1833298 + 1833298 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 1833298 * (5 : ZMod 1202644063) ^ 1833298) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 460354422 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 1202644063) ^ 7333195 = 912378826 := by
        calc
          (5 : ZMod 1202644063) ^ 7333195 = (5 : ZMod 1202644063) ^ (3666597 + 3666597 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 3666597 * (5 : ZMod 1202644063) ^ 3666597) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 912378826 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 1202644063) ^ 14666391 = 849652466 := by
        calc
          (5 : ZMod 1202644063) ^ 14666391 = (5 : ZMod 1202644063) ^ (7333195 + 7333195 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 7333195 * (5 : ZMod 1202644063) ^ 7333195) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 849652466 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 1202644063) ^ 29332782 = 125643483 := by
        calc
          (5 : ZMod 1202644063) ^ 29332782 = (5 : ZMod 1202644063) ^ (14666391 + 14666391) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 14666391 * (5 : ZMod 1202644063) ^ 14666391 := by rw [pow_add]
          _ = 125643483 := by rw [factor_2_23]; decide
      change (5 : ZMod 1202644063) ^ 29332782 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (5 : ZMod 1202644063) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 1202644063) ^ 2 = 25 := by
        calc
          (5 : ZMod 1202644063) ^ 2 = (5 : ZMod 1202644063) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 1 * (5 : ZMod 1202644063) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 1202644063) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1202644063) ^ 5 = (5 : ZMod 1202644063) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 2 * (5 : ZMod 1202644063) ^ 2) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 1202644063) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 1202644063) ^ 11 = (5 : ZMod 1202644063) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 5 * (5 : ZMod 1202644063) ^ 5) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 1202644063) ^ 23 = 1099301367 := by
        calc
          (5 : ZMod 1202644063) ^ 23 = (5 : ZMod 1202644063) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 11 * (5 : ZMod 1202644063) ^ 11) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 1099301367 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 1202644063) ^ 46 = 224160194 := by
        calc
          (5 : ZMod 1202644063) ^ 46 = (5 : ZMod 1202644063) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 23 * (5 : ZMod 1202644063) ^ 23 := by rw [pow_add]
          _ = 224160194 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 1202644063) ^ 92 = 713508336 := by
        calc
          (5 : ZMod 1202644063) ^ 92 = (5 : ZMod 1202644063) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 46 * (5 : ZMod 1202644063) ^ 46 := by rw [pow_add]
          _ = 713508336 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 1202644063) ^ 184 = 887207696 := by
        calc
          (5 : ZMod 1202644063) ^ 184 = (5 : ZMod 1202644063) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 92 * (5 : ZMod 1202644063) ^ 92 := by rw [pow_add]
          _ = 887207696 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 1202644063) ^ 369 = 169051994 := by
        calc
          (5 : ZMod 1202644063) ^ 369 = (5 : ZMod 1202644063) ^ (184 + 184 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = ((5 : ZMod 1202644063) ^ 184 * (5 : ZMod 1202644063) ^ 184) * (5 : ZMod 1202644063) := by rw [pow_succ, pow_add]
          _ = 169051994 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 1202644063) ^ 738 = 286375413 := by
        calc
          (5 : ZMod 1202644063) ^ 738 = (5 : ZMod 1202644063) ^ (369 + 369) :=
            congrArg (fun n : ℕ => (5 : ZMod 1202644063) ^ n) (by norm_num)
          _ = (5 : ZMod 1202644063) ^ 369 * (5 : ZMod 1202644063) ^ 369 := by rw [pow_add]
          _ = 286375413 := by rw [factor_3_8]; decide
      change (5 : ZMod 1202644063) ^ 738 ≠ 1
      rw [factor_3_9]
      decide

#print axioms prime_lucas_1202644063

end TotientTailPeriodKiller
end Erdos249257
