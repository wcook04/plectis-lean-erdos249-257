import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1526482039 : Nat.Prime 1526482039 := by
  apply lucas_primality 1526482039 (3 : ZMod 1526482039)
  ·
      have fermat_0 : (3 : ZMod 1526482039) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 1526482039) ^ 2 = 9 := by
        calc
          (3 : ZMod 1526482039) ^ 2 = (3 : ZMod 1526482039) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 1 * (3 : ZMod 1526482039) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 1526482039) ^ 5 = 243 := by
        calc
          (3 : ZMod 1526482039) ^ 5 = (3 : ZMod 1526482039) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 2 * (3 : ZMod 1526482039) ^ 2) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 1526482039) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1526482039) ^ 11 = (3 : ZMod 1526482039) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 5 * (3 : ZMod 1526482039) ^ 5) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 1526482039) ^ 22 = 851418829 := by
        calc
          (3 : ZMod 1526482039) ^ 22 = (3 : ZMod 1526482039) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 11 * (3 : ZMod 1526482039) ^ 11 := by rw [pow_add]
          _ = 851418829 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 1526482039) ^ 45 = 1234776353 := by
        calc
          (3 : ZMod 1526482039) ^ 45 = (3 : ZMod 1526482039) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 22 * (3 : ZMod 1526482039) ^ 22) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1234776353 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 1526482039) ^ 90 = 95124791 := by
        calc
          (3 : ZMod 1526482039) ^ 90 = (3 : ZMod 1526482039) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 45 * (3 : ZMod 1526482039) ^ 45 := by rw [pow_add]
          _ = 95124791 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 1526482039) ^ 181 = 1039126972 := by
        calc
          (3 : ZMod 1526482039) ^ 181 = (3 : ZMod 1526482039) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 90 * (3 : ZMod 1526482039) ^ 90) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1039126972 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 1526482039) ^ 363 = 1451782094 := by
        calc
          (3 : ZMod 1526482039) ^ 363 = (3 : ZMod 1526482039) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 181 * (3 : ZMod 1526482039) ^ 181) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1451782094 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 1526482039) ^ 727 = 691249547 := by
        calc
          (3 : ZMod 1526482039) ^ 727 = (3 : ZMod 1526482039) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 363 * (3 : ZMod 1526482039) ^ 363) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 691249547 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 1526482039) ^ 1455 = 375215257 := by
        calc
          (3 : ZMod 1526482039) ^ 1455 = (3 : ZMod 1526482039) ^ (727 + 727 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 727 * (3 : ZMod 1526482039) ^ 727) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 375215257 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 1526482039) ^ 2911 = 301302921 := by
        calc
          (3 : ZMod 1526482039) ^ 2911 = (3 : ZMod 1526482039) ^ (1455 + 1455 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 1455 * (3 : ZMod 1526482039) ^ 1455) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 301302921 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 1526482039) ^ 5823 = 77687606 := by
        calc
          (3 : ZMod 1526482039) ^ 5823 = (3 : ZMod 1526482039) ^ (2911 + 2911 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 2911 * (3 : ZMod 1526482039) ^ 2911) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 77687606 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 1526482039) ^ 11646 = 655228089 := by
        calc
          (3 : ZMod 1526482039) ^ 11646 = (3 : ZMod 1526482039) ^ (5823 + 5823) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 5823 * (3 : ZMod 1526482039) ^ 5823 := by rw [pow_add]
          _ = 655228089 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 1526482039) ^ 23292 = 1219448148 := by
        calc
          (3 : ZMod 1526482039) ^ 23292 = (3 : ZMod 1526482039) ^ (11646 + 11646) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 11646 * (3 : ZMod 1526482039) ^ 11646 := by rw [pow_add]
          _ = 1219448148 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 1526482039) ^ 46584 = 748642053 := by
        calc
          (3 : ZMod 1526482039) ^ 46584 = (3 : ZMod 1526482039) ^ (23292 + 23292) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 23292 * (3 : ZMod 1526482039) ^ 23292 := by rw [pow_add]
          _ = 748642053 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 1526482039) ^ 93169 = 714200161 := by
        calc
          (3 : ZMod 1526482039) ^ 93169 = (3 : ZMod 1526482039) ^ (46584 + 46584 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 46584 * (3 : ZMod 1526482039) ^ 46584) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 714200161 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 1526482039) ^ 186338 = 148988174 := by
        calc
          (3 : ZMod 1526482039) ^ 186338 = (3 : ZMod 1526482039) ^ (93169 + 93169) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 93169 * (3 : ZMod 1526482039) ^ 93169 := by rw [pow_add]
          _ = 148988174 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 1526482039) ^ 372676 = 38352266 := by
        calc
          (3 : ZMod 1526482039) ^ 372676 = (3 : ZMod 1526482039) ^ (186338 + 186338) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 186338 * (3 : ZMod 1526482039) ^ 186338 := by rw [pow_add]
          _ = 38352266 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 1526482039) ^ 745352 = 1111784941 := by
        calc
          (3 : ZMod 1526482039) ^ 745352 = (3 : ZMod 1526482039) ^ (372676 + 372676) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 372676 * (3 : ZMod 1526482039) ^ 372676 := by rw [pow_add]
          _ = 1111784941 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 1526482039) ^ 1490705 = 972778237 := by
        calc
          (3 : ZMod 1526482039) ^ 1490705 = (3 : ZMod 1526482039) ^ (745352 + 745352 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 745352 * (3 : ZMod 1526482039) ^ 745352) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 972778237 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 1526482039) ^ 2981410 = 208302942 := by
        calc
          (3 : ZMod 1526482039) ^ 2981410 = (3 : ZMod 1526482039) ^ (1490705 + 1490705) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 1490705 * (3 : ZMod 1526482039) ^ 1490705 := by rw [pow_add]
          _ = 208302942 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 1526482039) ^ 5962820 = 1070663874 := by
        calc
          (3 : ZMod 1526482039) ^ 5962820 = (3 : ZMod 1526482039) ^ (2981410 + 2981410) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 2981410 * (3 : ZMod 1526482039) ^ 2981410 := by rw [pow_add]
          _ = 1070663874 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 1526482039) ^ 11925640 = 1083744622 := by
        calc
          (3 : ZMod 1526482039) ^ 11925640 = (3 : ZMod 1526482039) ^ (5962820 + 5962820) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 5962820 * (3 : ZMod 1526482039) ^ 5962820 := by rw [pow_add]
          _ = 1083744622 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 1526482039) ^ 23851281 = 1017433640 := by
        calc
          (3 : ZMod 1526482039) ^ 23851281 = (3 : ZMod 1526482039) ^ (11925640 + 11925640 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 11925640 * (3 : ZMod 1526482039) ^ 11925640) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1017433640 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 1526482039) ^ 47702563 = 1068223270 := by
        calc
          (3 : ZMod 1526482039) ^ 47702563 = (3 : ZMod 1526482039) ^ (23851281 + 23851281 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 23851281 * (3 : ZMod 1526482039) ^ 23851281) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1068223270 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 1526482039) ^ 95405127 = 969654830 := by
        calc
          (3 : ZMod 1526482039) ^ 95405127 = (3 : ZMod 1526482039) ^ (47702563 + 47702563 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 47702563 * (3 : ZMod 1526482039) ^ 47702563) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 969654830 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 1526482039) ^ 190810254 = 139737329 := by
        calc
          (3 : ZMod 1526482039) ^ 190810254 = (3 : ZMod 1526482039) ^ (95405127 + 95405127) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 95405127 * (3 : ZMod 1526482039) ^ 95405127 := by rw [pow_add]
          _ = 139737329 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 1526482039) ^ 381620509 = 1486610936 := by
        calc
          (3 : ZMod 1526482039) ^ 381620509 = (3 : ZMod 1526482039) ^ (190810254 + 190810254 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 190810254 * (3 : ZMod 1526482039) ^ 190810254) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1486610936 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 1526482039) ^ 763241019 = 1526482038 := by
        calc
          (3 : ZMod 1526482039) ^ 763241019 = (3 : ZMod 1526482039) ^ (381620509 + 381620509 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 381620509 * (3 : ZMod 1526482039) ^ 381620509) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1526482038 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 1526482039) ^ 1526482038 = 1 := by
        calc
          (3 : ZMod 1526482039) ^ 1526482038 = (3 : ZMod 1526482039) ^ (763241019 + 763241019) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 763241019 * (3 : ZMod 1526482039) ^ 763241019 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (67, 1), (3797219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (67, 1), (3797219, 1)] : List FactorBlock).map factorBlockValue).prod = 1526482039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 1526482039) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 1526482039) ^ 2 = 9 := by
        calc
          (3 : ZMod 1526482039) ^ 2 = (3 : ZMod 1526482039) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 1 * (3 : ZMod 1526482039) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 1526482039) ^ 5 = 243 := by
        calc
          (3 : ZMod 1526482039) ^ 5 = (3 : ZMod 1526482039) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 2 * (3 : ZMod 1526482039) ^ 2) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 1526482039) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1526482039) ^ 11 = (3 : ZMod 1526482039) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 5 * (3 : ZMod 1526482039) ^ 5) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 1526482039) ^ 22 = 851418829 := by
        calc
          (3 : ZMod 1526482039) ^ 22 = (3 : ZMod 1526482039) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 11 * (3 : ZMod 1526482039) ^ 11 := by rw [pow_add]
          _ = 851418829 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 1526482039) ^ 45 = 1234776353 := by
        calc
          (3 : ZMod 1526482039) ^ 45 = (3 : ZMod 1526482039) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 22 * (3 : ZMod 1526482039) ^ 22) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1234776353 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 1526482039) ^ 90 = 95124791 := by
        calc
          (3 : ZMod 1526482039) ^ 90 = (3 : ZMod 1526482039) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 45 * (3 : ZMod 1526482039) ^ 45 := by rw [pow_add]
          _ = 95124791 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 1526482039) ^ 181 = 1039126972 := by
        calc
          (3 : ZMod 1526482039) ^ 181 = (3 : ZMod 1526482039) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 90 * (3 : ZMod 1526482039) ^ 90) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1039126972 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 1526482039) ^ 363 = 1451782094 := by
        calc
          (3 : ZMod 1526482039) ^ 363 = (3 : ZMod 1526482039) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 181 * (3 : ZMod 1526482039) ^ 181) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1451782094 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 1526482039) ^ 727 = 691249547 := by
        calc
          (3 : ZMod 1526482039) ^ 727 = (3 : ZMod 1526482039) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 363 * (3 : ZMod 1526482039) ^ 363) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 691249547 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 1526482039) ^ 1455 = 375215257 := by
        calc
          (3 : ZMod 1526482039) ^ 1455 = (3 : ZMod 1526482039) ^ (727 + 727 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 727 * (3 : ZMod 1526482039) ^ 727) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 375215257 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 1526482039) ^ 2911 = 301302921 := by
        calc
          (3 : ZMod 1526482039) ^ 2911 = (3 : ZMod 1526482039) ^ (1455 + 1455 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 1455 * (3 : ZMod 1526482039) ^ 1455) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 301302921 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 1526482039) ^ 5823 = 77687606 := by
        calc
          (3 : ZMod 1526482039) ^ 5823 = (3 : ZMod 1526482039) ^ (2911 + 2911 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 2911 * (3 : ZMod 1526482039) ^ 2911) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 77687606 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 1526482039) ^ 11646 = 655228089 := by
        calc
          (3 : ZMod 1526482039) ^ 11646 = (3 : ZMod 1526482039) ^ (5823 + 5823) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 5823 * (3 : ZMod 1526482039) ^ 5823 := by rw [pow_add]
          _ = 655228089 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 1526482039) ^ 23292 = 1219448148 := by
        calc
          (3 : ZMod 1526482039) ^ 23292 = (3 : ZMod 1526482039) ^ (11646 + 11646) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 11646 * (3 : ZMod 1526482039) ^ 11646 := by rw [pow_add]
          _ = 1219448148 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 1526482039) ^ 46584 = 748642053 := by
        calc
          (3 : ZMod 1526482039) ^ 46584 = (3 : ZMod 1526482039) ^ (23292 + 23292) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 23292 * (3 : ZMod 1526482039) ^ 23292 := by rw [pow_add]
          _ = 748642053 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 1526482039) ^ 93169 = 714200161 := by
        calc
          (3 : ZMod 1526482039) ^ 93169 = (3 : ZMod 1526482039) ^ (46584 + 46584 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 46584 * (3 : ZMod 1526482039) ^ 46584) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 714200161 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 1526482039) ^ 186338 = 148988174 := by
        calc
          (3 : ZMod 1526482039) ^ 186338 = (3 : ZMod 1526482039) ^ (93169 + 93169) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 93169 * (3 : ZMod 1526482039) ^ 93169 := by rw [pow_add]
          _ = 148988174 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 1526482039) ^ 372676 = 38352266 := by
        calc
          (3 : ZMod 1526482039) ^ 372676 = (3 : ZMod 1526482039) ^ (186338 + 186338) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 186338 * (3 : ZMod 1526482039) ^ 186338 := by rw [pow_add]
          _ = 38352266 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 1526482039) ^ 745352 = 1111784941 := by
        calc
          (3 : ZMod 1526482039) ^ 745352 = (3 : ZMod 1526482039) ^ (372676 + 372676) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 372676 * (3 : ZMod 1526482039) ^ 372676 := by rw [pow_add]
          _ = 1111784941 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 1526482039) ^ 1490705 = 972778237 := by
        calc
          (3 : ZMod 1526482039) ^ 1490705 = (3 : ZMod 1526482039) ^ (745352 + 745352 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 745352 * (3 : ZMod 1526482039) ^ 745352) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 972778237 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 1526482039) ^ 2981410 = 208302942 := by
        calc
          (3 : ZMod 1526482039) ^ 2981410 = (3 : ZMod 1526482039) ^ (1490705 + 1490705) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 1490705 * (3 : ZMod 1526482039) ^ 1490705 := by rw [pow_add]
          _ = 208302942 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 1526482039) ^ 5962820 = 1070663874 := by
        calc
          (3 : ZMod 1526482039) ^ 5962820 = (3 : ZMod 1526482039) ^ (2981410 + 2981410) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 2981410 * (3 : ZMod 1526482039) ^ 2981410 := by rw [pow_add]
          _ = 1070663874 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 1526482039) ^ 11925640 = 1083744622 := by
        calc
          (3 : ZMod 1526482039) ^ 11925640 = (3 : ZMod 1526482039) ^ (5962820 + 5962820) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 5962820 * (3 : ZMod 1526482039) ^ 5962820 := by rw [pow_add]
          _ = 1083744622 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 1526482039) ^ 23851281 = 1017433640 := by
        calc
          (3 : ZMod 1526482039) ^ 23851281 = (3 : ZMod 1526482039) ^ (11925640 + 11925640 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 11925640 * (3 : ZMod 1526482039) ^ 11925640) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1017433640 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 1526482039) ^ 47702563 = 1068223270 := by
        calc
          (3 : ZMod 1526482039) ^ 47702563 = (3 : ZMod 1526482039) ^ (23851281 + 23851281 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 23851281 * (3 : ZMod 1526482039) ^ 23851281) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1068223270 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 1526482039) ^ 95405127 = 969654830 := by
        calc
          (3 : ZMod 1526482039) ^ 95405127 = (3 : ZMod 1526482039) ^ (47702563 + 47702563 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 47702563 * (3 : ZMod 1526482039) ^ 47702563) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 969654830 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 1526482039) ^ 190810254 = 139737329 := by
        calc
          (3 : ZMod 1526482039) ^ 190810254 = (3 : ZMod 1526482039) ^ (95405127 + 95405127) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 95405127 * (3 : ZMod 1526482039) ^ 95405127 := by rw [pow_add]
          _ = 139737329 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 1526482039) ^ 381620509 = 1486610936 := by
        calc
          (3 : ZMod 1526482039) ^ 381620509 = (3 : ZMod 1526482039) ^ (190810254 + 190810254 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 190810254 * (3 : ZMod 1526482039) ^ 190810254) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1486610936 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 1526482039) ^ 763241019 = 1526482038 := by
        calc
          (3 : ZMod 1526482039) ^ 763241019 = (3 : ZMod 1526482039) ^ (381620509 + 381620509 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 381620509 * (3 : ZMod 1526482039) ^ 381620509) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1526482038 := by rw [factor_0_28]; decide
      change (3 : ZMod 1526482039) ^ 763241019 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (3 : ZMod 1526482039) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 1526482039) ^ 3 = 27 := by
        calc
          (3 : ZMod 1526482039) ^ 3 = (3 : ZMod 1526482039) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 1 * (3 : ZMod 1526482039) ^ 1) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 1526482039) ^ 7 = 2187 := by
        calc
          (3 : ZMod 1526482039) ^ 7 = (3 : ZMod 1526482039) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 3 * (3 : ZMod 1526482039) ^ 3) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 1526482039) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 1526482039) ^ 15 = (3 : ZMod 1526482039) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 7 * (3 : ZMod 1526482039) ^ 7) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 1526482039) ^ 30 = 761156368 := by
        calc
          (3 : ZMod 1526482039) ^ 30 = (3 : ZMod 1526482039) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 15 * (3 : ZMod 1526482039) ^ 15 := by rw [pow_add]
          _ = 761156368 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 1526482039) ^ 60 = 259131929 := by
        calc
          (3 : ZMod 1526482039) ^ 60 = (3 : ZMod 1526482039) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 30 * (3 : ZMod 1526482039) ^ 30 := by rw [pow_add]
          _ = 259131929 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 1526482039) ^ 121 = 1334672246 := by
        calc
          (3 : ZMod 1526482039) ^ 121 = (3 : ZMod 1526482039) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 60 * (3 : ZMod 1526482039) ^ 60) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1334672246 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 1526482039) ^ 242 = 1353491869 := by
        calc
          (3 : ZMod 1526482039) ^ 242 = (3 : ZMod 1526482039) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 121 * (3 : ZMod 1526482039) ^ 121 := by rw [pow_add]
          _ = 1353491869 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 1526482039) ^ 485 = 926916614 := by
        calc
          (3 : ZMod 1526482039) ^ 485 = (3 : ZMod 1526482039) ^ (242 + 242 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 242 * (3 : ZMod 1526482039) ^ 242) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 926916614 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 1526482039) ^ 970 = 364898461 := by
        calc
          (3 : ZMod 1526482039) ^ 970 = (3 : ZMod 1526482039) ^ (485 + 485) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 485 * (3 : ZMod 1526482039) ^ 485 := by rw [pow_add]
          _ = 364898461 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 1526482039) ^ 1941 = 1298393023 := by
        calc
          (3 : ZMod 1526482039) ^ 1941 = (3 : ZMod 1526482039) ^ (970 + 970 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 970 * (3 : ZMod 1526482039) ^ 970) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1298393023 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 1526482039) ^ 3882 = 50334826 := by
        calc
          (3 : ZMod 1526482039) ^ 3882 = (3 : ZMod 1526482039) ^ (1941 + 1941) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 1941 * (3 : ZMod 1526482039) ^ 1941 := by rw [pow_add]
          _ = 50334826 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 1526482039) ^ 7764 = 879399636 := by
        calc
          (3 : ZMod 1526482039) ^ 7764 = (3 : ZMod 1526482039) ^ (3882 + 3882) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 3882 * (3 : ZMod 1526482039) ^ 3882 := by rw [pow_add]
          _ = 879399636 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 1526482039) ^ 15528 = 1009521225 := by
        calc
          (3 : ZMod 1526482039) ^ 15528 = (3 : ZMod 1526482039) ^ (7764 + 7764) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 7764 * (3 : ZMod 1526482039) ^ 7764 := by rw [pow_add]
          _ = 1009521225 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 1526482039) ^ 31056 = 483378800 := by
        calc
          (3 : ZMod 1526482039) ^ 31056 = (3 : ZMod 1526482039) ^ (15528 + 15528) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 15528 * (3 : ZMod 1526482039) ^ 15528 := by rw [pow_add]
          _ = 483378800 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 1526482039) ^ 62112 = 18040480 := by
        calc
          (3 : ZMod 1526482039) ^ 62112 = (3 : ZMod 1526482039) ^ (31056 + 31056) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 31056 * (3 : ZMod 1526482039) ^ 31056 := by rw [pow_add]
          _ = 18040480 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 1526482039) ^ 124225 = 681695825 := by
        calc
          (3 : ZMod 1526482039) ^ 124225 = (3 : ZMod 1526482039) ^ (62112 + 62112 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 62112 * (3 : ZMod 1526482039) ^ 62112) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 681695825 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 1526482039) ^ 248450 = 810868632 := by
        calc
          (3 : ZMod 1526482039) ^ 248450 = (3 : ZMod 1526482039) ^ (124225 + 124225) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 124225 * (3 : ZMod 1526482039) ^ 124225 := by rw [pow_add]
          _ = 810868632 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 1526482039) ^ 496901 = 1199161151 := by
        calc
          (3 : ZMod 1526482039) ^ 496901 = (3 : ZMod 1526482039) ^ (248450 + 248450 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 248450 * (3 : ZMod 1526482039) ^ 248450) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1199161151 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 1526482039) ^ 993803 = 1098774377 := by
        calc
          (3 : ZMod 1526482039) ^ 993803 = (3 : ZMod 1526482039) ^ (496901 + 496901 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 496901 * (3 : ZMod 1526482039) ^ 496901) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1098774377 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 1526482039) ^ 1987606 = 1501512238 := by
        calc
          (3 : ZMod 1526482039) ^ 1987606 = (3 : ZMod 1526482039) ^ (993803 + 993803) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 993803 * (3 : ZMod 1526482039) ^ 993803 := by rw [pow_add]
          _ = 1501512238 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 1526482039) ^ 3975213 = 1172414231 := by
        calc
          (3 : ZMod 1526482039) ^ 3975213 = (3 : ZMod 1526482039) ^ (1987606 + 1987606 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 1987606 * (3 : ZMod 1526482039) ^ 1987606) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1172414231 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 1526482039) ^ 7950427 = 448277204 := by
        calc
          (3 : ZMod 1526482039) ^ 7950427 = (3 : ZMod 1526482039) ^ (3975213 + 3975213 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 3975213 * (3 : ZMod 1526482039) ^ 3975213) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 448277204 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 1526482039) ^ 15900854 = 1267369259 := by
        calc
          (3 : ZMod 1526482039) ^ 15900854 = (3 : ZMod 1526482039) ^ (7950427 + 7950427) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 7950427 * (3 : ZMod 1526482039) ^ 7950427 := by rw [pow_add]
          _ = 1267369259 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 1526482039) ^ 31801709 = 710080940 := by
        calc
          (3 : ZMod 1526482039) ^ 31801709 = (3 : ZMod 1526482039) ^ (15900854 + 15900854 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 15900854 * (3 : ZMod 1526482039) ^ 15900854) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 710080940 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 1526482039) ^ 63603418 = 1443963701 := by
        calc
          (3 : ZMod 1526482039) ^ 63603418 = (3 : ZMod 1526482039) ^ (31801709 + 31801709) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 31801709 * (3 : ZMod 1526482039) ^ 31801709 := by rw [pow_add]
          _ = 1443963701 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 1526482039) ^ 127206836 = 1506546487 := by
        calc
          (3 : ZMod 1526482039) ^ 127206836 = (3 : ZMod 1526482039) ^ (63603418 + 63603418) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 63603418 * (3 : ZMod 1526482039) ^ 63603418 := by rw [pow_add]
          _ = 1506546487 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 1526482039) ^ 254413673 = 59806655 := by
        calc
          (3 : ZMod 1526482039) ^ 254413673 = (3 : ZMod 1526482039) ^ (127206836 + 127206836 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 127206836 * (3 : ZMod 1526482039) ^ 127206836) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 59806655 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 1526482039) ^ 508827346 = 59806654 := by
        calc
          (3 : ZMod 1526482039) ^ 508827346 = (3 : ZMod 1526482039) ^ (254413673 + 254413673) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 254413673 * (3 : ZMod 1526482039) ^ 254413673 := by rw [pow_add]
          _ = 59806654 := by rw [factor_1_27]; decide
      change (3 : ZMod 1526482039) ^ 508827346 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (3 : ZMod 1526482039) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 1526482039) ^ 2 = 9 := by
        calc
          (3 : ZMod 1526482039) ^ 2 = (3 : ZMod 1526482039) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 1 * (3 : ZMod 1526482039) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 1526482039) ^ 5 = 243 := by
        calc
          (3 : ZMod 1526482039) ^ 5 = (3 : ZMod 1526482039) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 2 * (3 : ZMod 1526482039) ^ 2) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 1526482039) ^ 10 = 59049 := by
        calc
          (3 : ZMod 1526482039) ^ 10 = (3 : ZMod 1526482039) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 5 * (3 : ZMod 1526482039) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 1526482039) ^ 21 = 1301460969 := by
        calc
          (3 : ZMod 1526482039) ^ 21 = (3 : ZMod 1526482039) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 10 * (3 : ZMod 1526482039) ^ 10) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1301460969 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 1526482039) ^ 43 = 306806488 := by
        calc
          (3 : ZMod 1526482039) ^ 43 = (3 : ZMod 1526482039) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 21 * (3 : ZMod 1526482039) ^ 21) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 306806488 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 1526482039) ^ 86 = 754992671 := by
        calc
          (3 : ZMod 1526482039) ^ 86 = (3 : ZMod 1526482039) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 43 * (3 : ZMod 1526482039) ^ 43 := by rw [pow_add]
          _ = 754992671 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 1526482039) ^ 173 = 990359196 := by
        calc
          (3 : ZMod 1526482039) ^ 173 = (3 : ZMod 1526482039) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 86 * (3 : ZMod 1526482039) ^ 86) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 990359196 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 1526482039) ^ 347 = 424673444 := by
        calc
          (3 : ZMod 1526482039) ^ 347 = (3 : ZMod 1526482039) ^ (173 + 173 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 173 * (3 : ZMod 1526482039) ^ 173) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 424673444 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 1526482039) ^ 695 = 773355749 := by
        calc
          (3 : ZMod 1526482039) ^ 695 = (3 : ZMod 1526482039) ^ (347 + 347 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 347 * (3 : ZMod 1526482039) ^ 347) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 773355749 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 1526482039) ^ 1390 = 255260822 := by
        calc
          (3 : ZMod 1526482039) ^ 1390 = (3 : ZMod 1526482039) ^ (695 + 695) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 695 * (3 : ZMod 1526482039) ^ 695 := by rw [pow_add]
          _ = 255260822 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 1526482039) ^ 2781 = 1279796647 := by
        calc
          (3 : ZMod 1526482039) ^ 2781 = (3 : ZMod 1526482039) ^ (1390 + 1390 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 1390 * (3 : ZMod 1526482039) ^ 1390) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1279796647 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 1526482039) ^ 5562 = 1405544535 := by
        calc
          (3 : ZMod 1526482039) ^ 5562 = (3 : ZMod 1526482039) ^ (2781 + 2781) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 2781 * (3 : ZMod 1526482039) ^ 2781 := by rw [pow_add]
          _ = 1405544535 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 1526482039) ^ 11124 = 597296285 := by
        calc
          (3 : ZMod 1526482039) ^ 11124 = (3 : ZMod 1526482039) ^ (5562 + 5562) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 5562 * (3 : ZMod 1526482039) ^ 5562 := by rw [pow_add]
          _ = 597296285 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 1526482039) ^ 22249 = 629652201 := by
        calc
          (3 : ZMod 1526482039) ^ 22249 = (3 : ZMod 1526482039) ^ (11124 + 11124 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 11124 * (3 : ZMod 1526482039) ^ 11124) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 629652201 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 1526482039) ^ 44498 = 1042870767 := by
        calc
          (3 : ZMod 1526482039) ^ 44498 = (3 : ZMod 1526482039) ^ (22249 + 22249) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 22249 * (3 : ZMod 1526482039) ^ 22249 := by rw [pow_add]
          _ = 1042870767 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 1526482039) ^ 88997 = 743273348 := by
        calc
          (3 : ZMod 1526482039) ^ 88997 = (3 : ZMod 1526482039) ^ (44498 + 44498 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 44498 * (3 : ZMod 1526482039) ^ 44498) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 743273348 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 1526482039) ^ 177994 = 337057856 := by
        calc
          (3 : ZMod 1526482039) ^ 177994 = (3 : ZMod 1526482039) ^ (88997 + 88997) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 88997 * (3 : ZMod 1526482039) ^ 88997 := by rw [pow_add]
          _ = 337057856 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 1526482039) ^ 355989 = 1387620007 := by
        calc
          (3 : ZMod 1526482039) ^ 355989 = (3 : ZMod 1526482039) ^ (177994 + 177994 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 177994 * (3 : ZMod 1526482039) ^ 177994) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1387620007 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 1526482039) ^ 711978 = 851691397 := by
        calc
          (3 : ZMod 1526482039) ^ 711978 = (3 : ZMod 1526482039) ^ (355989 + 355989) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 355989 * (3 : ZMod 1526482039) ^ 355989 := by rw [pow_add]
          _ = 851691397 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 1526482039) ^ 1423957 = 1185196977 := by
        calc
          (3 : ZMod 1526482039) ^ 1423957 = (3 : ZMod 1526482039) ^ (711978 + 711978 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 711978 * (3 : ZMod 1526482039) ^ 711978) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1185196977 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 1526482039) ^ 2847914 = 222960303 := by
        calc
          (3 : ZMod 1526482039) ^ 2847914 = (3 : ZMod 1526482039) ^ (1423957 + 1423957) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 1423957 * (3 : ZMod 1526482039) ^ 1423957 := by rw [pow_add]
          _ = 222960303 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 1526482039) ^ 5695828 = 170894812 := by
        calc
          (3 : ZMod 1526482039) ^ 5695828 = (3 : ZMod 1526482039) ^ (2847914 + 2847914) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 2847914 * (3 : ZMod 1526482039) ^ 2847914 := by rw [pow_add]
          _ = 170894812 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 1526482039) ^ 11391657 = 807090743 := by
        calc
          (3 : ZMod 1526482039) ^ 11391657 = (3 : ZMod 1526482039) ^ (5695828 + 5695828 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 5695828 * (3 : ZMod 1526482039) ^ 5695828) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 807090743 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 1526482039) ^ 22783314 = 641307509 := by
        calc
          (3 : ZMod 1526482039) ^ 22783314 = (3 : ZMod 1526482039) ^ (11391657 + 11391657) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 11391657 * (3 : ZMod 1526482039) ^ 11391657 := by rw [pow_add]
          _ = 641307509 := by rw [factor_2_23]; decide
      change (3 : ZMod 1526482039) ^ 22783314 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (3 : ZMod 1526482039) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 1526482039) ^ 3 = 27 := by
        calc
          (3 : ZMod 1526482039) ^ 3 = (3 : ZMod 1526482039) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 1 * (3 : ZMod 1526482039) ^ 1) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 1526482039) ^ 6 = 729 := by
        calc
          (3 : ZMod 1526482039) ^ 6 = (3 : ZMod 1526482039) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 3 * (3 : ZMod 1526482039) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 1526482039) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1526482039) ^ 12 = (3 : ZMod 1526482039) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 6 * (3 : ZMod 1526482039) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 1526482039) ^ 25 = 91077798 := by
        calc
          (3 : ZMod 1526482039) ^ 25 = (3 : ZMod 1526482039) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 12 * (3 : ZMod 1526482039) ^ 12) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 91077798 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 1526482039) ^ 50 = 860174135 := by
        calc
          (3 : ZMod 1526482039) ^ 50 = (3 : ZMod 1526482039) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 25 * (3 : ZMod 1526482039) ^ 25 := by rw [pow_add]
          _ = 860174135 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 1526482039) ^ 100 = 1096362278 := by
        calc
          (3 : ZMod 1526482039) ^ 100 = (3 : ZMod 1526482039) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 50 * (3 : ZMod 1526482039) ^ 50 := by rw [pow_add]
          _ = 1096362278 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 1526482039) ^ 201 = 1294198363 := by
        calc
          (3 : ZMod 1526482039) ^ 201 = (3 : ZMod 1526482039) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = ((3 : ZMod 1526482039) ^ 100 * (3 : ZMod 1526482039) ^ 100) * (3 : ZMod 1526482039) := by rw [pow_succ, pow_add]
          _ = 1294198363 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 1526482039) ^ 402 = 333481816 := by
        calc
          (3 : ZMod 1526482039) ^ 402 = (3 : ZMod 1526482039) ^ (201 + 201) :=
            congrArg (fun n : ℕ => (3 : ZMod 1526482039) ^ n) (by norm_num)
          _ = (3 : ZMod 1526482039) ^ 201 * (3 : ZMod 1526482039) ^ 201 := by rw [pow_add]
          _ = 333481816 := by rw [factor_3_7]; decide
      change (3 : ZMod 1526482039) ^ 402 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_1526482039

end TotientTailPeriodKiller
end Erdos249257
