import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_36750397 : Nat.Prime 36750397 := by
  apply lucas_primality 36750397 (7 : ZMod 36750397)
  ·
      have fermat_0 : (7 : ZMod 36750397) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 36750397) ^ 2 = 49 := by
        calc
          (7 : ZMod 36750397) ^ 2 = (7 : ZMod 36750397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 1 * (7 : ZMod 36750397) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 36750397) ^ 4 = 2401 := by
        calc
          (7 : ZMod 36750397) ^ 4 = (7 : ZMod 36750397) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 2 * (7 : ZMod 36750397) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 36750397) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 36750397) ^ 8 = (7 : ZMod 36750397) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 4 * (7 : ZMod 36750397) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 36750397) ^ 17 = 23222046 := by
        calc
          (7 : ZMod 36750397) ^ 17 = (7 : ZMod 36750397) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 8 * (7 : ZMod 36750397) ^ 8) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 23222046 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 36750397) ^ 35 = 13837208 := by
        calc
          (7 : ZMod 36750397) ^ 35 = (7 : ZMod 36750397) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 17 * (7 : ZMod 36750397) ^ 17) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 13837208 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 36750397) ^ 70 = 6378762 := by
        calc
          (7 : ZMod 36750397) ^ 70 = (7 : ZMod 36750397) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 35 * (7 : ZMod 36750397) ^ 35 := by rw [pow_add]
          _ = 6378762 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 36750397) ^ 140 = 35110124 := by
        calc
          (7 : ZMod 36750397) ^ 140 = (7 : ZMod 36750397) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 70 * (7 : ZMod 36750397) ^ 70 := by rw [pow_add]
          _ = 35110124 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 36750397) ^ 280 = 35700556 := by
        calc
          (7 : ZMod 36750397) ^ 280 = (7 : ZMod 36750397) ^ (140 + 140) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 140 * (7 : ZMod 36750397) ^ 140 := by rw [pow_add]
          _ = 35700556 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 36750397) ^ 560 = 21719251 := by
        calc
          (7 : ZMod 36750397) ^ 560 = (7 : ZMod 36750397) ^ (280 + 280) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 280 * (7 : ZMod 36750397) ^ 280 := by rw [pow_add]
          _ = 21719251 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 36750397) ^ 1121 = 32432129 := by
        calc
          (7 : ZMod 36750397) ^ 1121 = (7 : ZMod 36750397) ^ (560 + 560 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 560 * (7 : ZMod 36750397) ^ 560) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 32432129 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 36750397) ^ 2243 = 25052730 := by
        calc
          (7 : ZMod 36750397) ^ 2243 = (7 : ZMod 36750397) ^ (1121 + 1121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 1121 * (7 : ZMod 36750397) ^ 1121) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 25052730 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 36750397) ^ 4486 = 14064205 := by
        calc
          (7 : ZMod 36750397) ^ 4486 = (7 : ZMod 36750397) ^ (2243 + 2243) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 2243 * (7 : ZMod 36750397) ^ 2243 := by rw [pow_add]
          _ = 14064205 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 36750397) ^ 8972 = 16756940 := by
        calc
          (7 : ZMod 36750397) ^ 8972 = (7 : ZMod 36750397) ^ (4486 + 4486) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 4486 * (7 : ZMod 36750397) ^ 4486 := by rw [pow_add]
          _ = 16756940 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 36750397) ^ 17944 = 28346194 := by
        calc
          (7 : ZMod 36750397) ^ 17944 = (7 : ZMod 36750397) ^ (8972 + 8972) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 8972 * (7 : ZMod 36750397) ^ 8972 := by rw [pow_add]
          _ = 28346194 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 36750397) ^ 35889 = 23243584 := by
        calc
          (7 : ZMod 36750397) ^ 35889 = (7 : ZMod 36750397) ^ (17944 + 17944 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 17944 * (7 : ZMod 36750397) ^ 17944) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 23243584 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 36750397) ^ 71778 = 28654977 := by
        calc
          (7 : ZMod 36750397) ^ 71778 = (7 : ZMod 36750397) ^ (35889 + 35889) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 35889 * (7 : ZMod 36750397) ^ 35889 := by rw [pow_add]
          _ = 28654977 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 36750397) ^ 143556 = 18019004 := by
        calc
          (7 : ZMod 36750397) ^ 143556 = (7 : ZMod 36750397) ^ (71778 + 71778) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 71778 * (7 : ZMod 36750397) ^ 71778 := by rw [pow_add]
          _ = 18019004 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 36750397) ^ 287112 = 2963787 := by
        calc
          (7 : ZMod 36750397) ^ 287112 = (7 : ZMod 36750397) ^ (143556 + 143556) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 143556 * (7 : ZMod 36750397) ^ 143556 := by rw [pow_add]
          _ = 2963787 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 36750397) ^ 574224 = 26991223 := by
        calc
          (7 : ZMod 36750397) ^ 574224 = (7 : ZMod 36750397) ^ (287112 + 287112) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 287112 * (7 : ZMod 36750397) ^ 287112 := by rw [pow_add]
          _ = 26991223 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 36750397) ^ 1148449 = 28394243 := by
        calc
          (7 : ZMod 36750397) ^ 1148449 = (7 : ZMod 36750397) ^ (574224 + 574224 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 574224 * (7 : ZMod 36750397) ^ 574224) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 28394243 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 36750397) ^ 2296899 = 11385757 := by
        calc
          (7 : ZMod 36750397) ^ 2296899 = (7 : ZMod 36750397) ^ (1148449 + 1148449 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 1148449 * (7 : ZMod 36750397) ^ 1148449) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 11385757 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 36750397) ^ 4593799 = 10937149 := by
        calc
          (7 : ZMod 36750397) ^ 4593799 = (7 : ZMod 36750397) ^ (2296899 + 2296899 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 2296899 * (7 : ZMod 36750397) ^ 2296899) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 10937149 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 36750397) ^ 9187599 = 26442054 := by
        calc
          (7 : ZMod 36750397) ^ 9187599 = (7 : ZMod 36750397) ^ (4593799 + 4593799 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 4593799 * (7 : ZMod 36750397) ^ 4593799) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 26442054 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 36750397) ^ 18375198 = 36750396 := by
        calc
          (7 : ZMod 36750397) ^ 18375198 = (7 : ZMod 36750397) ^ (9187599 + 9187599) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 9187599 * (7 : ZMod 36750397) ^ 9187599 := by rw [pow_add]
          _ = 36750396 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 36750397) ^ 36750396 = 1 := by
        calc
          (7 : ZMod 36750397) ^ 36750396 = (7 : ZMod 36750397) ^ (18375198 + 18375198) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 18375198 * (7 : ZMod 36750397) ^ 18375198 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 2), (10597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 2), (10597, 1)] : List FactorBlock).map factorBlockValue).prod = 36750397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 36750397) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 36750397) ^ 2 = 49 := by
        calc
          (7 : ZMod 36750397) ^ 2 = (7 : ZMod 36750397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 1 * (7 : ZMod 36750397) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 36750397) ^ 4 = 2401 := by
        calc
          (7 : ZMod 36750397) ^ 4 = (7 : ZMod 36750397) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 2 * (7 : ZMod 36750397) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 36750397) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 36750397) ^ 8 = (7 : ZMod 36750397) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 4 * (7 : ZMod 36750397) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 36750397) ^ 17 = 23222046 := by
        calc
          (7 : ZMod 36750397) ^ 17 = (7 : ZMod 36750397) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 8 * (7 : ZMod 36750397) ^ 8) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 23222046 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 36750397) ^ 35 = 13837208 := by
        calc
          (7 : ZMod 36750397) ^ 35 = (7 : ZMod 36750397) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 17 * (7 : ZMod 36750397) ^ 17) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 13837208 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 36750397) ^ 70 = 6378762 := by
        calc
          (7 : ZMod 36750397) ^ 70 = (7 : ZMod 36750397) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 35 * (7 : ZMod 36750397) ^ 35 := by rw [pow_add]
          _ = 6378762 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 36750397) ^ 140 = 35110124 := by
        calc
          (7 : ZMod 36750397) ^ 140 = (7 : ZMod 36750397) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 70 * (7 : ZMod 36750397) ^ 70 := by rw [pow_add]
          _ = 35110124 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 36750397) ^ 280 = 35700556 := by
        calc
          (7 : ZMod 36750397) ^ 280 = (7 : ZMod 36750397) ^ (140 + 140) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 140 * (7 : ZMod 36750397) ^ 140 := by rw [pow_add]
          _ = 35700556 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 36750397) ^ 560 = 21719251 := by
        calc
          (7 : ZMod 36750397) ^ 560 = (7 : ZMod 36750397) ^ (280 + 280) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 280 * (7 : ZMod 36750397) ^ 280 := by rw [pow_add]
          _ = 21719251 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 36750397) ^ 1121 = 32432129 := by
        calc
          (7 : ZMod 36750397) ^ 1121 = (7 : ZMod 36750397) ^ (560 + 560 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 560 * (7 : ZMod 36750397) ^ 560) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 32432129 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 36750397) ^ 2243 = 25052730 := by
        calc
          (7 : ZMod 36750397) ^ 2243 = (7 : ZMod 36750397) ^ (1121 + 1121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 1121 * (7 : ZMod 36750397) ^ 1121) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 25052730 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 36750397) ^ 4486 = 14064205 := by
        calc
          (7 : ZMod 36750397) ^ 4486 = (7 : ZMod 36750397) ^ (2243 + 2243) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 2243 * (7 : ZMod 36750397) ^ 2243 := by rw [pow_add]
          _ = 14064205 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 36750397) ^ 8972 = 16756940 := by
        calc
          (7 : ZMod 36750397) ^ 8972 = (7 : ZMod 36750397) ^ (4486 + 4486) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 4486 * (7 : ZMod 36750397) ^ 4486 := by rw [pow_add]
          _ = 16756940 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 36750397) ^ 17944 = 28346194 := by
        calc
          (7 : ZMod 36750397) ^ 17944 = (7 : ZMod 36750397) ^ (8972 + 8972) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 8972 * (7 : ZMod 36750397) ^ 8972 := by rw [pow_add]
          _ = 28346194 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 36750397) ^ 35889 = 23243584 := by
        calc
          (7 : ZMod 36750397) ^ 35889 = (7 : ZMod 36750397) ^ (17944 + 17944 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 17944 * (7 : ZMod 36750397) ^ 17944) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 23243584 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 36750397) ^ 71778 = 28654977 := by
        calc
          (7 : ZMod 36750397) ^ 71778 = (7 : ZMod 36750397) ^ (35889 + 35889) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 35889 * (7 : ZMod 36750397) ^ 35889 := by rw [pow_add]
          _ = 28654977 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 36750397) ^ 143556 = 18019004 := by
        calc
          (7 : ZMod 36750397) ^ 143556 = (7 : ZMod 36750397) ^ (71778 + 71778) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 71778 * (7 : ZMod 36750397) ^ 71778 := by rw [pow_add]
          _ = 18019004 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 36750397) ^ 287112 = 2963787 := by
        calc
          (7 : ZMod 36750397) ^ 287112 = (7 : ZMod 36750397) ^ (143556 + 143556) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 143556 * (7 : ZMod 36750397) ^ 143556 := by rw [pow_add]
          _ = 2963787 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 36750397) ^ 574224 = 26991223 := by
        calc
          (7 : ZMod 36750397) ^ 574224 = (7 : ZMod 36750397) ^ (287112 + 287112) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 287112 * (7 : ZMod 36750397) ^ 287112 := by rw [pow_add]
          _ = 26991223 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 36750397) ^ 1148449 = 28394243 := by
        calc
          (7 : ZMod 36750397) ^ 1148449 = (7 : ZMod 36750397) ^ (574224 + 574224 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 574224 * (7 : ZMod 36750397) ^ 574224) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 28394243 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 36750397) ^ 2296899 = 11385757 := by
        calc
          (7 : ZMod 36750397) ^ 2296899 = (7 : ZMod 36750397) ^ (1148449 + 1148449 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 1148449 * (7 : ZMod 36750397) ^ 1148449) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 11385757 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 36750397) ^ 4593799 = 10937149 := by
        calc
          (7 : ZMod 36750397) ^ 4593799 = (7 : ZMod 36750397) ^ (2296899 + 2296899 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 2296899 * (7 : ZMod 36750397) ^ 2296899) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 10937149 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 36750397) ^ 9187599 = 26442054 := by
        calc
          (7 : ZMod 36750397) ^ 9187599 = (7 : ZMod 36750397) ^ (4593799 + 4593799 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 4593799 * (7 : ZMod 36750397) ^ 4593799) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 26442054 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 36750397) ^ 18375198 = 36750396 := by
        calc
          (7 : ZMod 36750397) ^ 18375198 = (7 : ZMod 36750397) ^ (9187599 + 9187599) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 9187599 * (7 : ZMod 36750397) ^ 9187599 := by rw [pow_add]
          _ = 36750396 := by rw [factor_0_23]; decide
      change (7 : ZMod 36750397) ^ 18375198 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (7 : ZMod 36750397) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 36750397) ^ 2 = 49 := by
        calc
          (7 : ZMod 36750397) ^ 2 = (7 : ZMod 36750397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 1 * (7 : ZMod 36750397) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 36750397) ^ 5 = 16807 := by
        calc
          (7 : ZMod 36750397) ^ 5 = (7 : ZMod 36750397) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 2 * (7 : ZMod 36750397) ^ 2) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 36750397) ^ 11 = 29555702 := by
        calc
          (7 : ZMod 36750397) ^ 11 = (7 : ZMod 36750397) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 5 * (7 : ZMod 36750397) ^ 5) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 29555702 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 36750397) ^ 23 = 25976874 := by
        calc
          (7 : ZMod 36750397) ^ 23 = (7 : ZMod 36750397) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 11 * (7 : ZMod 36750397) ^ 11) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 25976874 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 36750397) ^ 46 = 18986429 := by
        calc
          (7 : ZMod 36750397) ^ 46 = (7 : ZMod 36750397) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 23 * (7 : ZMod 36750397) ^ 23 := by rw [pow_add]
          _ = 18986429 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 36750397) ^ 93 = 33255594 := by
        calc
          (7 : ZMod 36750397) ^ 93 = (7 : ZMod 36750397) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 46 * (7 : ZMod 36750397) ^ 46) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 33255594 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 36750397) ^ 186 = 21069829 := by
        calc
          (7 : ZMod 36750397) ^ 186 = (7 : ZMod 36750397) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 93 * (7 : ZMod 36750397) ^ 93 := by rw [pow_add]
          _ = 21069829 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 36750397) ^ 373 = 11591828 := by
        calc
          (7 : ZMod 36750397) ^ 373 = (7 : ZMod 36750397) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 186 * (7 : ZMod 36750397) ^ 186) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 11591828 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 36750397) ^ 747 = 35563785 := by
        calc
          (7 : ZMod 36750397) ^ 747 = (7 : ZMod 36750397) ^ (373 + 373 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 373 * (7 : ZMod 36750397) ^ 373) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 35563785 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 36750397) ^ 1495 = 26795996 := by
        calc
          (7 : ZMod 36750397) ^ 1495 = (7 : ZMod 36750397) ^ (747 + 747 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 747 * (7 : ZMod 36750397) ^ 747) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 26795996 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 36750397) ^ 2990 = 3837701 := by
        calc
          (7 : ZMod 36750397) ^ 2990 = (7 : ZMod 36750397) ^ (1495 + 1495) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 1495 * (7 : ZMod 36750397) ^ 1495 := by rw [pow_add]
          _ = 3837701 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 36750397) ^ 5981 = 11306486 := by
        calc
          (7 : ZMod 36750397) ^ 5981 = (7 : ZMod 36750397) ^ (2990 + 2990 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 2990 * (7 : ZMod 36750397) ^ 2990) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 11306486 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 36750397) ^ 11963 = 15398082 := by
        calc
          (7 : ZMod 36750397) ^ 11963 = (7 : ZMod 36750397) ^ (5981 + 5981 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 5981 * (7 : ZMod 36750397) ^ 5981) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 15398082 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 36750397) ^ 23926 = 9971292 := by
        calc
          (7 : ZMod 36750397) ^ 23926 = (7 : ZMod 36750397) ^ (11963 + 11963) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 11963 * (7 : ZMod 36750397) ^ 11963 := by rw [pow_add]
          _ = 9971292 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 36750397) ^ 47852 = 8582438 := by
        calc
          (7 : ZMod 36750397) ^ 47852 = (7 : ZMod 36750397) ^ (23926 + 23926) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 23926 * (7 : ZMod 36750397) ^ 23926 := by rw [pow_add]
          _ = 8582438 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 36750397) ^ 95704 = 9323096 := by
        calc
          (7 : ZMod 36750397) ^ 95704 = (7 : ZMod 36750397) ^ (47852 + 47852) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 47852 * (7 : ZMod 36750397) ^ 47852 := by rw [pow_add]
          _ = 9323096 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 36750397) ^ 191408 = 27811857 := by
        calc
          (7 : ZMod 36750397) ^ 191408 = (7 : ZMod 36750397) ^ (95704 + 95704) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 95704 * (7 : ZMod 36750397) ^ 95704 := by rw [pow_add]
          _ = 27811857 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 36750397) ^ 382816 = 2730574 := by
        calc
          (7 : ZMod 36750397) ^ 382816 = (7 : ZMod 36750397) ^ (191408 + 191408) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 191408 * (7 : ZMod 36750397) ^ 191408 := by rw [pow_add]
          _ = 2730574 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 36750397) ^ 765633 = 25024475 := by
        calc
          (7 : ZMod 36750397) ^ 765633 = (7 : ZMod 36750397) ^ (382816 + 382816 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 382816 * (7 : ZMod 36750397) ^ 382816) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 25024475 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 36750397) ^ 1531266 = 9671827 := by
        calc
          (7 : ZMod 36750397) ^ 1531266 = (7 : ZMod 36750397) ^ (765633 + 765633) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 765633 * (7 : ZMod 36750397) ^ 765633 := by rw [pow_add]
          _ = 9671827 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 36750397) ^ 3062533 = 19225974 := by
        calc
          (7 : ZMod 36750397) ^ 3062533 = (7 : ZMod 36750397) ^ (1531266 + 1531266 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 1531266 * (7 : ZMod 36750397) ^ 1531266) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 19225974 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 36750397) ^ 6125066 = 10694886 := by
        calc
          (7 : ZMod 36750397) ^ 6125066 = (7 : ZMod 36750397) ^ (3062533 + 3062533) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 3062533 * (7 : ZMod 36750397) ^ 3062533 := by rw [pow_add]
          _ = 10694886 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 36750397) ^ 12250132 = 10694885 := by
        calc
          (7 : ZMod 36750397) ^ 12250132 = (7 : ZMod 36750397) ^ (6125066 + 6125066) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 6125066 * (7 : ZMod 36750397) ^ 6125066 := by rw [pow_add]
          _ = 10694885 := by rw [factor_1_22]; decide
      change (7 : ZMod 36750397) ^ 12250132 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (7 : ZMod 36750397) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 36750397) ^ 2 = 49 := by
        calc
          (7 : ZMod 36750397) ^ 2 = (7 : ZMod 36750397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 1 * (7 : ZMod 36750397) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 36750397) ^ 4 = 2401 := by
        calc
          (7 : ZMod 36750397) ^ 4 = (7 : ZMod 36750397) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 2 * (7 : ZMod 36750397) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 36750397) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 36750397) ^ 8 = (7 : ZMod 36750397) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 4 * (7 : ZMod 36750397) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 36750397) ^ 16 = 24317662 := by
        calc
          (7 : ZMod 36750397) ^ 16 = (7 : ZMod 36750397) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 8 * (7 : ZMod 36750397) ^ 8 := by rw [pow_add]
          _ = 24317662 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 36750397) ^ 32 = 31540682 := by
        calc
          (7 : ZMod 36750397) ^ 32 = (7 : ZMod 36750397) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 16 * (7 : ZMod 36750397) ^ 16 := by rw [pow_add]
          _ = 31540682 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 36750397) ^ 65 = 10054424 := by
        calc
          (7 : ZMod 36750397) ^ 65 = (7 : ZMod 36750397) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 32 * (7 : ZMod 36750397) ^ 32) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 10054424 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 36750397) ^ 131 = 27446744 := by
        calc
          (7 : ZMod 36750397) ^ 131 = (7 : ZMod 36750397) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 65 * (7 : ZMod 36750397) ^ 65) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 27446744 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 36750397) ^ 263 = 7651219 := by
        calc
          (7 : ZMod 36750397) ^ 263 = (7 : ZMod 36750397) ^ (131 + 131 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 131 * (7 : ZMod 36750397) ^ 131) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 7651219 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 36750397) ^ 527 = 7273452 := by
        calc
          (7 : ZMod 36750397) ^ 527 = (7 : ZMod 36750397) ^ (263 + 263 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 263 * (7 : ZMod 36750397) ^ 263) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 7273452 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 36750397) ^ 1055 = 31535344 := by
        calc
          (7 : ZMod 36750397) ^ 1055 = (7 : ZMod 36750397) ^ (527 + 527 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 527 * (7 : ZMod 36750397) ^ 527) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 31535344 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 36750397) ^ 2111 = 24477709 := by
        calc
          (7 : ZMod 36750397) ^ 2111 = (7 : ZMod 36750397) ^ (1055 + 1055 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 1055 * (7 : ZMod 36750397) ^ 1055) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 24477709 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 36750397) ^ 4222 = 14669428 := by
        calc
          (7 : ZMod 36750397) ^ 4222 = (7 : ZMod 36750397) ^ (2111 + 2111) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 2111 * (7 : ZMod 36750397) ^ 2111 := by rw [pow_add]
          _ = 14669428 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 36750397) ^ 8444 = 21212096 := by
        calc
          (7 : ZMod 36750397) ^ 8444 = (7 : ZMod 36750397) ^ (4222 + 4222) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 4222 * (7 : ZMod 36750397) ^ 4222 := by rw [pow_add]
          _ = 21212096 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 36750397) ^ 16888 = 8798877 := by
        calc
          (7 : ZMod 36750397) ^ 16888 = (7 : ZMod 36750397) ^ (8444 + 8444) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 8444 * (7 : ZMod 36750397) ^ 8444 := by rw [pow_add]
          _ = 8798877 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 36750397) ^ 33777 = 14846759 := by
        calc
          (7 : ZMod 36750397) ^ 33777 = (7 : ZMod 36750397) ^ (16888 + 16888 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 16888 * (7 : ZMod 36750397) ^ 16888) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 14846759 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 36750397) ^ 67555 = 13135464 := by
        calc
          (7 : ZMod 36750397) ^ 67555 = (7 : ZMod 36750397) ^ (33777 + 33777 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 33777 * (7 : ZMod 36750397) ^ 33777) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 13135464 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 36750397) ^ 135111 = 30516527 := by
        calc
          (7 : ZMod 36750397) ^ 135111 = (7 : ZMod 36750397) ^ (67555 + 67555 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 67555 * (7 : ZMod 36750397) ^ 67555) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 30516527 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 36750397) ^ 270223 = 878023 := by
        calc
          (7 : ZMod 36750397) ^ 270223 = (7 : ZMod 36750397) ^ (135111 + 135111 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 135111 * (7 : ZMod 36750397) ^ 135111) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 878023 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 36750397) ^ 540447 = 5673826 := by
        calc
          (7 : ZMod 36750397) ^ 540447 = (7 : ZMod 36750397) ^ (270223 + 270223 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 270223 * (7 : ZMod 36750397) ^ 270223) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 5673826 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 36750397) ^ 1080894 = 19467789 := by
        calc
          (7 : ZMod 36750397) ^ 1080894 = (7 : ZMod 36750397) ^ (540447 + 540447) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 540447 * (7 : ZMod 36750397) ^ 540447 := by rw [pow_add]
          _ = 19467789 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 36750397) ^ 2161788 = 18417737 := by
        calc
          (7 : ZMod 36750397) ^ 2161788 = (7 : ZMod 36750397) ^ (1080894 + 1080894) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 1080894 * (7 : ZMod 36750397) ^ 1080894 := by rw [pow_add]
          _ = 18417737 := by rw [factor_2_20]; decide
      change (7 : ZMod 36750397) ^ 2161788 ≠ 1
      rw [factor_2_21]
      decide
    ·
      have factor_3_0 : (7 : ZMod 36750397) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 36750397) ^ 3 = 343 := by
        calc
          (7 : ZMod 36750397) ^ 3 = (7 : ZMod 36750397) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 1 * (7 : ZMod 36750397) ^ 1) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 36750397) ^ 6 = 117649 := by
        calc
          (7 : ZMod 36750397) ^ 6 = (7 : ZMod 36750397) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 3 * (7 : ZMod 36750397) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 36750397) ^ 13 = 14963915 := by
        calc
          (7 : ZMod 36750397) ^ 13 = (7 : ZMod 36750397) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 6 * (7 : ZMod 36750397) ^ 6) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 14963915 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 36750397) ^ 27 = 5050765 := by
        calc
          (7 : ZMod 36750397) ^ 27 = (7 : ZMod 36750397) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 13 * (7 : ZMod 36750397) ^ 13) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 5050765 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 36750397) ^ 54 = 12508469 := by
        calc
          (7 : ZMod 36750397) ^ 54 = (7 : ZMod 36750397) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 27 * (7 : ZMod 36750397) ^ 27 := by rw [pow_add]
          _ = 12508469 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 36750397) ^ 108 = 31779412 := by
        calc
          (7 : ZMod 36750397) ^ 108 = (7 : ZMod 36750397) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 54 * (7 : ZMod 36750397) ^ 54 := by rw [pow_add]
          _ = 31779412 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 36750397) ^ 216 = 18930601 := by
        calc
          (7 : ZMod 36750397) ^ 216 = (7 : ZMod 36750397) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 108 * (7 : ZMod 36750397) ^ 108 := by rw [pow_add]
          _ = 18930601 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 36750397) ^ 433 = 6420511 := by
        calc
          (7 : ZMod 36750397) ^ 433 = (7 : ZMod 36750397) ^ (216 + 216 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 216 * (7 : ZMod 36750397) ^ 216) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 6420511 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 36750397) ^ 867 = 31050768 := by
        calc
          (7 : ZMod 36750397) ^ 867 = (7 : ZMod 36750397) ^ (433 + 433 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = ((7 : ZMod 36750397) ^ 433 * (7 : ZMod 36750397) ^ 433) * (7 : ZMod 36750397) := by rw [pow_succ, pow_add]
          _ = 31050768 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 36750397) ^ 1734 = 56712 := by
        calc
          (7 : ZMod 36750397) ^ 1734 = (7 : ZMod 36750397) ^ (867 + 867) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 867 * (7 : ZMod 36750397) ^ 867 := by rw [pow_add]
          _ = 56712 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 36750397) ^ 3468 = 18966405 := by
        calc
          (7 : ZMod 36750397) ^ 3468 = (7 : ZMod 36750397) ^ (1734 + 1734) :=
            congrArg (fun n : ℕ => (7 : ZMod 36750397) ^ n) (by norm_num)
          _ = (7 : ZMod 36750397) ^ 1734 * (7 : ZMod 36750397) ^ 1734 := by rw [pow_add]
          _ = 18966405 := by rw [factor_3_10]; decide
      change (7 : ZMod 36750397) ^ 3468 ≠ 1
      rw [factor_3_11]
      decide

#print axioms prime_lucas_36750397

end TotientTailPeriodKiller
end Erdos249257
