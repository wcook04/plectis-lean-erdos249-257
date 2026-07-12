import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2401668757 : Nat.Prime 2401668757 := by
  apply lucas_primality 2401668757 (7 : ZMod 2401668757)
  ·
      have fermat_0 : (7 : ZMod 2401668757) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 2401668757) ^ 2 = 49 := by
        calc
          (7 : ZMod 2401668757) ^ 2 = (7 : ZMod 2401668757) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1 * (7 : ZMod 2401668757) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 2401668757) ^ 4 = 2401 := by
        calc
          (7 : ZMod 2401668757) ^ 4 = (7 : ZMod 2401668757) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2 * (7 : ZMod 2401668757) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 2401668757) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 2401668757) ^ 8 = (7 : ZMod 2401668757) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 4 * (7 : ZMod 2401668757) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 2401668757) ^ 17 = 74846673 := by
        calc
          (7 : ZMod 2401668757) ^ 17 = (7 : ZMod 2401668757) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 8 * (7 : ZMod 2401668757) ^ 8) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 74846673 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 2401668757) ^ 35 = 2343462315 := by
        calc
          (7 : ZMod 2401668757) ^ 35 = (7 : ZMod 2401668757) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 17 * (7 : ZMod 2401668757) ^ 17) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 2343462315 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 2401668757) ^ 71 = 238865901 := by
        calc
          (7 : ZMod 2401668757) ^ 71 = (7 : ZMod 2401668757) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 35 * (7 : ZMod 2401668757) ^ 35) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 238865901 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 2401668757) ^ 143 = 1298896190 := by
        calc
          (7 : ZMod 2401668757) ^ 143 = (7 : ZMod 2401668757) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 71 * (7 : ZMod 2401668757) ^ 71) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1298896190 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 2401668757) ^ 286 = 2286360576 := by
        calc
          (7 : ZMod 2401668757) ^ 286 = (7 : ZMod 2401668757) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 143 * (7 : ZMod 2401668757) ^ 143 := by rw [pow_add]
          _ = 2286360576 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 2401668757) ^ 572 = 2133150781 := by
        calc
          (7 : ZMod 2401668757) ^ 572 = (7 : ZMod 2401668757) ^ (286 + 286) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 286 * (7 : ZMod 2401668757) ^ 286 := by rw [pow_add]
          _ = 2133150781 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 2401668757) ^ 1145 = 131779603 := by
        calc
          (7 : ZMod 2401668757) ^ 1145 = (7 : ZMod 2401668757) ^ (572 + 572 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 572 * (7 : ZMod 2401668757) ^ 572) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 131779603 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 2401668757) ^ 2290 = 2205497373 := by
        calc
          (7 : ZMod 2401668757) ^ 2290 = (7 : ZMod 2401668757) ^ (1145 + 1145) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1145 * (7 : ZMod 2401668757) ^ 1145 := by rw [pow_add]
          _ = 2205497373 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 2401668757) ^ 4580 = 522623246 := by
        calc
          (7 : ZMod 2401668757) ^ 4580 = (7 : ZMod 2401668757) ^ (2290 + 2290) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2290 * (7 : ZMod 2401668757) ^ 2290 := by rw [pow_add]
          _ = 522623246 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 2401668757) ^ 9161 = 217771681 := by
        calc
          (7 : ZMod 2401668757) ^ 9161 = (7 : ZMod 2401668757) ^ (4580 + 4580 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 4580 * (7 : ZMod 2401668757) ^ 4580) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 217771681 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 2401668757) ^ 18323 = 1978545293 := by
        calc
          (7 : ZMod 2401668757) ^ 18323 = (7 : ZMod 2401668757) ^ (9161 + 9161 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 9161 * (7 : ZMod 2401668757) ^ 9161) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1978545293 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 2401668757) ^ 36646 = 1955866188 := by
        calc
          (7 : ZMod 2401668757) ^ 36646 = (7 : ZMod 2401668757) ^ (18323 + 18323) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 18323 * (7 : ZMod 2401668757) ^ 18323 := by rw [pow_add]
          _ = 1955866188 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 2401668757) ^ 73293 = 1243867022 := by
        calc
          (7 : ZMod 2401668757) ^ 73293 = (7 : ZMod 2401668757) ^ (36646 + 36646 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 36646 * (7 : ZMod 2401668757) ^ 36646) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1243867022 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 2401668757) ^ 146586 = 1111096053 := by
        calc
          (7 : ZMod 2401668757) ^ 146586 = (7 : ZMod 2401668757) ^ (73293 + 73293) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 73293 * (7 : ZMod 2401668757) ^ 73293 := by rw [pow_add]
          _ = 1111096053 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 2401668757) ^ 293172 = 602424014 := by
        calc
          (7 : ZMod 2401668757) ^ 293172 = (7 : ZMod 2401668757) ^ (146586 + 146586) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 146586 * (7 : ZMod 2401668757) ^ 146586 := by rw [pow_add]
          _ = 602424014 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 2401668757) ^ 586344 = 1398218994 := by
        calc
          (7 : ZMod 2401668757) ^ 586344 = (7 : ZMod 2401668757) ^ (293172 + 293172) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 293172 * (7 : ZMod 2401668757) ^ 293172 := by rw [pow_add]
          _ = 1398218994 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 2401668757) ^ 1172689 = 452314925 := by
        calc
          (7 : ZMod 2401668757) ^ 1172689 = (7 : ZMod 2401668757) ^ (586344 + 586344 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 586344 * (7 : ZMod 2401668757) ^ 586344) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 452314925 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 2401668757) ^ 2345379 = 1757901802 := by
        calc
          (7 : ZMod 2401668757) ^ 2345379 = (7 : ZMod 2401668757) ^ (1172689 + 1172689 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 1172689 * (7 : ZMod 2401668757) ^ 1172689) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1757901802 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 2401668757) ^ 4690759 = 772077712 := by
        calc
          (7 : ZMod 2401668757) ^ 4690759 = (7 : ZMod 2401668757) ^ (2345379 + 2345379 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 2345379 * (7 : ZMod 2401668757) ^ 2345379) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 772077712 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 2401668757) ^ 9381518 = 1866220113 := by
        calc
          (7 : ZMod 2401668757) ^ 9381518 = (7 : ZMod 2401668757) ^ (4690759 + 4690759) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 4690759 * (7 : ZMod 2401668757) ^ 4690759 := by rw [pow_add]
          _ = 1866220113 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 2401668757) ^ 18763037 = 1673466625 := by
        calc
          (7 : ZMod 2401668757) ^ 18763037 = (7 : ZMod 2401668757) ^ (9381518 + 9381518 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 9381518 * (7 : ZMod 2401668757) ^ 9381518) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1673466625 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 2401668757) ^ 37526074 = 1734218665 := by
        calc
          (7 : ZMod 2401668757) ^ 37526074 = (7 : ZMod 2401668757) ^ (18763037 + 18763037) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 18763037 * (7 : ZMod 2401668757) ^ 18763037 := by rw [pow_add]
          _ = 1734218665 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 2401668757) ^ 75052148 = 2336322807 := by
        calc
          (7 : ZMod 2401668757) ^ 75052148 = (7 : ZMod 2401668757) ^ (37526074 + 37526074) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 37526074 * (7 : ZMod 2401668757) ^ 37526074 := by rw [pow_add]
          _ = 2336322807 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 2401668757) ^ 150104297 = 1680647012 := by
        calc
          (7 : ZMod 2401668757) ^ 150104297 = (7 : ZMod 2401668757) ^ (75052148 + 75052148 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 75052148 * (7 : ZMod 2401668757) ^ 75052148) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1680647012 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 2401668757) ^ 300208594 = 2264747978 := by
        calc
          (7 : ZMod 2401668757) ^ 300208594 = (7 : ZMod 2401668757) ^ (150104297 + 150104297) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 150104297 * (7 : ZMod 2401668757) ^ 150104297 := by rw [pow_add]
          _ = 2264747978 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 2401668757) ^ 600417189 = 49545220 := by
        calc
          (7 : ZMod 2401668757) ^ 600417189 = (7 : ZMod 2401668757) ^ (300208594 + 300208594 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 300208594 * (7 : ZMod 2401668757) ^ 300208594) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 49545220 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 2401668757) ^ 1200834378 = 2401668756 := by
        calc
          (7 : ZMod 2401668757) ^ 1200834378 = (7 : ZMod 2401668757) ^ (600417189 + 600417189) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 600417189 * (7 : ZMod 2401668757) ^ 600417189 := by rw [pow_add]
          _ = 2401668756 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 2401668757) ^ 2401668756 = 1 := by
        calc
          (7 : ZMod 2401668757) ^ 2401668756 = (7 : ZMod 2401668757) ^ (1200834378 + 1200834378) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1200834378 * (7 : ZMod 2401668757) ^ 1200834378 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (29, 1), (73, 1), (31513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (29, 1), (73, 1), (31513, 1)] : List FactorBlock).map factorBlockValue).prod = 2401668757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 2401668757) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 2401668757) ^ 2 = 49 := by
        calc
          (7 : ZMod 2401668757) ^ 2 = (7 : ZMod 2401668757) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1 * (7 : ZMod 2401668757) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 2401668757) ^ 4 = 2401 := by
        calc
          (7 : ZMod 2401668757) ^ 4 = (7 : ZMod 2401668757) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2 * (7 : ZMod 2401668757) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 2401668757) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 2401668757) ^ 8 = (7 : ZMod 2401668757) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 4 * (7 : ZMod 2401668757) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 2401668757) ^ 17 = 74846673 := by
        calc
          (7 : ZMod 2401668757) ^ 17 = (7 : ZMod 2401668757) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 8 * (7 : ZMod 2401668757) ^ 8) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 74846673 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 2401668757) ^ 35 = 2343462315 := by
        calc
          (7 : ZMod 2401668757) ^ 35 = (7 : ZMod 2401668757) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 17 * (7 : ZMod 2401668757) ^ 17) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 2343462315 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 2401668757) ^ 71 = 238865901 := by
        calc
          (7 : ZMod 2401668757) ^ 71 = (7 : ZMod 2401668757) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 35 * (7 : ZMod 2401668757) ^ 35) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 238865901 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 2401668757) ^ 143 = 1298896190 := by
        calc
          (7 : ZMod 2401668757) ^ 143 = (7 : ZMod 2401668757) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 71 * (7 : ZMod 2401668757) ^ 71) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1298896190 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 2401668757) ^ 286 = 2286360576 := by
        calc
          (7 : ZMod 2401668757) ^ 286 = (7 : ZMod 2401668757) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 143 * (7 : ZMod 2401668757) ^ 143 := by rw [pow_add]
          _ = 2286360576 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 2401668757) ^ 572 = 2133150781 := by
        calc
          (7 : ZMod 2401668757) ^ 572 = (7 : ZMod 2401668757) ^ (286 + 286) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 286 * (7 : ZMod 2401668757) ^ 286 := by rw [pow_add]
          _ = 2133150781 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 2401668757) ^ 1145 = 131779603 := by
        calc
          (7 : ZMod 2401668757) ^ 1145 = (7 : ZMod 2401668757) ^ (572 + 572 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 572 * (7 : ZMod 2401668757) ^ 572) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 131779603 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 2401668757) ^ 2290 = 2205497373 := by
        calc
          (7 : ZMod 2401668757) ^ 2290 = (7 : ZMod 2401668757) ^ (1145 + 1145) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1145 * (7 : ZMod 2401668757) ^ 1145 := by rw [pow_add]
          _ = 2205497373 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 2401668757) ^ 4580 = 522623246 := by
        calc
          (7 : ZMod 2401668757) ^ 4580 = (7 : ZMod 2401668757) ^ (2290 + 2290) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2290 * (7 : ZMod 2401668757) ^ 2290 := by rw [pow_add]
          _ = 522623246 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 2401668757) ^ 9161 = 217771681 := by
        calc
          (7 : ZMod 2401668757) ^ 9161 = (7 : ZMod 2401668757) ^ (4580 + 4580 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 4580 * (7 : ZMod 2401668757) ^ 4580) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 217771681 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 2401668757) ^ 18323 = 1978545293 := by
        calc
          (7 : ZMod 2401668757) ^ 18323 = (7 : ZMod 2401668757) ^ (9161 + 9161 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 9161 * (7 : ZMod 2401668757) ^ 9161) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1978545293 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 2401668757) ^ 36646 = 1955866188 := by
        calc
          (7 : ZMod 2401668757) ^ 36646 = (7 : ZMod 2401668757) ^ (18323 + 18323) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 18323 * (7 : ZMod 2401668757) ^ 18323 := by rw [pow_add]
          _ = 1955866188 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 2401668757) ^ 73293 = 1243867022 := by
        calc
          (7 : ZMod 2401668757) ^ 73293 = (7 : ZMod 2401668757) ^ (36646 + 36646 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 36646 * (7 : ZMod 2401668757) ^ 36646) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1243867022 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 2401668757) ^ 146586 = 1111096053 := by
        calc
          (7 : ZMod 2401668757) ^ 146586 = (7 : ZMod 2401668757) ^ (73293 + 73293) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 73293 * (7 : ZMod 2401668757) ^ 73293 := by rw [pow_add]
          _ = 1111096053 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 2401668757) ^ 293172 = 602424014 := by
        calc
          (7 : ZMod 2401668757) ^ 293172 = (7 : ZMod 2401668757) ^ (146586 + 146586) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 146586 * (7 : ZMod 2401668757) ^ 146586 := by rw [pow_add]
          _ = 602424014 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 2401668757) ^ 586344 = 1398218994 := by
        calc
          (7 : ZMod 2401668757) ^ 586344 = (7 : ZMod 2401668757) ^ (293172 + 293172) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 293172 * (7 : ZMod 2401668757) ^ 293172 := by rw [pow_add]
          _ = 1398218994 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 2401668757) ^ 1172689 = 452314925 := by
        calc
          (7 : ZMod 2401668757) ^ 1172689 = (7 : ZMod 2401668757) ^ (586344 + 586344 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 586344 * (7 : ZMod 2401668757) ^ 586344) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 452314925 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 2401668757) ^ 2345379 = 1757901802 := by
        calc
          (7 : ZMod 2401668757) ^ 2345379 = (7 : ZMod 2401668757) ^ (1172689 + 1172689 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 1172689 * (7 : ZMod 2401668757) ^ 1172689) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1757901802 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 2401668757) ^ 4690759 = 772077712 := by
        calc
          (7 : ZMod 2401668757) ^ 4690759 = (7 : ZMod 2401668757) ^ (2345379 + 2345379 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 2345379 * (7 : ZMod 2401668757) ^ 2345379) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 772077712 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 2401668757) ^ 9381518 = 1866220113 := by
        calc
          (7 : ZMod 2401668757) ^ 9381518 = (7 : ZMod 2401668757) ^ (4690759 + 4690759) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 4690759 * (7 : ZMod 2401668757) ^ 4690759 := by rw [pow_add]
          _ = 1866220113 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 2401668757) ^ 18763037 = 1673466625 := by
        calc
          (7 : ZMod 2401668757) ^ 18763037 = (7 : ZMod 2401668757) ^ (9381518 + 9381518 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 9381518 * (7 : ZMod 2401668757) ^ 9381518) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1673466625 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 2401668757) ^ 37526074 = 1734218665 := by
        calc
          (7 : ZMod 2401668757) ^ 37526074 = (7 : ZMod 2401668757) ^ (18763037 + 18763037) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 18763037 * (7 : ZMod 2401668757) ^ 18763037 := by rw [pow_add]
          _ = 1734218665 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 2401668757) ^ 75052148 = 2336322807 := by
        calc
          (7 : ZMod 2401668757) ^ 75052148 = (7 : ZMod 2401668757) ^ (37526074 + 37526074) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 37526074 * (7 : ZMod 2401668757) ^ 37526074 := by rw [pow_add]
          _ = 2336322807 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 2401668757) ^ 150104297 = 1680647012 := by
        calc
          (7 : ZMod 2401668757) ^ 150104297 = (7 : ZMod 2401668757) ^ (75052148 + 75052148 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 75052148 * (7 : ZMod 2401668757) ^ 75052148) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1680647012 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 2401668757) ^ 300208594 = 2264747978 := by
        calc
          (7 : ZMod 2401668757) ^ 300208594 = (7 : ZMod 2401668757) ^ (150104297 + 150104297) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 150104297 * (7 : ZMod 2401668757) ^ 150104297 := by rw [pow_add]
          _ = 2264747978 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 2401668757) ^ 600417189 = 49545220 := by
        calc
          (7 : ZMod 2401668757) ^ 600417189 = (7 : ZMod 2401668757) ^ (300208594 + 300208594 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 300208594 * (7 : ZMod 2401668757) ^ 300208594) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 49545220 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 2401668757) ^ 1200834378 = 2401668756 := by
        calc
          (7 : ZMod 2401668757) ^ 1200834378 = (7 : ZMod 2401668757) ^ (600417189 + 600417189) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 600417189 * (7 : ZMod 2401668757) ^ 600417189 := by rw [pow_add]
          _ = 2401668756 := by rw [factor_0_29]; decide
      change (7 : ZMod 2401668757) ^ 1200834378 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (7 : ZMod 2401668757) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 2401668757) ^ 2 = 49 := by
        calc
          (7 : ZMod 2401668757) ^ 2 = (7 : ZMod 2401668757) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1 * (7 : ZMod 2401668757) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 2401668757) ^ 5 = 16807 := by
        calc
          (7 : ZMod 2401668757) ^ 5 = (7 : ZMod 2401668757) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 2 * (7 : ZMod 2401668757) ^ 2) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 2401668757) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 2401668757) ^ 11 = (7 : ZMod 2401668757) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 5 * (7 : ZMod 2401668757) ^ 5) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 2401668757) ^ 23 = 1118568615 := by
        calc
          (7 : ZMod 2401668757) ^ 23 = (7 : ZMod 2401668757) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 11 * (7 : ZMod 2401668757) ^ 11) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1118568615 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 2401668757) ^ 47 = 409336998 := by
        calc
          (7 : ZMod 2401668757) ^ 47 = (7 : ZMod 2401668757) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 23 * (7 : ZMod 2401668757) ^ 23) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 409336998 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 2401668757) ^ 95 = 905283885 := by
        calc
          (7 : ZMod 2401668757) ^ 95 = (7 : ZMod 2401668757) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 47 * (7 : ZMod 2401668757) ^ 47) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 905283885 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 2401668757) ^ 190 = 742701022 := by
        calc
          (7 : ZMod 2401668757) ^ 190 = (7 : ZMod 2401668757) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 95 * (7 : ZMod 2401668757) ^ 95 := by rw [pow_add]
          _ = 742701022 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 2401668757) ^ 381 = 1940061299 := by
        calc
          (7 : ZMod 2401668757) ^ 381 = (7 : ZMod 2401668757) ^ (190 + 190 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 190 * (7 : ZMod 2401668757) ^ 190) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1940061299 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 2401668757) ^ 763 = 290081065 := by
        calc
          (7 : ZMod 2401668757) ^ 763 = (7 : ZMod 2401668757) ^ (381 + 381 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 381 * (7 : ZMod 2401668757) ^ 381) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 290081065 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 2401668757) ^ 1526 = 1002738439 := by
        calc
          (7 : ZMod 2401668757) ^ 1526 = (7 : ZMod 2401668757) ^ (763 + 763) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 763 * (7 : ZMod 2401668757) ^ 763 := by rw [pow_add]
          _ = 1002738439 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 2401668757) ^ 3053 = 1458852898 := by
        calc
          (7 : ZMod 2401668757) ^ 3053 = (7 : ZMod 2401668757) ^ (1526 + 1526 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 1526 * (7 : ZMod 2401668757) ^ 1526) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1458852898 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 2401668757) ^ 6107 = 1239548416 := by
        calc
          (7 : ZMod 2401668757) ^ 6107 = (7 : ZMod 2401668757) ^ (3053 + 3053 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 3053 * (7 : ZMod 2401668757) ^ 3053) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1239548416 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 2401668757) ^ 12215 = 2109210775 := by
        calc
          (7 : ZMod 2401668757) ^ 12215 = (7 : ZMod 2401668757) ^ (6107 + 6107 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 6107 * (7 : ZMod 2401668757) ^ 6107) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 2109210775 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 2401668757) ^ 24431 = 1080953016 := by
        calc
          (7 : ZMod 2401668757) ^ 24431 = (7 : ZMod 2401668757) ^ (12215 + 12215 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 12215 * (7 : ZMod 2401668757) ^ 12215) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1080953016 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 2401668757) ^ 48862 = 264257600 := by
        calc
          (7 : ZMod 2401668757) ^ 48862 = (7 : ZMod 2401668757) ^ (24431 + 24431) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 24431 * (7 : ZMod 2401668757) ^ 24431 := by rw [pow_add]
          _ = 264257600 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 2401668757) ^ 97724 = 774887126 := by
        calc
          (7 : ZMod 2401668757) ^ 97724 = (7 : ZMod 2401668757) ^ (48862 + 48862) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 48862 * (7 : ZMod 2401668757) ^ 48862 := by rw [pow_add]
          _ = 774887126 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 2401668757) ^ 195448 = 1953600331 := by
        calc
          (7 : ZMod 2401668757) ^ 195448 = (7 : ZMod 2401668757) ^ (97724 + 97724) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 97724 * (7 : ZMod 2401668757) ^ 97724 := by rw [pow_add]
          _ = 1953600331 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 2401668757) ^ 390896 = 155271346 := by
        calc
          (7 : ZMod 2401668757) ^ 390896 = (7 : ZMod 2401668757) ^ (195448 + 195448) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 195448 * (7 : ZMod 2401668757) ^ 195448 := by rw [pow_add]
          _ = 155271346 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 2401668757) ^ 781793 = 2111980971 := by
        calc
          (7 : ZMod 2401668757) ^ 781793 = (7 : ZMod 2401668757) ^ (390896 + 390896 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 390896 * (7 : ZMod 2401668757) ^ 390896) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 2111980971 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 2401668757) ^ 1563586 = 2118906833 := by
        calc
          (7 : ZMod 2401668757) ^ 1563586 = (7 : ZMod 2401668757) ^ (781793 + 781793) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 781793 * (7 : ZMod 2401668757) ^ 781793 := by rw [pow_add]
          _ = 2118906833 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 2401668757) ^ 3127172 = 431256254 := by
        calc
          (7 : ZMod 2401668757) ^ 3127172 = (7 : ZMod 2401668757) ^ (1563586 + 1563586) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1563586 * (7 : ZMod 2401668757) ^ 1563586 := by rw [pow_add]
          _ = 431256254 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 2401668757) ^ 6254345 = 1219163121 := by
        calc
          (7 : ZMod 2401668757) ^ 6254345 = (7 : ZMod 2401668757) ^ (3127172 + 3127172 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 3127172 * (7 : ZMod 2401668757) ^ 3127172) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1219163121 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 2401668757) ^ 12508691 = 1445082269 := by
        calc
          (7 : ZMod 2401668757) ^ 12508691 = (7 : ZMod 2401668757) ^ (6254345 + 6254345 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 6254345 * (7 : ZMod 2401668757) ^ 6254345) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1445082269 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 2401668757) ^ 25017382 = 2183104033 := by
        calc
          (7 : ZMod 2401668757) ^ 25017382 = (7 : ZMod 2401668757) ^ (12508691 + 12508691) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 12508691 * (7 : ZMod 2401668757) ^ 12508691 := by rw [pow_add]
          _ = 2183104033 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 2401668757) ^ 50034765 = 51723250 := by
        calc
          (7 : ZMod 2401668757) ^ 50034765 = (7 : ZMod 2401668757) ^ (25017382 + 25017382 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 25017382 * (7 : ZMod 2401668757) ^ 25017382) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 51723250 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 2401668757) ^ 100069531 = 1967854860 := by
        calc
          (7 : ZMod 2401668757) ^ 100069531 = (7 : ZMod 2401668757) ^ (50034765 + 50034765 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 50034765 * (7 : ZMod 2401668757) ^ 50034765) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1967854860 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 2401668757) ^ 200139063 = 119270452 := by
        calc
          (7 : ZMod 2401668757) ^ 200139063 = (7 : ZMod 2401668757) ^ (100069531 + 100069531 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 100069531 * (7 : ZMod 2401668757) ^ 100069531) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 119270452 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 2401668757) ^ 400278126 = 1225597268 := by
        calc
          (7 : ZMod 2401668757) ^ 400278126 = (7 : ZMod 2401668757) ^ (200139063 + 200139063) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 200139063 * (7 : ZMod 2401668757) ^ 200139063 := by rw [pow_add]
          _ = 1225597268 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 2401668757) ^ 800556252 = 1225597267 := by
        calc
          (7 : ZMod 2401668757) ^ 800556252 = (7 : ZMod 2401668757) ^ (400278126 + 400278126) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 400278126 * (7 : ZMod 2401668757) ^ 400278126 := by rw [pow_add]
          _ = 1225597267 := by rw [factor_1_28]; decide
      change (7 : ZMod 2401668757) ^ 800556252 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (7 : ZMod 2401668757) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 2401668757) ^ 2 = 49 := by
        calc
          (7 : ZMod 2401668757) ^ 2 = (7 : ZMod 2401668757) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1 * (7 : ZMod 2401668757) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 2401668757) ^ 4 = 2401 := by
        calc
          (7 : ZMod 2401668757) ^ 4 = (7 : ZMod 2401668757) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2 * (7 : ZMod 2401668757) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 2401668757) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 2401668757) ^ 9 = (7 : ZMod 2401668757) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 4 * (7 : ZMod 2401668757) ^ 4) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 2401668757) ^ 19 = 1265818220 := by
        calc
          (7 : ZMod 2401668757) ^ 19 = (7 : ZMod 2401668757) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 9 * (7 : ZMod 2401668757) ^ 9) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1265818220 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 2401668757) ^ 39 = 1944789421 := by
        calc
          (7 : ZMod 2401668757) ^ 39 = (7 : ZMod 2401668757) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 19 * (7 : ZMod 2401668757) ^ 19) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1944789421 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 2401668757) ^ 78 = 456158887 := by
        calc
          (7 : ZMod 2401668757) ^ 78 = (7 : ZMod 2401668757) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 39 * (7 : ZMod 2401668757) ^ 39 := by rw [pow_add]
          _ = 456158887 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 2401668757) ^ 157 = 1081065514 := by
        calc
          (7 : ZMod 2401668757) ^ 157 = (7 : ZMod 2401668757) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 78 * (7 : ZMod 2401668757) ^ 78) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1081065514 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 2401668757) ^ 315 = 1380400181 := by
        calc
          (7 : ZMod 2401668757) ^ 315 = (7 : ZMod 2401668757) ^ (157 + 157 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 157 * (7 : ZMod 2401668757) ^ 157) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1380400181 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 2401668757) ^ 631 = 1182976404 := by
        calc
          (7 : ZMod 2401668757) ^ 631 = (7 : ZMod 2401668757) ^ (315 + 315 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 315 * (7 : ZMod 2401668757) ^ 315) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1182976404 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 2401668757) ^ 1263 = 263484241 := by
        calc
          (7 : ZMod 2401668757) ^ 1263 = (7 : ZMod 2401668757) ^ (631 + 631 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 631 * (7 : ZMod 2401668757) ^ 631) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 263484241 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 2401668757) ^ 2527 = 1997226883 := by
        calc
          (7 : ZMod 2401668757) ^ 2527 = (7 : ZMod 2401668757) ^ (1263 + 1263 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 1263 * (7 : ZMod 2401668757) ^ 1263) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1997226883 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 2401668757) ^ 5054 = 1484218541 := by
        calc
          (7 : ZMod 2401668757) ^ 5054 = (7 : ZMod 2401668757) ^ (2527 + 2527) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2527 * (7 : ZMod 2401668757) ^ 2527 := by rw [pow_add]
          _ = 1484218541 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 2401668757) ^ 10109 = 1841111031 := by
        calc
          (7 : ZMod 2401668757) ^ 10109 = (7 : ZMod 2401668757) ^ (5054 + 5054 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 5054 * (7 : ZMod 2401668757) ^ 5054) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1841111031 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 2401668757) ^ 20218 = 127238404 := by
        calc
          (7 : ZMod 2401668757) ^ 20218 = (7 : ZMod 2401668757) ^ (10109 + 10109) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 10109 * (7 : ZMod 2401668757) ^ 10109 := by rw [pow_add]
          _ = 127238404 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 2401668757) ^ 40437 = 714274782 := by
        calc
          (7 : ZMod 2401668757) ^ 40437 = (7 : ZMod 2401668757) ^ (20218 + 20218 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 20218 * (7 : ZMod 2401668757) ^ 20218) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 714274782 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 2401668757) ^ 80875 = 679459974 := by
        calc
          (7 : ZMod 2401668757) ^ 80875 = (7 : ZMod 2401668757) ^ (40437 + 40437 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 40437 * (7 : ZMod 2401668757) ^ 40437) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 679459974 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 2401668757) ^ 161750 = 2326003378 := by
        calc
          (7 : ZMod 2401668757) ^ 161750 = (7 : ZMod 2401668757) ^ (80875 + 80875) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 80875 * (7 : ZMod 2401668757) ^ 80875 := by rw [pow_add]
          _ = 2326003378 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 2401668757) ^ 323500 = 291145350 := by
        calc
          (7 : ZMod 2401668757) ^ 323500 = (7 : ZMod 2401668757) ^ (161750 + 161750) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 161750 * (7 : ZMod 2401668757) ^ 161750 := by rw [pow_add]
          _ = 291145350 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 2401668757) ^ 647001 = 1784309951 := by
        calc
          (7 : ZMod 2401668757) ^ 647001 = (7 : ZMod 2401668757) ^ (323500 + 323500 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 323500 * (7 : ZMod 2401668757) ^ 323500) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1784309951 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 2401668757) ^ 1294002 = 1399439595 := by
        calc
          (7 : ZMod 2401668757) ^ 1294002 = (7 : ZMod 2401668757) ^ (647001 + 647001) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 647001 * (7 : ZMod 2401668757) ^ 647001 := by rw [pow_add]
          _ = 1399439595 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 2401668757) ^ 2588005 = 1438669203 := by
        calc
          (7 : ZMod 2401668757) ^ 2588005 = (7 : ZMod 2401668757) ^ (1294002 + 1294002 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 1294002 * (7 : ZMod 2401668757) ^ 1294002) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1438669203 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 2401668757) ^ 5176010 = 1276867074 := by
        calc
          (7 : ZMod 2401668757) ^ 5176010 = (7 : ZMod 2401668757) ^ (2588005 + 2588005) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2588005 * (7 : ZMod 2401668757) ^ 2588005 := by rw [pow_add]
          _ = 1276867074 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 2401668757) ^ 10352020 = 2181347840 := by
        calc
          (7 : ZMod 2401668757) ^ 10352020 = (7 : ZMod 2401668757) ^ (5176010 + 5176010) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 5176010 * (7 : ZMod 2401668757) ^ 5176010 := by rw [pow_add]
          _ = 2181347840 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 2401668757) ^ 20704041 = 4439414 := by
        calc
          (7 : ZMod 2401668757) ^ 20704041 = (7 : ZMod 2401668757) ^ (10352020 + 10352020 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 10352020 * (7 : ZMod 2401668757) ^ 10352020) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 4439414 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 2401668757) ^ 41408082 = 302843454 := by
        calc
          (7 : ZMod 2401668757) ^ 41408082 = (7 : ZMod 2401668757) ^ (20704041 + 20704041) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 20704041 * (7 : ZMod 2401668757) ^ 20704041 := by rw [pow_add]
          _ = 302843454 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 2401668757) ^ 82816164 = 2074005113 := by
        calc
          (7 : ZMod 2401668757) ^ 82816164 = (7 : ZMod 2401668757) ^ (41408082 + 41408082) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 41408082 * (7 : ZMod 2401668757) ^ 41408082 := by rw [pow_add]
          _ = 2074005113 := by rw [factor_2_25]; decide
      change (7 : ZMod 2401668757) ^ 82816164 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (7 : ZMod 2401668757) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 2401668757) ^ 3 = 343 := by
        calc
          (7 : ZMod 2401668757) ^ 3 = (7 : ZMod 2401668757) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 1 * (7 : ZMod 2401668757) ^ 1) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 2401668757) ^ 7 = 823543 := by
        calc
          (7 : ZMod 2401668757) ^ 7 = (7 : ZMod 2401668757) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 3 * (7 : ZMod 2401668757) ^ 3) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 2401668757) ^ 15 = 1864046111 := by
        calc
          (7 : ZMod 2401668757) ^ 15 = (7 : ZMod 2401668757) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 7 * (7 : ZMod 2401668757) ^ 7) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1864046111 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 2401668757) ^ 31 = 966244820 := by
        calc
          (7 : ZMod 2401668757) ^ 31 = (7 : ZMod 2401668757) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 15 * (7 : ZMod 2401668757) ^ 15) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 966244820 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 2401668757) ^ 62 = 2166877258 := by
        calc
          (7 : ZMod 2401668757) ^ 62 = (7 : ZMod 2401668757) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 31 * (7 : ZMod 2401668757) ^ 31 := by rw [pow_add]
          _ = 2166877258 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 2401668757) ^ 125 = 448309236 := by
        calc
          (7 : ZMod 2401668757) ^ 125 = (7 : ZMod 2401668757) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 62 * (7 : ZMod 2401668757) ^ 62) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 448309236 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 2401668757) ^ 251 = 130280197 := by
        calc
          (7 : ZMod 2401668757) ^ 251 = (7 : ZMod 2401668757) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 125 * (7 : ZMod 2401668757) ^ 125) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 130280197 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 2401668757) ^ 502 = 391013829 := by
        calc
          (7 : ZMod 2401668757) ^ 502 = (7 : ZMod 2401668757) ^ (251 + 251) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 251 * (7 : ZMod 2401668757) ^ 251 := by rw [pow_add]
          _ = 391013829 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 2401668757) ^ 1004 = 1100579135 := by
        calc
          (7 : ZMod 2401668757) ^ 1004 = (7 : ZMod 2401668757) ^ (502 + 502) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 502 * (7 : ZMod 2401668757) ^ 502 := by rw [pow_add]
          _ = 1100579135 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 2401668757) ^ 2008 = 2212337982 := by
        calc
          (7 : ZMod 2401668757) ^ 2008 = (7 : ZMod 2401668757) ^ (1004 + 1004) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1004 * (7 : ZMod 2401668757) ^ 1004 := by rw [pow_add]
          _ = 2212337982 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 2401668757) ^ 4016 = 1706134527 := by
        calc
          (7 : ZMod 2401668757) ^ 4016 = (7 : ZMod 2401668757) ^ (2008 + 2008) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2008 * (7 : ZMod 2401668757) ^ 2008 := by rw [pow_add]
          _ = 1706134527 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 2401668757) ^ 8032 = 1169421198 := by
        calc
          (7 : ZMod 2401668757) ^ 8032 = (7 : ZMod 2401668757) ^ (4016 + 4016) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 4016 * (7 : ZMod 2401668757) ^ 4016 := by rw [pow_add]
          _ = 1169421198 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 2401668757) ^ 16064 = 1658176016 := by
        calc
          (7 : ZMod 2401668757) ^ 16064 = (7 : ZMod 2401668757) ^ (8032 + 8032) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 8032 * (7 : ZMod 2401668757) ^ 8032 := by rw [pow_add]
          _ = 1658176016 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 2401668757) ^ 32128 = 2316934105 := by
        calc
          (7 : ZMod 2401668757) ^ 32128 = (7 : ZMod 2401668757) ^ (16064 + 16064) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 16064 * (7 : ZMod 2401668757) ^ 16064 := by rw [pow_add]
          _ = 2316934105 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 2401668757) ^ 64256 = 1982027857 := by
        calc
          (7 : ZMod 2401668757) ^ 64256 = (7 : ZMod 2401668757) ^ (32128 + 32128) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 32128 * (7 : ZMod 2401668757) ^ 32128 := by rw [pow_add]
          _ = 1982027857 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 2401668757) ^ 128513 = 2277449100 := by
        calc
          (7 : ZMod 2401668757) ^ 128513 = (7 : ZMod 2401668757) ^ (64256 + 64256 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 64256 * (7 : ZMod 2401668757) ^ 64256) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 2277449100 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 2401668757) ^ 257027 = 516518846 := by
        calc
          (7 : ZMod 2401668757) ^ 257027 = (7 : ZMod 2401668757) ^ (128513 + 128513 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 128513 * (7 : ZMod 2401668757) ^ 128513) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 516518846 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 2401668757) ^ 514055 = 210170431 := by
        calc
          (7 : ZMod 2401668757) ^ 514055 = (7 : ZMod 2401668757) ^ (257027 + 257027 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 257027 * (7 : ZMod 2401668757) ^ 257027) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 210170431 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 2401668757) ^ 1028111 = 1841819919 := by
        calc
          (7 : ZMod 2401668757) ^ 1028111 = (7 : ZMod 2401668757) ^ (514055 + 514055 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 514055 * (7 : ZMod 2401668757) ^ 514055) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1841819919 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 2401668757) ^ 2056223 = 1371262528 := by
        calc
          (7 : ZMod 2401668757) ^ 2056223 = (7 : ZMod 2401668757) ^ (1028111 + 1028111 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 1028111 * (7 : ZMod 2401668757) ^ 1028111) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1371262528 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 2401668757) ^ 4112446 = 414444245 := by
        calc
          (7 : ZMod 2401668757) ^ 4112446 = (7 : ZMod 2401668757) ^ (2056223 + 2056223) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2056223 * (7 : ZMod 2401668757) ^ 2056223 := by rw [pow_add]
          _ = 414444245 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 2401668757) ^ 8224893 = 726071608 := by
        calc
          (7 : ZMod 2401668757) ^ 8224893 = (7 : ZMod 2401668757) ^ (4112446 + 4112446 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 4112446 * (7 : ZMod 2401668757) ^ 4112446) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 726071608 := by rw [factor_3_21]; decide
      have factor_3_23 : (7 : ZMod 2401668757) ^ 16449786 = 671959521 := by
        calc
          (7 : ZMod 2401668757) ^ 16449786 = (7 : ZMod 2401668757) ^ (8224893 + 8224893) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 8224893 * (7 : ZMod 2401668757) ^ 8224893 := by rw [pow_add]
          _ = 671959521 := by rw [factor_3_22]; decide
      have factor_3_24 : (7 : ZMod 2401668757) ^ 32899572 = 1319403185 := by
        calc
          (7 : ZMod 2401668757) ^ 32899572 = (7 : ZMod 2401668757) ^ (16449786 + 16449786) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 16449786 * (7 : ZMod 2401668757) ^ 16449786 := by rw [pow_add]
          _ = 1319403185 := by rw [factor_3_23]; decide
      change (7 : ZMod 2401668757) ^ 32899572 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (7 : ZMod 2401668757) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 2401668757) ^ 2 = 49 := by
        calc
          (7 : ZMod 2401668757) ^ 2 = (7 : ZMod 2401668757) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 1 * (7 : ZMod 2401668757) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 2401668757) ^ 4 = 2401 := by
        calc
          (7 : ZMod 2401668757) ^ 4 = (7 : ZMod 2401668757) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 2 * (7 : ZMod 2401668757) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 2401668757) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 2401668757) ^ 9 = (7 : ZMod 2401668757) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 4 * (7 : ZMod 2401668757) ^ 4) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 2401668757) ^ 18 = 523926711 := by
        calc
          (7 : ZMod 2401668757) ^ 18 = (7 : ZMod 2401668757) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 9 * (7 : ZMod 2401668757) ^ 9 := by rw [pow_add]
          _ = 523926711 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 2401668757) ^ 37 = 1951221856 := by
        calc
          (7 : ZMod 2401668757) ^ 37 = (7 : ZMod 2401668757) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 18 * (7 : ZMod 2401668757) ^ 18) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1951221856 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 2401668757) ^ 74 = 274266305 := by
        calc
          (7 : ZMod 2401668757) ^ 74 = (7 : ZMod 2401668757) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 37 * (7 : ZMod 2401668757) ^ 37 := by rw [pow_add]
          _ = 274266305 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 2401668757) ^ 148 = 1780932957 := by
        calc
          (7 : ZMod 2401668757) ^ 148 = (7 : ZMod 2401668757) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 74 * (7 : ZMod 2401668757) ^ 74 := by rw [pow_add]
          _ = 1780932957 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 2401668757) ^ 297 = 339065388 := by
        calc
          (7 : ZMod 2401668757) ^ 297 = (7 : ZMod 2401668757) ^ (148 + 148 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 148 * (7 : ZMod 2401668757) ^ 148) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 339065388 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 2401668757) ^ 595 = 377849505 := by
        calc
          (7 : ZMod 2401668757) ^ 595 = (7 : ZMod 2401668757) ^ (297 + 297 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 297 * (7 : ZMod 2401668757) ^ 297) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 377849505 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 2401668757) ^ 1190 = 1451227392 := by
        calc
          (7 : ZMod 2401668757) ^ 1190 = (7 : ZMod 2401668757) ^ (595 + 595) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 595 * (7 : ZMod 2401668757) ^ 595 := by rw [pow_add]
          _ = 1451227392 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 2401668757) ^ 2381 = 1015609308 := by
        calc
          (7 : ZMod 2401668757) ^ 2381 = (7 : ZMod 2401668757) ^ (1190 + 1190 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 1190 * (7 : ZMod 2401668757) ^ 1190) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 1015609308 := by rw [factor_4_10]; decide
      have factor_4_12 : (7 : ZMod 2401668757) ^ 4763 = 460002013 := by
        calc
          (7 : ZMod 2401668757) ^ 4763 = (7 : ZMod 2401668757) ^ (2381 + 2381 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 2381 * (7 : ZMod 2401668757) ^ 2381) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 460002013 := by rw [factor_4_11]; decide
      have factor_4_13 : (7 : ZMod 2401668757) ^ 9526 = 1766108937 := by
        calc
          (7 : ZMod 2401668757) ^ 9526 = (7 : ZMod 2401668757) ^ (4763 + 4763) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 4763 * (7 : ZMod 2401668757) ^ 4763 := by rw [pow_add]
          _ = 1766108937 := by rw [factor_4_12]; decide
      have factor_4_14 : (7 : ZMod 2401668757) ^ 19053 = 975887126 := by
        calc
          (7 : ZMod 2401668757) ^ 19053 = (7 : ZMod 2401668757) ^ (9526 + 9526 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = ((7 : ZMod 2401668757) ^ 9526 * (7 : ZMod 2401668757) ^ 9526) * (7 : ZMod 2401668757) := by rw [pow_succ, pow_add]
          _ = 975887126 := by rw [factor_4_13]; decide
      have factor_4_15 : (7 : ZMod 2401668757) ^ 38106 = 13540840 := by
        calc
          (7 : ZMod 2401668757) ^ 38106 = (7 : ZMod 2401668757) ^ (19053 + 19053) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 19053 * (7 : ZMod 2401668757) ^ 19053 := by rw [pow_add]
          _ = 13540840 := by rw [factor_4_14]; decide
      have factor_4_16 : (7 : ZMod 2401668757) ^ 76212 = 1348321192 := by
        calc
          (7 : ZMod 2401668757) ^ 76212 = (7 : ZMod 2401668757) ^ (38106 + 38106) :=
            congrArg (fun n : ℕ => (7 : ZMod 2401668757) ^ n) (by norm_num)
          _ = (7 : ZMod 2401668757) ^ 38106 * (7 : ZMod 2401668757) ^ 38106 := by rw [pow_add]
          _ = 1348321192 := by rw [factor_4_15]; decide
      change (7 : ZMod 2401668757) ^ 76212 ≠ 1
      rw [factor_4_16]
      decide

#print axioms prime_lucas_2401668757

end TotientTailPeriodKiller
end Erdos249257
