import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_12220560479 : Nat.Prime 12220560479 := by
  apply lucas_primality 12220560479 (7 : ZMod 12220560479)
  ·
      have fermat_0 : (7 : ZMod 12220560479) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 12220560479) ^ 2 = 49 := by
        calc
          (7 : ZMod 12220560479) ^ 2 = (7 : ZMod 12220560479) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 1 * (7 : ZMod 12220560479) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 12220560479) ^ 5 = 16807 := by
        calc
          (7 : ZMod 12220560479) ^ 5 = (7 : ZMod 12220560479) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 2 * (7 : ZMod 12220560479) ^ 2) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 12220560479) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 12220560479) ^ 11 = (7 : ZMod 12220560479) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 5 * (7 : ZMod 12220560479) ^ 5) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 12220560479) ^ 22 = 5521830957 := by
        calc
          (7 : ZMod 12220560479) ^ 22 = (7 : ZMod 12220560479) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 11 * (7 : ZMod 12220560479) ^ 11 := by rw [pow_add]
          _ = 5521830957 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 12220560479) ^ 45 = 11425902308 := by
        calc
          (7 : ZMod 12220560479) ^ 45 = (7 : ZMod 12220560479) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 22 * (7 : ZMod 12220560479) ^ 22) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 11425902308 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 12220560479) ^ 91 = 9023451965 := by
        calc
          (7 : ZMod 12220560479) ^ 91 = (7 : ZMod 12220560479) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 45 * (7 : ZMod 12220560479) ^ 45) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 9023451965 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 12220560479) ^ 182 = 9727947654 := by
        calc
          (7 : ZMod 12220560479) ^ 182 = (7 : ZMod 12220560479) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 91 * (7 : ZMod 12220560479) ^ 91 := by rw [pow_add]
          _ = 9727947654 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 12220560479) ^ 364 = 7532160304 := by
        calc
          (7 : ZMod 12220560479) ^ 364 = (7 : ZMod 12220560479) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 182 * (7 : ZMod 12220560479) ^ 182 := by rw [pow_add]
          _ = 7532160304 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 12220560479) ^ 728 = 11612627542 := by
        calc
          (7 : ZMod 12220560479) ^ 728 = (7 : ZMod 12220560479) ^ (364 + 364) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 364 * (7 : ZMod 12220560479) ^ 364 := by rw [pow_add]
          _ = 11612627542 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 12220560479) ^ 1456 = 4784644165 := by
        calc
          (7 : ZMod 12220560479) ^ 1456 = (7 : ZMod 12220560479) ^ (728 + 728) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 728 * (7 : ZMod 12220560479) ^ 728 := by rw [pow_add]
          _ = 4784644165 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 12220560479) ^ 2913 = 12010742406 := by
        calc
          (7 : ZMod 12220560479) ^ 2913 = (7 : ZMod 12220560479) ^ (1456 + 1456 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 1456 * (7 : ZMod 12220560479) ^ 1456) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 12010742406 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 12220560479) ^ 5827 = 5966630421 := by
        calc
          (7 : ZMod 12220560479) ^ 5827 = (7 : ZMod 12220560479) ^ (2913 + 2913 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 2913 * (7 : ZMod 12220560479) ^ 2913) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 5966630421 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 12220560479) ^ 11654 = 1602198032 := by
        calc
          (7 : ZMod 12220560479) ^ 11654 = (7 : ZMod 12220560479) ^ (5827 + 5827) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 5827 * (7 : ZMod 12220560479) ^ 5827 := by rw [pow_add]
          _ = 1602198032 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 12220560479) ^ 23308 = 3394819209 := by
        calc
          (7 : ZMod 12220560479) ^ 23308 = (7 : ZMod 12220560479) ^ (11654 + 11654) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 11654 * (7 : ZMod 12220560479) ^ 11654 := by rw [pow_add]
          _ = 3394819209 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 12220560479) ^ 46617 = 4005710806 := by
        calc
          (7 : ZMod 12220560479) ^ 46617 = (7 : ZMod 12220560479) ^ (23308 + 23308 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 23308 * (7 : ZMod 12220560479) ^ 23308) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 4005710806 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 12220560479) ^ 93235 = 3869877834 := by
        calc
          (7 : ZMod 12220560479) ^ 93235 = (7 : ZMod 12220560479) ^ (46617 + 46617 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 46617 * (7 : ZMod 12220560479) ^ 46617) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 3869877834 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 12220560479) ^ 186470 = 3174653136 := by
        calc
          (7 : ZMod 12220560479) ^ 186470 = (7 : ZMod 12220560479) ^ (93235 + 93235) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 93235 * (7 : ZMod 12220560479) ^ 93235 := by rw [pow_add]
          _ = 3174653136 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 12220560479) ^ 372941 = 2853246301 := by
        calc
          (7 : ZMod 12220560479) ^ 372941 = (7 : ZMod 12220560479) ^ (186470 + 186470 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 186470 * (7 : ZMod 12220560479) ^ 186470) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 2853246301 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 12220560479) ^ 745883 = 700083627 := by
        calc
          (7 : ZMod 12220560479) ^ 745883 = (7 : ZMod 12220560479) ^ (372941 + 372941 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 372941 * (7 : ZMod 12220560479) ^ 372941) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 700083627 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 12220560479) ^ 1491767 = 1768143814 := by
        calc
          (7 : ZMod 12220560479) ^ 1491767 = (7 : ZMod 12220560479) ^ (745883 + 745883 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 745883 * (7 : ZMod 12220560479) ^ 745883) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 1768143814 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 12220560479) ^ 2983535 = 1084098841 := by
        calc
          (7 : ZMod 12220560479) ^ 2983535 = (7 : ZMod 12220560479) ^ (1491767 + 1491767 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 1491767 * (7 : ZMod 12220560479) ^ 1491767) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 1084098841 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 12220560479) ^ 5967070 = 5041128915 := by
        calc
          (7 : ZMod 12220560479) ^ 5967070 = (7 : ZMod 12220560479) ^ (2983535 + 2983535) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 2983535 * (7 : ZMod 12220560479) ^ 2983535 := by rw [pow_add]
          _ = 5041128915 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 12220560479) ^ 11934141 = 7209528623 := by
        calc
          (7 : ZMod 12220560479) ^ 11934141 = (7 : ZMod 12220560479) ^ (5967070 + 5967070 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 5967070 * (7 : ZMod 12220560479) ^ 5967070) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 7209528623 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 12220560479) ^ 23868282 = 748405871 := by
        calc
          (7 : ZMod 12220560479) ^ 23868282 = (7 : ZMod 12220560479) ^ (11934141 + 11934141) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 11934141 * (7 : ZMod 12220560479) ^ 11934141 := by rw [pow_add]
          _ = 748405871 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 12220560479) ^ 47736564 = 7960131124 := by
        calc
          (7 : ZMod 12220560479) ^ 47736564 = (7 : ZMod 12220560479) ^ (23868282 + 23868282) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 23868282 * (7 : ZMod 12220560479) ^ 23868282 := by rw [pow_add]
          _ = 7960131124 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 12220560479) ^ 95473128 = 2064031799 := by
        calc
          (7 : ZMod 12220560479) ^ 95473128 = (7 : ZMod 12220560479) ^ (47736564 + 47736564) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 47736564 * (7 : ZMod 12220560479) ^ 47736564 := by rw [pow_add]
          _ = 2064031799 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 12220560479) ^ 190946257 = 5497494453 := by
        calc
          (7 : ZMod 12220560479) ^ 190946257 = (7 : ZMod 12220560479) ^ (95473128 + 95473128 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 95473128 * (7 : ZMod 12220560479) ^ 95473128) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 5497494453 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 12220560479) ^ 381892514 = 6512324732 := by
        calc
          (7 : ZMod 12220560479) ^ 381892514 = (7 : ZMod 12220560479) ^ (190946257 + 190946257) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 190946257 * (7 : ZMod 12220560479) ^ 190946257 := by rw [pow_add]
          _ = 6512324732 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 12220560479) ^ 763785029 = 9040269 := by
        calc
          (7 : ZMod 12220560479) ^ 763785029 = (7 : ZMod 12220560479) ^ (381892514 + 381892514 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 381892514 * (7 : ZMod 12220560479) ^ 381892514) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 9040269 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 12220560479) ^ 1527570059 = 4147443100 := by
        calc
          (7 : ZMod 12220560479) ^ 1527570059 = (7 : ZMod 12220560479) ^ (763785029 + 763785029 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 763785029 * (7 : ZMod 12220560479) ^ 763785029) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 4147443100 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 12220560479) ^ 3055140119 = 9506616645 := by
        calc
          (7 : ZMod 12220560479) ^ 3055140119 = (7 : ZMod 12220560479) ^ (1527570059 + 1527570059 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 1527570059 * (7 : ZMod 12220560479) ^ 1527570059) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 9506616645 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 12220560479) ^ 6110280239 = 12220560478 := by
        calc
          (7 : ZMod 12220560479) ^ 6110280239 = (7 : ZMod 12220560479) ^ (3055140119 + 3055140119 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 3055140119 * (7 : ZMod 12220560479) ^ 3055140119) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 12220560478 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 12220560479) ^ 12220560478 = 1 := by
        calc
          (7 : ZMod 12220560479) ^ 12220560478 = (7 : ZMod 12220560479) ^ (6110280239 + 6110280239) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 6110280239 * (7 : ZMod 12220560479) ^ 6110280239 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (1181, 1), (739117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (1181, 1), (739117, 1)] : List FactorBlock).map factorBlockValue).prod = 12220560479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 12220560479) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 12220560479) ^ 2 = 49 := by
        calc
          (7 : ZMod 12220560479) ^ 2 = (7 : ZMod 12220560479) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 1 * (7 : ZMod 12220560479) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 12220560479) ^ 5 = 16807 := by
        calc
          (7 : ZMod 12220560479) ^ 5 = (7 : ZMod 12220560479) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 2 * (7 : ZMod 12220560479) ^ 2) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 12220560479) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 12220560479) ^ 11 = (7 : ZMod 12220560479) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 5 * (7 : ZMod 12220560479) ^ 5) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 12220560479) ^ 22 = 5521830957 := by
        calc
          (7 : ZMod 12220560479) ^ 22 = (7 : ZMod 12220560479) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 11 * (7 : ZMod 12220560479) ^ 11 := by rw [pow_add]
          _ = 5521830957 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 12220560479) ^ 45 = 11425902308 := by
        calc
          (7 : ZMod 12220560479) ^ 45 = (7 : ZMod 12220560479) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 22 * (7 : ZMod 12220560479) ^ 22) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 11425902308 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 12220560479) ^ 91 = 9023451965 := by
        calc
          (7 : ZMod 12220560479) ^ 91 = (7 : ZMod 12220560479) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 45 * (7 : ZMod 12220560479) ^ 45) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 9023451965 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 12220560479) ^ 182 = 9727947654 := by
        calc
          (7 : ZMod 12220560479) ^ 182 = (7 : ZMod 12220560479) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 91 * (7 : ZMod 12220560479) ^ 91 := by rw [pow_add]
          _ = 9727947654 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 12220560479) ^ 364 = 7532160304 := by
        calc
          (7 : ZMod 12220560479) ^ 364 = (7 : ZMod 12220560479) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 182 * (7 : ZMod 12220560479) ^ 182 := by rw [pow_add]
          _ = 7532160304 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 12220560479) ^ 728 = 11612627542 := by
        calc
          (7 : ZMod 12220560479) ^ 728 = (7 : ZMod 12220560479) ^ (364 + 364) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 364 * (7 : ZMod 12220560479) ^ 364 := by rw [pow_add]
          _ = 11612627542 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 12220560479) ^ 1456 = 4784644165 := by
        calc
          (7 : ZMod 12220560479) ^ 1456 = (7 : ZMod 12220560479) ^ (728 + 728) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 728 * (7 : ZMod 12220560479) ^ 728 := by rw [pow_add]
          _ = 4784644165 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 12220560479) ^ 2913 = 12010742406 := by
        calc
          (7 : ZMod 12220560479) ^ 2913 = (7 : ZMod 12220560479) ^ (1456 + 1456 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 1456 * (7 : ZMod 12220560479) ^ 1456) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 12010742406 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 12220560479) ^ 5827 = 5966630421 := by
        calc
          (7 : ZMod 12220560479) ^ 5827 = (7 : ZMod 12220560479) ^ (2913 + 2913 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 2913 * (7 : ZMod 12220560479) ^ 2913) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 5966630421 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 12220560479) ^ 11654 = 1602198032 := by
        calc
          (7 : ZMod 12220560479) ^ 11654 = (7 : ZMod 12220560479) ^ (5827 + 5827) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 5827 * (7 : ZMod 12220560479) ^ 5827 := by rw [pow_add]
          _ = 1602198032 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 12220560479) ^ 23308 = 3394819209 := by
        calc
          (7 : ZMod 12220560479) ^ 23308 = (7 : ZMod 12220560479) ^ (11654 + 11654) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 11654 * (7 : ZMod 12220560479) ^ 11654 := by rw [pow_add]
          _ = 3394819209 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 12220560479) ^ 46617 = 4005710806 := by
        calc
          (7 : ZMod 12220560479) ^ 46617 = (7 : ZMod 12220560479) ^ (23308 + 23308 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 23308 * (7 : ZMod 12220560479) ^ 23308) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 4005710806 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 12220560479) ^ 93235 = 3869877834 := by
        calc
          (7 : ZMod 12220560479) ^ 93235 = (7 : ZMod 12220560479) ^ (46617 + 46617 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 46617 * (7 : ZMod 12220560479) ^ 46617) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 3869877834 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 12220560479) ^ 186470 = 3174653136 := by
        calc
          (7 : ZMod 12220560479) ^ 186470 = (7 : ZMod 12220560479) ^ (93235 + 93235) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 93235 * (7 : ZMod 12220560479) ^ 93235 := by rw [pow_add]
          _ = 3174653136 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 12220560479) ^ 372941 = 2853246301 := by
        calc
          (7 : ZMod 12220560479) ^ 372941 = (7 : ZMod 12220560479) ^ (186470 + 186470 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 186470 * (7 : ZMod 12220560479) ^ 186470) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 2853246301 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 12220560479) ^ 745883 = 700083627 := by
        calc
          (7 : ZMod 12220560479) ^ 745883 = (7 : ZMod 12220560479) ^ (372941 + 372941 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 372941 * (7 : ZMod 12220560479) ^ 372941) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 700083627 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 12220560479) ^ 1491767 = 1768143814 := by
        calc
          (7 : ZMod 12220560479) ^ 1491767 = (7 : ZMod 12220560479) ^ (745883 + 745883 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 745883 * (7 : ZMod 12220560479) ^ 745883) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 1768143814 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 12220560479) ^ 2983535 = 1084098841 := by
        calc
          (7 : ZMod 12220560479) ^ 2983535 = (7 : ZMod 12220560479) ^ (1491767 + 1491767 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 1491767 * (7 : ZMod 12220560479) ^ 1491767) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 1084098841 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 12220560479) ^ 5967070 = 5041128915 := by
        calc
          (7 : ZMod 12220560479) ^ 5967070 = (7 : ZMod 12220560479) ^ (2983535 + 2983535) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 2983535 * (7 : ZMod 12220560479) ^ 2983535 := by rw [pow_add]
          _ = 5041128915 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 12220560479) ^ 11934141 = 7209528623 := by
        calc
          (7 : ZMod 12220560479) ^ 11934141 = (7 : ZMod 12220560479) ^ (5967070 + 5967070 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 5967070 * (7 : ZMod 12220560479) ^ 5967070) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 7209528623 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 12220560479) ^ 23868282 = 748405871 := by
        calc
          (7 : ZMod 12220560479) ^ 23868282 = (7 : ZMod 12220560479) ^ (11934141 + 11934141) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 11934141 * (7 : ZMod 12220560479) ^ 11934141 := by rw [pow_add]
          _ = 748405871 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 12220560479) ^ 47736564 = 7960131124 := by
        calc
          (7 : ZMod 12220560479) ^ 47736564 = (7 : ZMod 12220560479) ^ (23868282 + 23868282) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 23868282 * (7 : ZMod 12220560479) ^ 23868282 := by rw [pow_add]
          _ = 7960131124 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 12220560479) ^ 95473128 = 2064031799 := by
        calc
          (7 : ZMod 12220560479) ^ 95473128 = (7 : ZMod 12220560479) ^ (47736564 + 47736564) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 47736564 * (7 : ZMod 12220560479) ^ 47736564 := by rw [pow_add]
          _ = 2064031799 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 12220560479) ^ 190946257 = 5497494453 := by
        calc
          (7 : ZMod 12220560479) ^ 190946257 = (7 : ZMod 12220560479) ^ (95473128 + 95473128 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 95473128 * (7 : ZMod 12220560479) ^ 95473128) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 5497494453 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 12220560479) ^ 381892514 = 6512324732 := by
        calc
          (7 : ZMod 12220560479) ^ 381892514 = (7 : ZMod 12220560479) ^ (190946257 + 190946257) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 190946257 * (7 : ZMod 12220560479) ^ 190946257 := by rw [pow_add]
          _ = 6512324732 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 12220560479) ^ 763785029 = 9040269 := by
        calc
          (7 : ZMod 12220560479) ^ 763785029 = (7 : ZMod 12220560479) ^ (381892514 + 381892514 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 381892514 * (7 : ZMod 12220560479) ^ 381892514) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 9040269 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 12220560479) ^ 1527570059 = 4147443100 := by
        calc
          (7 : ZMod 12220560479) ^ 1527570059 = (7 : ZMod 12220560479) ^ (763785029 + 763785029 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 763785029 * (7 : ZMod 12220560479) ^ 763785029) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 4147443100 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 12220560479) ^ 3055140119 = 9506616645 := by
        calc
          (7 : ZMod 12220560479) ^ 3055140119 = (7 : ZMod 12220560479) ^ (1527570059 + 1527570059 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 1527570059 * (7 : ZMod 12220560479) ^ 1527570059) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 9506616645 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 12220560479) ^ 6110280239 = 12220560478 := by
        calc
          (7 : ZMod 12220560479) ^ 6110280239 = (7 : ZMod 12220560479) ^ (3055140119 + 3055140119 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 3055140119 * (7 : ZMod 12220560479) ^ 3055140119) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 12220560478 := by rw [factor_0_31]; decide
      change (7 : ZMod 12220560479) ^ 6110280239 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (7 : ZMod 12220560479) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 12220560479) ^ 3 = 343 := by
        calc
          (7 : ZMod 12220560479) ^ 3 = (7 : ZMod 12220560479) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 1 * (7 : ZMod 12220560479) ^ 1) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 12220560479) ^ 6 = 117649 := by
        calc
          (7 : ZMod 12220560479) ^ 6 = (7 : ZMod 12220560479) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 3 * (7 : ZMod 12220560479) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 12220560479) ^ 13 = 11345087054 := by
        calc
          (7 : ZMod 12220560479) ^ 13 = (7 : ZMod 12220560479) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 6 * (7 : ZMod 12220560479) ^ 6) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 11345087054 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 12220560479) ^ 26 = 10828568521 := by
        calc
          (7 : ZMod 12220560479) ^ 26 = (7 : ZMod 12220560479) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 13 * (7 : ZMod 12220560479) ^ 13 := by rw [pow_add]
          _ = 10828568521 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 12220560479) ^ 52 = 280651555 := by
        calc
          (7 : ZMod 12220560479) ^ 52 = (7 : ZMod 12220560479) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 26 * (7 : ZMod 12220560479) ^ 26 := by rw [pow_add]
          _ = 280651555 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 12220560479) ^ 104 = 6883575014 := by
        calc
          (7 : ZMod 12220560479) ^ 104 = (7 : ZMod 12220560479) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 52 * (7 : ZMod 12220560479) ^ 52 := by rw [pow_add]
          _ = 6883575014 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 12220560479) ^ 208 = 11543471292 := by
        calc
          (7 : ZMod 12220560479) ^ 208 = (7 : ZMod 12220560479) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 104 * (7 : ZMod 12220560479) ^ 104 := by rw [pow_add]
          _ = 11543471292 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 12220560479) ^ 416 = 11272255115 := by
        calc
          (7 : ZMod 12220560479) ^ 416 = (7 : ZMod 12220560479) ^ (208 + 208) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 208 * (7 : ZMod 12220560479) ^ 208 := by rw [pow_add]
          _ = 11272255115 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 12220560479) ^ 832 = 2825059406 := by
        calc
          (7 : ZMod 12220560479) ^ 832 = (7 : ZMod 12220560479) ^ (416 + 416) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 416 * (7 : ZMod 12220560479) ^ 416 := by rw [pow_add]
          _ = 2825059406 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 12220560479) ^ 1664 = 1735517958 := by
        calc
          (7 : ZMod 12220560479) ^ 1664 = (7 : ZMod 12220560479) ^ (832 + 832) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 832 * (7 : ZMod 12220560479) ^ 832 := by rw [pow_add]
          _ = 1735517958 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 12220560479) ^ 3329 = 6774625440 := by
        calc
          (7 : ZMod 12220560479) ^ 3329 = (7 : ZMod 12220560479) ^ (1664 + 1664 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 1664 * (7 : ZMod 12220560479) ^ 1664) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 6774625440 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 12220560479) ^ 6659 = 1612571079 := by
        calc
          (7 : ZMod 12220560479) ^ 6659 = (7 : ZMod 12220560479) ^ (3329 + 3329 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 3329 * (7 : ZMod 12220560479) ^ 3329) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 1612571079 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 12220560479) ^ 13319 = 3920146929 := by
        calc
          (7 : ZMod 12220560479) ^ 13319 = (7 : ZMod 12220560479) ^ (6659 + 6659 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 6659 * (7 : ZMod 12220560479) ^ 6659) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 3920146929 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 12220560479) ^ 26638 = 523983813 := by
        calc
          (7 : ZMod 12220560479) ^ 26638 = (7 : ZMod 12220560479) ^ (13319 + 13319) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 13319 * (7 : ZMod 12220560479) ^ 13319 := by rw [pow_add]
          _ = 523983813 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 12220560479) ^ 53277 = 5525563213 := by
        calc
          (7 : ZMod 12220560479) ^ 53277 = (7 : ZMod 12220560479) ^ (26638 + 26638 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 26638 * (7 : ZMod 12220560479) ^ 26638) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 5525563213 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 12220560479) ^ 106554 = 6861743251 := by
        calc
          (7 : ZMod 12220560479) ^ 106554 = (7 : ZMod 12220560479) ^ (53277 + 53277) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 53277 * (7 : ZMod 12220560479) ^ 53277 := by rw [pow_add]
          _ = 6861743251 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 12220560479) ^ 213109 = 5449271040 := by
        calc
          (7 : ZMod 12220560479) ^ 213109 = (7 : ZMod 12220560479) ^ (106554 + 106554 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 106554 * (7 : ZMod 12220560479) ^ 106554) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 5449271040 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 12220560479) ^ 426219 = 10090921847 := by
        calc
          (7 : ZMod 12220560479) ^ 426219 = (7 : ZMod 12220560479) ^ (213109 + 213109 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 213109 * (7 : ZMod 12220560479) ^ 213109) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 10090921847 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 12220560479) ^ 852438 = 1399752849 := by
        calc
          (7 : ZMod 12220560479) ^ 852438 = (7 : ZMod 12220560479) ^ (426219 + 426219) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 426219 * (7 : ZMod 12220560479) ^ 426219 := by rw [pow_add]
          _ = 1399752849 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 12220560479) ^ 1704877 = 3069505105 := by
        calc
          (7 : ZMod 12220560479) ^ 1704877 = (7 : ZMod 12220560479) ^ (852438 + 852438 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 852438 * (7 : ZMod 12220560479) ^ 852438) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 3069505105 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 12220560479) ^ 3409754 = 3291049593 := by
        calc
          (7 : ZMod 12220560479) ^ 3409754 = (7 : ZMod 12220560479) ^ (1704877 + 1704877) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 1704877 * (7 : ZMod 12220560479) ^ 1704877 := by rw [pow_add]
          _ = 3291049593 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 12220560479) ^ 6819509 = 2298467914 := by
        calc
          (7 : ZMod 12220560479) ^ 6819509 = (7 : ZMod 12220560479) ^ (3409754 + 3409754 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 3409754 * (7 : ZMod 12220560479) ^ 3409754) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 2298467914 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 12220560479) ^ 13639018 = 4159878484 := by
        calc
          (7 : ZMod 12220560479) ^ 13639018 = (7 : ZMod 12220560479) ^ (6819509 + 6819509) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 6819509 * (7 : ZMod 12220560479) ^ 6819509 := by rw [pow_add]
          _ = 4159878484 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 12220560479) ^ 27278036 = 9713425428 := by
        calc
          (7 : ZMod 12220560479) ^ 27278036 = (7 : ZMod 12220560479) ^ (13639018 + 13639018) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 13639018 * (7 : ZMod 12220560479) ^ 13639018 := by rw [pow_add]
          _ = 9713425428 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 12220560479) ^ 54556073 = 4707426616 := by
        calc
          (7 : ZMod 12220560479) ^ 54556073 = (7 : ZMod 12220560479) ^ (27278036 + 27278036 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 27278036 * (7 : ZMod 12220560479) ^ 27278036) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 4707426616 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 12220560479) ^ 109112147 = 4435029864 := by
        calc
          (7 : ZMod 12220560479) ^ 109112147 = (7 : ZMod 12220560479) ^ (54556073 + 54556073 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 54556073 * (7 : ZMod 12220560479) ^ 54556073) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 4435029864 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 12220560479) ^ 218224294 = 11310806910 := by
        calc
          (7 : ZMod 12220560479) ^ 218224294 = (7 : ZMod 12220560479) ^ (109112147 + 109112147) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 109112147 * (7 : ZMod 12220560479) ^ 109112147 := by rw [pow_add]
          _ = 11310806910 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 12220560479) ^ 436448588 = 7561730474 := by
        calc
          (7 : ZMod 12220560479) ^ 436448588 = (7 : ZMod 12220560479) ^ (218224294 + 218224294) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 218224294 * (7 : ZMod 12220560479) ^ 218224294 := by rw [pow_add]
          _ = 7561730474 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 12220560479) ^ 872897177 = 3390693803 := by
        calc
          (7 : ZMod 12220560479) ^ 872897177 = (7 : ZMod 12220560479) ^ (436448588 + 436448588 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 436448588 * (7 : ZMod 12220560479) ^ 436448588) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 3390693803 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 12220560479) ^ 1745794354 = 8645356275 := by
        calc
          (7 : ZMod 12220560479) ^ 1745794354 = (7 : ZMod 12220560479) ^ (872897177 + 872897177) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 872897177 * (7 : ZMod 12220560479) ^ 872897177 := by rw [pow_add]
          _ = 8645356275 := by rw [factor_1_29]; decide
      change (7 : ZMod 12220560479) ^ 1745794354 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (7 : ZMod 12220560479) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 12220560479) ^ 2 = 49 := by
        calc
          (7 : ZMod 12220560479) ^ 2 = (7 : ZMod 12220560479) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 1 * (7 : ZMod 12220560479) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 12220560479) ^ 4 = 2401 := by
        calc
          (7 : ZMod 12220560479) ^ 4 = (7 : ZMod 12220560479) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 2 * (7 : ZMod 12220560479) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 12220560479) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 12220560479) ^ 9 = (7 : ZMod 12220560479) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 4 * (7 : ZMod 12220560479) ^ 4) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 12220560479) ^ 19 = 8531299666 := by
        calc
          (7 : ZMod 12220560479) ^ 19 = (7 : ZMod 12220560479) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 9 * (7 : ZMod 12220560479) ^ 9) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 8531299666 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 12220560479) ^ 39 = 5146383516 := by
        calc
          (7 : ZMod 12220560479) ^ 39 = (7 : ZMod 12220560479) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 19 * (7 : ZMod 12220560479) ^ 19) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 5146383516 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 12220560479) ^ 78 = 6793272527 := by
        calc
          (7 : ZMod 12220560479) ^ 78 = (7 : ZMod 12220560479) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 39 * (7 : ZMod 12220560479) ^ 39 := by rw [pow_add]
          _ = 6793272527 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 12220560479) ^ 157 = 6997311581 := by
        calc
          (7 : ZMod 12220560479) ^ 157 = (7 : ZMod 12220560479) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 78 * (7 : ZMod 12220560479) ^ 78) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 6997311581 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 12220560479) ^ 315 = 7780896100 := by
        calc
          (7 : ZMod 12220560479) ^ 315 = (7 : ZMod 12220560479) ^ (157 + 157 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 157 * (7 : ZMod 12220560479) ^ 157) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 7780896100 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 12220560479) ^ 631 = 1798742852 := by
        calc
          (7 : ZMod 12220560479) ^ 631 = (7 : ZMod 12220560479) ^ (315 + 315 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 315 * (7 : ZMod 12220560479) ^ 315) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 1798742852 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 12220560479) ^ 1263 = 11907802721 := by
        calc
          (7 : ZMod 12220560479) ^ 1263 = (7 : ZMod 12220560479) ^ (631 + 631 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 631 * (7 : ZMod 12220560479) ^ 631) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 11907802721 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 12220560479) ^ 2526 = 4109752015 := by
        calc
          (7 : ZMod 12220560479) ^ 2526 = (7 : ZMod 12220560479) ^ (1263 + 1263) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 1263 * (7 : ZMod 12220560479) ^ 1263 := by rw [pow_add]
          _ = 4109752015 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 12220560479) ^ 5052 = 7945041149 := by
        calc
          (7 : ZMod 12220560479) ^ 5052 = (7 : ZMod 12220560479) ^ (2526 + 2526) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 2526 * (7 : ZMod 12220560479) ^ 2526 := by rw [pow_add]
          _ = 7945041149 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 12220560479) ^ 10105 = 10535954336 := by
        calc
          (7 : ZMod 12220560479) ^ 10105 = (7 : ZMod 12220560479) ^ (5052 + 5052 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 5052 * (7 : ZMod 12220560479) ^ 5052) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 10535954336 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 12220560479) ^ 20210 = 1277455985 := by
        calc
          (7 : ZMod 12220560479) ^ 20210 = (7 : ZMod 12220560479) ^ (10105 + 10105) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 10105 * (7 : ZMod 12220560479) ^ 10105 := by rw [pow_add]
          _ = 1277455985 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 12220560479) ^ 40420 = 10714942723 := by
        calc
          (7 : ZMod 12220560479) ^ 40420 = (7 : ZMod 12220560479) ^ (20210 + 20210) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 20210 * (7 : ZMod 12220560479) ^ 20210 := by rw [pow_add]
          _ = 10714942723 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 12220560479) ^ 80840 = 4364717951 := by
        calc
          (7 : ZMod 12220560479) ^ 80840 = (7 : ZMod 12220560479) ^ (40420 + 40420) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 40420 * (7 : ZMod 12220560479) ^ 40420 := by rw [pow_add]
          _ = 4364717951 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 12220560479) ^ 161681 = 5563489319 := by
        calc
          (7 : ZMod 12220560479) ^ 161681 = (7 : ZMod 12220560479) ^ (80840 + 80840 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 80840 * (7 : ZMod 12220560479) ^ 80840) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 5563489319 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 12220560479) ^ 323363 = 282476824 := by
        calc
          (7 : ZMod 12220560479) ^ 323363 = (7 : ZMod 12220560479) ^ (161681 + 161681 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 161681 * (7 : ZMod 12220560479) ^ 161681) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 282476824 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 12220560479) ^ 646727 = 10865948362 := by
        calc
          (7 : ZMod 12220560479) ^ 646727 = (7 : ZMod 12220560479) ^ (323363 + 323363 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 323363 * (7 : ZMod 12220560479) ^ 323363) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 10865948362 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 12220560479) ^ 1293454 = 5995144339 := by
        calc
          (7 : ZMod 12220560479) ^ 1293454 = (7 : ZMod 12220560479) ^ (646727 + 646727) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 646727 * (7 : ZMod 12220560479) ^ 646727 := by rw [pow_add]
          _ = 5995144339 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 12220560479) ^ 2586909 = 8528588684 := by
        calc
          (7 : ZMod 12220560479) ^ 2586909 = (7 : ZMod 12220560479) ^ (1293454 + 1293454 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 1293454 * (7 : ZMod 12220560479) ^ 1293454) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 8528588684 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 12220560479) ^ 5173819 = 2192527042 := by
        calc
          (7 : ZMod 12220560479) ^ 5173819 = (7 : ZMod 12220560479) ^ (2586909 + 2586909 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 2586909 * (7 : ZMod 12220560479) ^ 2586909) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 2192527042 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 12220560479) ^ 10347638 = 10597940270 := by
        calc
          (7 : ZMod 12220560479) ^ 10347638 = (7 : ZMod 12220560479) ^ (5173819 + 5173819) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 5173819 * (7 : ZMod 12220560479) ^ 5173819 := by rw [pow_add]
          _ = 10597940270 := by rw [factor_2_22]; decide
      change (7 : ZMod 12220560479) ^ 10347638 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (7 : ZMod 12220560479) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 12220560479) ^ 2 = 49 := by
        calc
          (7 : ZMod 12220560479) ^ 2 = (7 : ZMod 12220560479) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 1 * (7 : ZMod 12220560479) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 12220560479) ^ 4 = 2401 := by
        calc
          (7 : ZMod 12220560479) ^ 4 = (7 : ZMod 12220560479) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 2 * (7 : ZMod 12220560479) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 12220560479) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 12220560479) ^ 8 = (7 : ZMod 12220560479) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 4 * (7 : ZMod 12220560479) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 12220560479) ^ 16 = 5226627200 := by
        calc
          (7 : ZMod 12220560479) ^ 16 = (7 : ZMod 12220560479) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 8 * (7 : ZMod 12220560479) ^ 8 := by rw [pow_add]
          _ = 5226627200 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 12220560479) ^ 32 = 1269112337 := by
        calc
          (7 : ZMod 12220560479) ^ 32 = (7 : ZMod 12220560479) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 16 * (7 : ZMod 12220560479) ^ 16 := by rw [pow_add]
          _ = 1269112337 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 12220560479) ^ 64 = 9562972745 := by
        calc
          (7 : ZMod 12220560479) ^ 64 = (7 : ZMod 12220560479) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 32 * (7 : ZMod 12220560479) ^ 32 := by rw [pow_add]
          _ = 9562972745 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 12220560479) ^ 129 = 5506371002 := by
        calc
          (7 : ZMod 12220560479) ^ 129 = (7 : ZMod 12220560479) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 64 * (7 : ZMod 12220560479) ^ 64) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 5506371002 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 12220560479) ^ 258 = 8263214075 := by
        calc
          (7 : ZMod 12220560479) ^ 258 = (7 : ZMod 12220560479) ^ (129 + 129) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 129 * (7 : ZMod 12220560479) ^ 129 := by rw [pow_add]
          _ = 8263214075 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 12220560479) ^ 516 = 679252575 := by
        calc
          (7 : ZMod 12220560479) ^ 516 = (7 : ZMod 12220560479) ^ (258 + 258) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 258 * (7 : ZMod 12220560479) ^ 258 := by rw [pow_add]
          _ = 679252575 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 12220560479) ^ 1033 = 10824317861 := by
        calc
          (7 : ZMod 12220560479) ^ 1033 = (7 : ZMod 12220560479) ^ (516 + 516 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 516 * (7 : ZMod 12220560479) ^ 516) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 10824317861 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 12220560479) ^ 2066 = 7955804582 := by
        calc
          (7 : ZMod 12220560479) ^ 2066 = (7 : ZMod 12220560479) ^ (1033 + 1033) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 1033 * (7 : ZMod 12220560479) ^ 1033 := by rw [pow_add]
          _ = 7955804582 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 12220560479) ^ 4133 = 904536835 := by
        calc
          (7 : ZMod 12220560479) ^ 4133 = (7 : ZMod 12220560479) ^ (2066 + 2066 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 2066 * (7 : ZMod 12220560479) ^ 2066) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 904536835 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 12220560479) ^ 8267 = 4222503998 := by
        calc
          (7 : ZMod 12220560479) ^ 8267 = (7 : ZMod 12220560479) ^ (4133 + 4133 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = ((7 : ZMod 12220560479) ^ 4133 * (7 : ZMod 12220560479) ^ 4133) * (7 : ZMod 12220560479) := by rw [pow_succ, pow_add]
          _ = 4222503998 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 12220560479) ^ 16534 = 5885486114 := by
        calc
          (7 : ZMod 12220560479) ^ 16534 = (7 : ZMod 12220560479) ^ (8267 + 8267) :=
            congrArg (fun n : ℕ => (7 : ZMod 12220560479) ^ n) (by norm_num)
          _ = (7 : ZMod 12220560479) ^ 8267 * (7 : ZMod 12220560479) ^ 8267 := by rw [pow_add]
          _ = 5885486114 := by rw [factor_3_13]; decide
      change (7 : ZMod 12220560479) ^ 16534 ≠ 1
      rw [factor_3_14]
      decide

#print axioms prime_lucas_12220560479

end TotientTailPeriodKiller
end Erdos249257
