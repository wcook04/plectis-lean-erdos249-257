import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_4758099209 : Nat.Prime 4758099209 := by
  apply lucas_primality 4758099209 (3 : ZMod 4758099209)
  ·
      have fermat_0 : (3 : ZMod 4758099209) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 4758099209) ^ 2 = 9 := by
        calc
          (3 : ZMod 4758099209) ^ 2 = (3 : ZMod 4758099209) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1 * (3 : ZMod 4758099209) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 4758099209) ^ 4 = 81 := by
        calc
          (3 : ZMod 4758099209) ^ 4 = (3 : ZMod 4758099209) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 2 * (3 : ZMod 4758099209) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 4758099209) ^ 8 = 6561 := by
        calc
          (3 : ZMod 4758099209) ^ 8 = (3 : ZMod 4758099209) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 4 * (3 : ZMod 4758099209) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 4758099209) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 4758099209) ^ 17 = (3 : ZMod 4758099209) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 8 * (3 : ZMod 4758099209) ^ 8) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 4758099209) ^ 35 = 3447686064 := by
        calc
          (3 : ZMod 4758099209) ^ 35 = (3 : ZMod 4758099209) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 17 * (3 : ZMod 4758099209) ^ 17) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3447686064 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 4758099209) ^ 70 = 3269731349 := by
        calc
          (3 : ZMod 4758099209) ^ 70 = (3 : ZMod 4758099209) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 35 * (3 : ZMod 4758099209) ^ 35 := by rw [pow_add]
          _ = 3269731349 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 4758099209) ^ 141 = 1269154037 := by
        calc
          (3 : ZMod 4758099209) ^ 141 = (3 : ZMod 4758099209) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 70 * (3 : ZMod 4758099209) ^ 70) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 1269154037 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 4758099209) ^ 283 = 1296013449 := by
        calc
          (3 : ZMod 4758099209) ^ 283 = (3 : ZMod 4758099209) ^ (141 + 141 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 141 * (3 : ZMod 4758099209) ^ 141) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 1296013449 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 4758099209) ^ 567 = 3736592592 := by
        calc
          (3 : ZMod 4758099209) ^ 567 = (3 : ZMod 4758099209) ^ (283 + 283 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 283 * (3 : ZMod 4758099209) ^ 283) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3736592592 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 4758099209) ^ 1134 = 3151975741 := by
        calc
          (3 : ZMod 4758099209) ^ 1134 = (3 : ZMod 4758099209) ^ (567 + 567) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 567 * (3 : ZMod 4758099209) ^ 567 := by rw [pow_add]
          _ = 3151975741 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 4758099209) ^ 2268 = 3008135571 := by
        calc
          (3 : ZMod 4758099209) ^ 2268 = (3 : ZMod 4758099209) ^ (1134 + 1134) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1134 * (3 : ZMod 4758099209) ^ 1134 := by rw [pow_add]
          _ = 3008135571 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 4758099209) ^ 4537 = 3915149794 := by
        calc
          (3 : ZMod 4758099209) ^ 4537 = (3 : ZMod 4758099209) ^ (2268 + 2268 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 2268 * (3 : ZMod 4758099209) ^ 2268) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3915149794 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 4758099209) ^ 9075 = 883150473 := by
        calc
          (3 : ZMod 4758099209) ^ 9075 = (3 : ZMod 4758099209) ^ (4537 + 4537 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 4537 * (3 : ZMod 4758099209) ^ 4537) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 883150473 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 4758099209) ^ 18150 = 3230129438 := by
        calc
          (3 : ZMod 4758099209) ^ 18150 = (3 : ZMod 4758099209) ^ (9075 + 9075) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 9075 * (3 : ZMod 4758099209) ^ 9075 := by rw [pow_add]
          _ = 3230129438 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 4758099209) ^ 36301 = 2232883452 := by
        calc
          (3 : ZMod 4758099209) ^ 36301 = (3 : ZMod 4758099209) ^ (18150 + 18150 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 18150 * (3 : ZMod 4758099209) ^ 18150) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 2232883452 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 4758099209) ^ 72602 = 1848630776 := by
        calc
          (3 : ZMod 4758099209) ^ 72602 = (3 : ZMod 4758099209) ^ (36301 + 36301) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 36301 * (3 : ZMod 4758099209) ^ 36301 := by rw [pow_add]
          _ = 1848630776 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 4758099209) ^ 145205 = 1743118536 := by
        calc
          (3 : ZMod 4758099209) ^ 145205 = (3 : ZMod 4758099209) ^ (72602 + 72602 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 72602 * (3 : ZMod 4758099209) ^ 72602) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 1743118536 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 4758099209) ^ 290411 = 2300563535 := by
        calc
          (3 : ZMod 4758099209) ^ 290411 = (3 : ZMod 4758099209) ^ (145205 + 145205 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 145205 * (3 : ZMod 4758099209) ^ 145205) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 2300563535 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 4758099209) ^ 580822 = 3049399805 := by
        calc
          (3 : ZMod 4758099209) ^ 580822 = (3 : ZMod 4758099209) ^ (290411 + 290411) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 290411 * (3 : ZMod 4758099209) ^ 290411 := by rw [pow_add]
          _ = 3049399805 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 4758099209) ^ 1161645 = 3925747516 := by
        calc
          (3 : ZMod 4758099209) ^ 1161645 = (3 : ZMod 4758099209) ^ (580822 + 580822 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 580822 * (3 : ZMod 4758099209) ^ 580822) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3925747516 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 4758099209) ^ 2323290 = 1032069324 := by
        calc
          (3 : ZMod 4758099209) ^ 2323290 = (3 : ZMod 4758099209) ^ (1161645 + 1161645) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1161645 * (3 : ZMod 4758099209) ^ 1161645 := by rw [pow_add]
          _ = 1032069324 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 4758099209) ^ 4646581 = 4574806317 := by
        calc
          (3 : ZMod 4758099209) ^ 4646581 = (3 : ZMod 4758099209) ^ (2323290 + 2323290 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 2323290 * (3 : ZMod 4758099209) ^ 2323290) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 4574806317 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 4758099209) ^ 9293162 = 2360665506 := by
        calc
          (3 : ZMod 4758099209) ^ 9293162 = (3 : ZMod 4758099209) ^ (4646581 + 4646581) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 4646581 * (3 : ZMod 4758099209) ^ 4646581 := by rw [pow_add]
          _ = 2360665506 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 4758099209) ^ 18586325 = 4029655263 := by
        calc
          (3 : ZMod 4758099209) ^ 18586325 = (3 : ZMod 4758099209) ^ (9293162 + 9293162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 9293162 * (3 : ZMod 4758099209) ^ 9293162) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 4029655263 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 4758099209) ^ 37172650 = 2654993802 := by
        calc
          (3 : ZMod 4758099209) ^ 37172650 = (3 : ZMod 4758099209) ^ (18586325 + 18586325) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 18586325 * (3 : ZMod 4758099209) ^ 18586325 := by rw [pow_add]
          _ = 2654993802 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 4758099209) ^ 74345300 = 276889475 := by
        calc
          (3 : ZMod 4758099209) ^ 74345300 = (3 : ZMod 4758099209) ^ (37172650 + 37172650) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 37172650 * (3 : ZMod 4758099209) ^ 37172650 := by rw [pow_add]
          _ = 276889475 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 4758099209) ^ 148690600 = 662146426 := by
        calc
          (3 : ZMod 4758099209) ^ 148690600 = (3 : ZMod 4758099209) ^ (74345300 + 74345300) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 74345300 * (3 : ZMod 4758099209) ^ 74345300 := by rw [pow_add]
          _ = 662146426 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 4758099209) ^ 297381200 = 2024139912 := by
        calc
          (3 : ZMod 4758099209) ^ 297381200 = (3 : ZMod 4758099209) ^ (148690600 + 148690600) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 148690600 * (3 : ZMod 4758099209) ^ 148690600 := by rw [pow_add]
          _ = 2024139912 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 4758099209) ^ 594762401 = 3236252210 := by
        calc
          (3 : ZMod 4758099209) ^ 594762401 = (3 : ZMod 4758099209) ^ (297381200 + 297381200 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 297381200 * (3 : ZMod 4758099209) ^ 297381200) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3236252210 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 4758099209) ^ 1189524802 = 4415199277 := by
        calc
          (3 : ZMod 4758099209) ^ 1189524802 = (3 : ZMod 4758099209) ^ (594762401 + 594762401) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 594762401 * (3 : ZMod 4758099209) ^ 594762401 := by rw [pow_add]
          _ = 4415199277 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 4758099209) ^ 2379049604 = 4758099208 := by
        calc
          (3 : ZMod 4758099209) ^ 2379049604 = (3 : ZMod 4758099209) ^ (1189524802 + 1189524802) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1189524802 * (3 : ZMod 4758099209) ^ 1189524802 := by rw [pow_add]
          _ = 4758099208 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 4758099209) ^ 4758099208 = 1 := by
        calc
          (3 : ZMod 4758099209) ^ 4758099208 = (3 : ZMod 4758099209) ^ (2379049604 + 2379049604) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 2379049604 * (3 : ZMod 4758099209) ^ 2379049604 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (131, 1), (4540171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (131, 1), (4540171, 1)] : List FactorBlock).map factorBlockValue).prod = 4758099209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 4758099209) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 4758099209) ^ 2 = 9 := by
        calc
          (3 : ZMod 4758099209) ^ 2 = (3 : ZMod 4758099209) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1 * (3 : ZMod 4758099209) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 4758099209) ^ 4 = 81 := by
        calc
          (3 : ZMod 4758099209) ^ 4 = (3 : ZMod 4758099209) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 2 * (3 : ZMod 4758099209) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 4758099209) ^ 8 = 6561 := by
        calc
          (3 : ZMod 4758099209) ^ 8 = (3 : ZMod 4758099209) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 4 * (3 : ZMod 4758099209) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 4758099209) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 4758099209) ^ 17 = (3 : ZMod 4758099209) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 8 * (3 : ZMod 4758099209) ^ 8) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 4758099209) ^ 35 = 3447686064 := by
        calc
          (3 : ZMod 4758099209) ^ 35 = (3 : ZMod 4758099209) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 17 * (3 : ZMod 4758099209) ^ 17) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3447686064 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 4758099209) ^ 70 = 3269731349 := by
        calc
          (3 : ZMod 4758099209) ^ 70 = (3 : ZMod 4758099209) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 35 * (3 : ZMod 4758099209) ^ 35 := by rw [pow_add]
          _ = 3269731349 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 4758099209) ^ 141 = 1269154037 := by
        calc
          (3 : ZMod 4758099209) ^ 141 = (3 : ZMod 4758099209) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 70 * (3 : ZMod 4758099209) ^ 70) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 1269154037 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 4758099209) ^ 283 = 1296013449 := by
        calc
          (3 : ZMod 4758099209) ^ 283 = (3 : ZMod 4758099209) ^ (141 + 141 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 141 * (3 : ZMod 4758099209) ^ 141) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 1296013449 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 4758099209) ^ 567 = 3736592592 := by
        calc
          (3 : ZMod 4758099209) ^ 567 = (3 : ZMod 4758099209) ^ (283 + 283 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 283 * (3 : ZMod 4758099209) ^ 283) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3736592592 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 4758099209) ^ 1134 = 3151975741 := by
        calc
          (3 : ZMod 4758099209) ^ 1134 = (3 : ZMod 4758099209) ^ (567 + 567) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 567 * (3 : ZMod 4758099209) ^ 567 := by rw [pow_add]
          _ = 3151975741 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 4758099209) ^ 2268 = 3008135571 := by
        calc
          (3 : ZMod 4758099209) ^ 2268 = (3 : ZMod 4758099209) ^ (1134 + 1134) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1134 * (3 : ZMod 4758099209) ^ 1134 := by rw [pow_add]
          _ = 3008135571 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 4758099209) ^ 4537 = 3915149794 := by
        calc
          (3 : ZMod 4758099209) ^ 4537 = (3 : ZMod 4758099209) ^ (2268 + 2268 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 2268 * (3 : ZMod 4758099209) ^ 2268) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3915149794 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 4758099209) ^ 9075 = 883150473 := by
        calc
          (3 : ZMod 4758099209) ^ 9075 = (3 : ZMod 4758099209) ^ (4537 + 4537 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 4537 * (3 : ZMod 4758099209) ^ 4537) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 883150473 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 4758099209) ^ 18150 = 3230129438 := by
        calc
          (3 : ZMod 4758099209) ^ 18150 = (3 : ZMod 4758099209) ^ (9075 + 9075) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 9075 * (3 : ZMod 4758099209) ^ 9075 := by rw [pow_add]
          _ = 3230129438 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 4758099209) ^ 36301 = 2232883452 := by
        calc
          (3 : ZMod 4758099209) ^ 36301 = (3 : ZMod 4758099209) ^ (18150 + 18150 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 18150 * (3 : ZMod 4758099209) ^ 18150) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 2232883452 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 4758099209) ^ 72602 = 1848630776 := by
        calc
          (3 : ZMod 4758099209) ^ 72602 = (3 : ZMod 4758099209) ^ (36301 + 36301) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 36301 * (3 : ZMod 4758099209) ^ 36301 := by rw [pow_add]
          _ = 1848630776 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 4758099209) ^ 145205 = 1743118536 := by
        calc
          (3 : ZMod 4758099209) ^ 145205 = (3 : ZMod 4758099209) ^ (72602 + 72602 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 72602 * (3 : ZMod 4758099209) ^ 72602) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 1743118536 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 4758099209) ^ 290411 = 2300563535 := by
        calc
          (3 : ZMod 4758099209) ^ 290411 = (3 : ZMod 4758099209) ^ (145205 + 145205 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 145205 * (3 : ZMod 4758099209) ^ 145205) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 2300563535 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 4758099209) ^ 580822 = 3049399805 := by
        calc
          (3 : ZMod 4758099209) ^ 580822 = (3 : ZMod 4758099209) ^ (290411 + 290411) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 290411 * (3 : ZMod 4758099209) ^ 290411 := by rw [pow_add]
          _ = 3049399805 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 4758099209) ^ 1161645 = 3925747516 := by
        calc
          (3 : ZMod 4758099209) ^ 1161645 = (3 : ZMod 4758099209) ^ (580822 + 580822 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 580822 * (3 : ZMod 4758099209) ^ 580822) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3925747516 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 4758099209) ^ 2323290 = 1032069324 := by
        calc
          (3 : ZMod 4758099209) ^ 2323290 = (3 : ZMod 4758099209) ^ (1161645 + 1161645) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1161645 * (3 : ZMod 4758099209) ^ 1161645 := by rw [pow_add]
          _ = 1032069324 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 4758099209) ^ 4646581 = 4574806317 := by
        calc
          (3 : ZMod 4758099209) ^ 4646581 = (3 : ZMod 4758099209) ^ (2323290 + 2323290 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 2323290 * (3 : ZMod 4758099209) ^ 2323290) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 4574806317 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 4758099209) ^ 9293162 = 2360665506 := by
        calc
          (3 : ZMod 4758099209) ^ 9293162 = (3 : ZMod 4758099209) ^ (4646581 + 4646581) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 4646581 * (3 : ZMod 4758099209) ^ 4646581 := by rw [pow_add]
          _ = 2360665506 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 4758099209) ^ 18586325 = 4029655263 := by
        calc
          (3 : ZMod 4758099209) ^ 18586325 = (3 : ZMod 4758099209) ^ (9293162 + 9293162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 9293162 * (3 : ZMod 4758099209) ^ 9293162) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 4029655263 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 4758099209) ^ 37172650 = 2654993802 := by
        calc
          (3 : ZMod 4758099209) ^ 37172650 = (3 : ZMod 4758099209) ^ (18586325 + 18586325) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 18586325 * (3 : ZMod 4758099209) ^ 18586325 := by rw [pow_add]
          _ = 2654993802 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 4758099209) ^ 74345300 = 276889475 := by
        calc
          (3 : ZMod 4758099209) ^ 74345300 = (3 : ZMod 4758099209) ^ (37172650 + 37172650) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 37172650 * (3 : ZMod 4758099209) ^ 37172650 := by rw [pow_add]
          _ = 276889475 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 4758099209) ^ 148690600 = 662146426 := by
        calc
          (3 : ZMod 4758099209) ^ 148690600 = (3 : ZMod 4758099209) ^ (74345300 + 74345300) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 74345300 * (3 : ZMod 4758099209) ^ 74345300 := by rw [pow_add]
          _ = 662146426 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 4758099209) ^ 297381200 = 2024139912 := by
        calc
          (3 : ZMod 4758099209) ^ 297381200 = (3 : ZMod 4758099209) ^ (148690600 + 148690600) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 148690600 * (3 : ZMod 4758099209) ^ 148690600 := by rw [pow_add]
          _ = 2024139912 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 4758099209) ^ 594762401 = 3236252210 := by
        calc
          (3 : ZMod 4758099209) ^ 594762401 = (3 : ZMod 4758099209) ^ (297381200 + 297381200 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 297381200 * (3 : ZMod 4758099209) ^ 297381200) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3236252210 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 4758099209) ^ 1189524802 = 4415199277 := by
        calc
          (3 : ZMod 4758099209) ^ 1189524802 = (3 : ZMod 4758099209) ^ (594762401 + 594762401) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 594762401 * (3 : ZMod 4758099209) ^ 594762401 := by rw [pow_add]
          _ = 4415199277 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 4758099209) ^ 2379049604 = 4758099208 := by
        calc
          (3 : ZMod 4758099209) ^ 2379049604 = (3 : ZMod 4758099209) ^ (1189524802 + 1189524802) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1189524802 * (3 : ZMod 4758099209) ^ 1189524802 := by rw [pow_add]
          _ = 4758099208 := by rw [factor_0_30]; decide
      change (3 : ZMod 4758099209) ^ 2379049604 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (3 : ZMod 4758099209) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 4758099209) ^ 2 = 9 := by
        calc
          (3 : ZMod 4758099209) ^ 2 = (3 : ZMod 4758099209) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1 * (3 : ZMod 4758099209) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 4758099209) ^ 4 = 81 := by
        calc
          (3 : ZMod 4758099209) ^ 4 = (3 : ZMod 4758099209) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 2 * (3 : ZMod 4758099209) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 4758099209) ^ 8 = 6561 := by
        calc
          (3 : ZMod 4758099209) ^ 8 = (3 : ZMod 4758099209) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 4 * (3 : ZMod 4758099209) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 4758099209) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 4758099209) ^ 17 = (3 : ZMod 4758099209) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 8 * (3 : ZMod 4758099209) ^ 8) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 4758099209) ^ 34 = 1149228688 := by
        calc
          (3 : ZMod 4758099209) ^ 34 = (3 : ZMod 4758099209) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 17 * (3 : ZMod 4758099209) ^ 17 := by rw [pow_add]
          _ = 1149228688 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 4758099209) ^ 69 = 4261976589 := by
        calc
          (3 : ZMod 4758099209) ^ 69 = (3 : ZMod 4758099209) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 34 * (3 : ZMod 4758099209) ^ 34) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 4261976589 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 4758099209) ^ 138 = 1985490568 := by
        calc
          (3 : ZMod 4758099209) ^ 138 = (3 : ZMod 4758099209) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 69 * (3 : ZMod 4758099209) ^ 69 := by rw [pow_add]
          _ = 1985490568 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 4758099209) ^ 277 = 3545876384 := by
        calc
          (3 : ZMod 4758099209) ^ 277 = (3 : ZMod 4758099209) ^ (138 + 138 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 138 * (3 : ZMod 4758099209) ^ 138) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 3545876384 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 4758099209) ^ 554 = 2473226215 := by
        calc
          (3 : ZMod 4758099209) ^ 554 = (3 : ZMod 4758099209) ^ (277 + 277) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 277 * (3 : ZMod 4758099209) ^ 277 := by rw [pow_add]
          _ = 2473226215 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 4758099209) ^ 1108 = 2623390056 := by
        calc
          (3 : ZMod 4758099209) ^ 1108 = (3 : ZMod 4758099209) ^ (554 + 554) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 554 * (3 : ZMod 4758099209) ^ 554 := by rw [pow_add]
          _ = 2623390056 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 4758099209) ^ 2216 = 466672341 := by
        calc
          (3 : ZMod 4758099209) ^ 2216 = (3 : ZMod 4758099209) ^ (1108 + 1108) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1108 * (3 : ZMod 4758099209) ^ 1108 := by rw [pow_add]
          _ = 466672341 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 4758099209) ^ 4433 = 2294700795 := by
        calc
          (3 : ZMod 4758099209) ^ 4433 = (3 : ZMod 4758099209) ^ (2216 + 2216 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 2216 * (3 : ZMod 4758099209) ^ 2216) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 2294700795 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 4758099209) ^ 8867 = 4022141142 := by
        calc
          (3 : ZMod 4758099209) ^ 8867 = (3 : ZMod 4758099209) ^ (4433 + 4433 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 4433 * (3 : ZMod 4758099209) ^ 4433) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 4022141142 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 4758099209) ^ 17735 = 1686515668 := by
        calc
          (3 : ZMod 4758099209) ^ 17735 = (3 : ZMod 4758099209) ^ (8867 + 8867 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 8867 * (3 : ZMod 4758099209) ^ 8867) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 1686515668 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 4758099209) ^ 35470 = 3133674906 := by
        calc
          (3 : ZMod 4758099209) ^ 35470 = (3 : ZMod 4758099209) ^ (17735 + 17735) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 17735 * (3 : ZMod 4758099209) ^ 17735 := by rw [pow_add]
          _ = 3133674906 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 4758099209) ^ 70940 = 1068188528 := by
        calc
          (3 : ZMod 4758099209) ^ 70940 = (3 : ZMod 4758099209) ^ (35470 + 35470) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 35470 * (3 : ZMod 4758099209) ^ 35470 := by rw [pow_add]
          _ = 1068188528 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 4758099209) ^ 141880 = 1990448653 := by
        calc
          (3 : ZMod 4758099209) ^ 141880 = (3 : ZMod 4758099209) ^ (70940 + 70940) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 70940 * (3 : ZMod 4758099209) ^ 70940 := by rw [pow_add]
          _ = 1990448653 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 4758099209) ^ 283760 = 1280630060 := by
        calc
          (3 : ZMod 4758099209) ^ 283760 = (3 : ZMod 4758099209) ^ (141880 + 141880) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 141880 * (3 : ZMod 4758099209) ^ 141880 := by rw [pow_add]
          _ = 1280630060 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 4758099209) ^ 567521 = 1962718616 := by
        calc
          (3 : ZMod 4758099209) ^ 567521 = (3 : ZMod 4758099209) ^ (283760 + 283760 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 283760 * (3 : ZMod 4758099209) ^ 283760) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 1962718616 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 4758099209) ^ 1135042 = 3188483805 := by
        calc
          (3 : ZMod 4758099209) ^ 1135042 = (3 : ZMod 4758099209) ^ (567521 + 567521) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 567521 * (3 : ZMod 4758099209) ^ 567521 := by rw [pow_add]
          _ = 3188483805 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 4758099209) ^ 2270085 = 895687692 := by
        calc
          (3 : ZMod 4758099209) ^ 2270085 = (3 : ZMod 4758099209) ^ (1135042 + 1135042 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 1135042 * (3 : ZMod 4758099209) ^ 1135042) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 895687692 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 4758099209) ^ 4540171 = 203366019 := by
        calc
          (3 : ZMod 4758099209) ^ 4540171 = (3 : ZMod 4758099209) ^ (2270085 + 2270085 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 2270085 * (3 : ZMod 4758099209) ^ 2270085) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 203366019 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 4758099209) ^ 9080342 = 1534236522 := by
        calc
          (3 : ZMod 4758099209) ^ 9080342 = (3 : ZMod 4758099209) ^ (4540171 + 4540171) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 4540171 * (3 : ZMod 4758099209) ^ 4540171 := by rw [pow_add]
          _ = 1534236522 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 4758099209) ^ 18160684 = 91273058 := by
        calc
          (3 : ZMod 4758099209) ^ 18160684 = (3 : ZMod 4758099209) ^ (9080342 + 9080342) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 9080342 * (3 : ZMod 4758099209) ^ 9080342 := by rw [pow_add]
          _ = 91273058 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 4758099209) ^ 36321368 = 777502415 := by
        calc
          (3 : ZMod 4758099209) ^ 36321368 = (3 : ZMod 4758099209) ^ (18160684 + 18160684) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 18160684 * (3 : ZMod 4758099209) ^ 18160684 := by rw [pow_add]
          _ = 777502415 := by rw [factor_1_24]; decide
      change (3 : ZMod 4758099209) ^ 36321368 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (3 : ZMod 4758099209) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 4758099209) ^ 2 = 9 := by
        calc
          (3 : ZMod 4758099209) ^ 2 = (3 : ZMod 4758099209) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 1 * (3 : ZMod 4758099209) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 4758099209) ^ 4 = 81 := by
        calc
          (3 : ZMod 4758099209) ^ 4 = (3 : ZMod 4758099209) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 2 * (3 : ZMod 4758099209) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 4758099209) ^ 8 = 6561 := by
        calc
          (3 : ZMod 4758099209) ^ 8 = (3 : ZMod 4758099209) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 4 * (3 : ZMod 4758099209) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 4758099209) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 4758099209) ^ 16 = (3 : ZMod 4758099209) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 8 * (3 : ZMod 4758099209) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 4758099209) ^ 32 = 2242402836 := by
        calc
          (3 : ZMod 4758099209) ^ 32 = (3 : ZMod 4758099209) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 16 * (3 : ZMod 4758099209) ^ 16 := by rw [pow_add]
          _ = 2242402836 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 4758099209) ^ 65 = 2872231341 := by
        calc
          (3 : ZMod 4758099209) ^ 65 = (3 : ZMod 4758099209) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 32 * (3 : ZMod 4758099209) ^ 32) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 2872231341 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 4758099209) ^ 131 = 1549955248 := by
        calc
          (3 : ZMod 4758099209) ^ 131 = (3 : ZMod 4758099209) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = ((3 : ZMod 4758099209) ^ 65 * (3 : ZMod 4758099209) ^ 65) * (3 : ZMod 4758099209) := by rw [pow_succ, pow_add]
          _ = 1549955248 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 4758099209) ^ 262 = 1571639219 := by
        calc
          (3 : ZMod 4758099209) ^ 262 = (3 : ZMod 4758099209) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 131 * (3 : ZMod 4758099209) ^ 131 := by rw [pow_add]
          _ = 1571639219 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 4758099209) ^ 524 = 3137867573 := by
        calc
          (3 : ZMod 4758099209) ^ 524 = (3 : ZMod 4758099209) ^ (262 + 262) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 262 * (3 : ZMod 4758099209) ^ 262 := by rw [pow_add]
          _ = 3137867573 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 4758099209) ^ 1048 = 1682360890 := by
        calc
          (3 : ZMod 4758099209) ^ 1048 = (3 : ZMod 4758099209) ^ (524 + 524) :=
            congrArg (fun n : ℕ => (3 : ZMod 4758099209) ^ n) (by norm_num)
          _ = (3 : ZMod 4758099209) ^ 524 * (3 : ZMod 4758099209) ^ 524 := by rw [pow_add]
          _ = 1682360890 := by rw [factor_2_9]; decide
      change (3 : ZMod 4758099209) ^ 1048 ≠ 1
      rw [factor_2_10]
      decide

#print axioms prime_lucas_4758099209

end TotientTailPeriodKiller
end Erdos249257
