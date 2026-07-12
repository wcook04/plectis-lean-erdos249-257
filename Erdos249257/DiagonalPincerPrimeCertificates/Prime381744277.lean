import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_381744277 : Nat.Prime 381744277 := by
  apply lucas_primality 381744277 (2 : ZMod 381744277)
  ·
      have fermat_0 : (2 : ZMod 381744277) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 381744277) ^ 2 = 4 := by
        calc
          (2 : ZMod 381744277) ^ 2 = (2 : ZMod 381744277) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1 * (2 : ZMod 381744277) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 381744277) ^ 5 = 32 := by
        calc
          (2 : ZMod 381744277) ^ 5 = (2 : ZMod 381744277) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 2 * (2 : ZMod 381744277) ^ 2) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 381744277) ^ 11 = 2048 := by
        calc
          (2 : ZMod 381744277) ^ 11 = (2 : ZMod 381744277) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 5 * (2 : ZMod 381744277) ^ 5) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 381744277) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 381744277) ^ 22 = (2 : ZMod 381744277) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 11 * (2 : ZMod 381744277) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 381744277) ^ 45 = 147310573 := by
        calc
          (2 : ZMod 381744277) ^ 45 = (2 : ZMod 381744277) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 22 * (2 : ZMod 381744277) ^ 22) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 147310573 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 381744277) ^ 91 = 259834997 := by
        calc
          (2 : ZMod 381744277) ^ 91 = (2 : ZMod 381744277) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 45 * (2 : ZMod 381744277) ^ 45) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 259834997 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 381744277) ^ 182 = 192768501 := by
        calc
          (2 : ZMod 381744277) ^ 182 = (2 : ZMod 381744277) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 91 * (2 : ZMod 381744277) ^ 91 := by rw [pow_add]
          _ = 192768501 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 381744277) ^ 364 = 64205997 := by
        calc
          (2 : ZMod 381744277) ^ 364 = (2 : ZMod 381744277) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 182 * (2 : ZMod 381744277) ^ 182 := by rw [pow_add]
          _ = 64205997 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 381744277) ^ 728 = 176242803 := by
        calc
          (2 : ZMod 381744277) ^ 728 = (2 : ZMod 381744277) ^ (364 + 364) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 364 * (2 : ZMod 381744277) ^ 364 := by rw [pow_add]
          _ = 176242803 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 381744277) ^ 1456 = 67720981 := by
        calc
          (2 : ZMod 381744277) ^ 1456 = (2 : ZMod 381744277) ^ (728 + 728) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 728 * (2 : ZMod 381744277) ^ 728 := by rw [pow_add]
          _ = 67720981 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 381744277) ^ 2912 = 204805344 := by
        calc
          (2 : ZMod 381744277) ^ 2912 = (2 : ZMod 381744277) ^ (1456 + 1456) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1456 * (2 : ZMod 381744277) ^ 1456 := by rw [pow_add]
          _ = 204805344 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 381744277) ^ 5824 = 358466473 := by
        calc
          (2 : ZMod 381744277) ^ 5824 = (2 : ZMod 381744277) ^ (2912 + 2912) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 2912 * (2 : ZMod 381744277) ^ 2912 := by rw [pow_add]
          _ = 358466473 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 381744277) ^ 11649 = 249573321 := by
        calc
          (2 : ZMod 381744277) ^ 11649 = (2 : ZMod 381744277) ^ (5824 + 5824 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 5824 * (2 : ZMod 381744277) ^ 5824) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 249573321 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 381744277) ^ 23299 = 162911253 := by
        calc
          (2 : ZMod 381744277) ^ 23299 = (2 : ZMod 381744277) ^ (11649 + 11649 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 11649 * (2 : ZMod 381744277) ^ 11649) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 162911253 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 381744277) ^ 46599 = 158634021 := by
        calc
          (2 : ZMod 381744277) ^ 46599 = (2 : ZMod 381744277) ^ (23299 + 23299 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 23299 * (2 : ZMod 381744277) ^ 23299) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 158634021 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 381744277) ^ 93199 = 5170352 := by
        calc
          (2 : ZMod 381744277) ^ 93199 = (2 : ZMod 381744277) ^ (46599 + 46599 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 46599 * (2 : ZMod 381744277) ^ 46599) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 5170352 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 381744277) ^ 186398 = 133318425 := by
        calc
          (2 : ZMod 381744277) ^ 186398 = (2 : ZMod 381744277) ^ (93199 + 93199) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 93199 * (2 : ZMod 381744277) ^ 93199 := by rw [pow_add]
          _ = 133318425 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 381744277) ^ 372797 = 23891612 := by
        calc
          (2 : ZMod 381744277) ^ 372797 = (2 : ZMod 381744277) ^ (186398 + 186398 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 186398 * (2 : ZMod 381744277) ^ 186398) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 23891612 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 381744277) ^ 745594 = 267610139 := by
        calc
          (2 : ZMod 381744277) ^ 745594 = (2 : ZMod 381744277) ^ (372797 + 372797) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 372797 * (2 : ZMod 381744277) ^ 372797 := by rw [pow_add]
          _ = 267610139 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 381744277) ^ 1491188 = 213548406 := by
        calc
          (2 : ZMod 381744277) ^ 1491188 = (2 : ZMod 381744277) ^ (745594 + 745594) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 745594 * (2 : ZMod 381744277) ^ 745594 := by rw [pow_add]
          _ = 213548406 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 381744277) ^ 2982377 = 70955988 := by
        calc
          (2 : ZMod 381744277) ^ 2982377 = (2 : ZMod 381744277) ^ (1491188 + 1491188 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1491188 * (2 : ZMod 381744277) ^ 1491188) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 70955988 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 381744277) ^ 5964754 = 258604328 := by
        calc
          (2 : ZMod 381744277) ^ 5964754 = (2 : ZMod 381744277) ^ (2982377 + 2982377) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 2982377 * (2 : ZMod 381744277) ^ 2982377 := by rw [pow_add]
          _ = 258604328 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 381744277) ^ 11929508 = 139241195 := by
        calc
          (2 : ZMod 381744277) ^ 11929508 = (2 : ZMod 381744277) ^ (5964754 + 5964754) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 5964754 * (2 : ZMod 381744277) ^ 5964754 := by rw [pow_add]
          _ = 139241195 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 381744277) ^ 23859017 = 321209217 := by
        calc
          (2 : ZMod 381744277) ^ 23859017 = (2 : ZMod 381744277) ^ (11929508 + 11929508 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 11929508 * (2 : ZMod 381744277) ^ 11929508) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 321209217 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 381744277) ^ 47718034 = 381226420 := by
        calc
          (2 : ZMod 381744277) ^ 47718034 = (2 : ZMod 381744277) ^ (23859017 + 23859017) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 23859017 * (2 : ZMod 381744277) ^ 23859017 := by rw [pow_add]
          _ = 381226420 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 381744277) ^ 95436069 = 1035713 := by
        calc
          (2 : ZMod 381744277) ^ 95436069 = (2 : ZMod 381744277) ^ (47718034 + 47718034 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 47718034 * (2 : ZMod 381744277) ^ 47718034) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 1035713 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 381744277) ^ 190872138 = 381744276 := by
        calc
          (2 : ZMod 381744277) ^ 190872138 = (2 : ZMod 381744277) ^ (95436069 + 95436069) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 95436069 * (2 : ZMod 381744277) ^ 95436069 := by rw [pow_add]
          _ = 381744276 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 381744277) ^ 381744276 = 1 := by
        calc
          (2 : ZMod 381744277) ^ 381744276 = (2 : ZMod 381744277) ^ (190872138 + 190872138) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 190872138 * (2 : ZMod 381744277) ^ 190872138 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (41, 1), (97, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (41, 1), (97, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod = 381744277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 381744277) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 381744277) ^ 2 = 4 := by
        calc
          (2 : ZMod 381744277) ^ 2 = (2 : ZMod 381744277) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1 * (2 : ZMod 381744277) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 381744277) ^ 5 = 32 := by
        calc
          (2 : ZMod 381744277) ^ 5 = (2 : ZMod 381744277) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 2 * (2 : ZMod 381744277) ^ 2) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 381744277) ^ 11 = 2048 := by
        calc
          (2 : ZMod 381744277) ^ 11 = (2 : ZMod 381744277) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 5 * (2 : ZMod 381744277) ^ 5) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 381744277) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 381744277) ^ 22 = (2 : ZMod 381744277) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 11 * (2 : ZMod 381744277) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 381744277) ^ 45 = 147310573 := by
        calc
          (2 : ZMod 381744277) ^ 45 = (2 : ZMod 381744277) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 22 * (2 : ZMod 381744277) ^ 22) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 147310573 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 381744277) ^ 91 = 259834997 := by
        calc
          (2 : ZMod 381744277) ^ 91 = (2 : ZMod 381744277) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 45 * (2 : ZMod 381744277) ^ 45) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 259834997 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 381744277) ^ 182 = 192768501 := by
        calc
          (2 : ZMod 381744277) ^ 182 = (2 : ZMod 381744277) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 91 * (2 : ZMod 381744277) ^ 91 := by rw [pow_add]
          _ = 192768501 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 381744277) ^ 364 = 64205997 := by
        calc
          (2 : ZMod 381744277) ^ 364 = (2 : ZMod 381744277) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 182 * (2 : ZMod 381744277) ^ 182 := by rw [pow_add]
          _ = 64205997 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 381744277) ^ 728 = 176242803 := by
        calc
          (2 : ZMod 381744277) ^ 728 = (2 : ZMod 381744277) ^ (364 + 364) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 364 * (2 : ZMod 381744277) ^ 364 := by rw [pow_add]
          _ = 176242803 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 381744277) ^ 1456 = 67720981 := by
        calc
          (2 : ZMod 381744277) ^ 1456 = (2 : ZMod 381744277) ^ (728 + 728) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 728 * (2 : ZMod 381744277) ^ 728 := by rw [pow_add]
          _ = 67720981 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 381744277) ^ 2912 = 204805344 := by
        calc
          (2 : ZMod 381744277) ^ 2912 = (2 : ZMod 381744277) ^ (1456 + 1456) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1456 * (2 : ZMod 381744277) ^ 1456 := by rw [pow_add]
          _ = 204805344 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 381744277) ^ 5824 = 358466473 := by
        calc
          (2 : ZMod 381744277) ^ 5824 = (2 : ZMod 381744277) ^ (2912 + 2912) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 2912 * (2 : ZMod 381744277) ^ 2912 := by rw [pow_add]
          _ = 358466473 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 381744277) ^ 11649 = 249573321 := by
        calc
          (2 : ZMod 381744277) ^ 11649 = (2 : ZMod 381744277) ^ (5824 + 5824 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 5824 * (2 : ZMod 381744277) ^ 5824) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 249573321 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 381744277) ^ 23299 = 162911253 := by
        calc
          (2 : ZMod 381744277) ^ 23299 = (2 : ZMod 381744277) ^ (11649 + 11649 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 11649 * (2 : ZMod 381744277) ^ 11649) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 162911253 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 381744277) ^ 46599 = 158634021 := by
        calc
          (2 : ZMod 381744277) ^ 46599 = (2 : ZMod 381744277) ^ (23299 + 23299 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 23299 * (2 : ZMod 381744277) ^ 23299) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 158634021 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 381744277) ^ 93199 = 5170352 := by
        calc
          (2 : ZMod 381744277) ^ 93199 = (2 : ZMod 381744277) ^ (46599 + 46599 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 46599 * (2 : ZMod 381744277) ^ 46599) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 5170352 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 381744277) ^ 186398 = 133318425 := by
        calc
          (2 : ZMod 381744277) ^ 186398 = (2 : ZMod 381744277) ^ (93199 + 93199) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 93199 * (2 : ZMod 381744277) ^ 93199 := by rw [pow_add]
          _ = 133318425 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 381744277) ^ 372797 = 23891612 := by
        calc
          (2 : ZMod 381744277) ^ 372797 = (2 : ZMod 381744277) ^ (186398 + 186398 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 186398 * (2 : ZMod 381744277) ^ 186398) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 23891612 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 381744277) ^ 745594 = 267610139 := by
        calc
          (2 : ZMod 381744277) ^ 745594 = (2 : ZMod 381744277) ^ (372797 + 372797) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 372797 * (2 : ZMod 381744277) ^ 372797 := by rw [pow_add]
          _ = 267610139 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 381744277) ^ 1491188 = 213548406 := by
        calc
          (2 : ZMod 381744277) ^ 1491188 = (2 : ZMod 381744277) ^ (745594 + 745594) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 745594 * (2 : ZMod 381744277) ^ 745594 := by rw [pow_add]
          _ = 213548406 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 381744277) ^ 2982377 = 70955988 := by
        calc
          (2 : ZMod 381744277) ^ 2982377 = (2 : ZMod 381744277) ^ (1491188 + 1491188 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1491188 * (2 : ZMod 381744277) ^ 1491188) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 70955988 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 381744277) ^ 5964754 = 258604328 := by
        calc
          (2 : ZMod 381744277) ^ 5964754 = (2 : ZMod 381744277) ^ (2982377 + 2982377) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 2982377 * (2 : ZMod 381744277) ^ 2982377 := by rw [pow_add]
          _ = 258604328 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 381744277) ^ 11929508 = 139241195 := by
        calc
          (2 : ZMod 381744277) ^ 11929508 = (2 : ZMod 381744277) ^ (5964754 + 5964754) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 5964754 * (2 : ZMod 381744277) ^ 5964754 := by rw [pow_add]
          _ = 139241195 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 381744277) ^ 23859017 = 321209217 := by
        calc
          (2 : ZMod 381744277) ^ 23859017 = (2 : ZMod 381744277) ^ (11929508 + 11929508 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 11929508 * (2 : ZMod 381744277) ^ 11929508) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 321209217 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 381744277) ^ 47718034 = 381226420 := by
        calc
          (2 : ZMod 381744277) ^ 47718034 = (2 : ZMod 381744277) ^ (23859017 + 23859017) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 23859017 * (2 : ZMod 381744277) ^ 23859017 := by rw [pow_add]
          _ = 381226420 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 381744277) ^ 95436069 = 1035713 := by
        calc
          (2 : ZMod 381744277) ^ 95436069 = (2 : ZMod 381744277) ^ (47718034 + 47718034 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 47718034 * (2 : ZMod 381744277) ^ 47718034) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 1035713 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 381744277) ^ 190872138 = 381744276 := by
        calc
          (2 : ZMod 381744277) ^ 190872138 = (2 : ZMod 381744277) ^ (95436069 + 95436069) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 95436069 * (2 : ZMod 381744277) ^ 95436069 := by rw [pow_add]
          _ = 381744276 := by rw [factor_0_26]; decide
      change (2 : ZMod 381744277) ^ 190872138 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (2 : ZMod 381744277) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 381744277) ^ 3 = 8 := by
        calc
          (2 : ZMod 381744277) ^ 3 = (2 : ZMod 381744277) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1 * (2 : ZMod 381744277) ^ 1) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 381744277) ^ 7 = 128 := by
        calc
          (2 : ZMod 381744277) ^ 7 = (2 : ZMod 381744277) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 3 * (2 : ZMod 381744277) ^ 3) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 381744277) ^ 15 = 32768 := by
        calc
          (2 : ZMod 381744277) ^ 15 = (2 : ZMod 381744277) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 7 * (2 : ZMod 381744277) ^ 7) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 381744277) ^ 30 = 310253270 := by
        calc
          (2 : ZMod 381744277) ^ 30 = (2 : ZMod 381744277) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 15 * (2 : ZMod 381744277) ^ 15 := by rw [pow_add]
          _ = 310253270 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 381744277) ^ 60 = 298217676 := by
        calc
          (2 : ZMod 381744277) ^ 60 = (2 : ZMod 381744277) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 30 * (2 : ZMod 381744277) ^ 30 := by rw [pow_add]
          _ = 298217676 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 381744277) ^ 121 = 274609413 := by
        calc
          (2 : ZMod 381744277) ^ 121 = (2 : ZMod 381744277) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 60 * (2 : ZMod 381744277) ^ 60) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 274609413 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 381744277) ^ 242 = 248094609 := by
        calc
          (2 : ZMod 381744277) ^ 242 = (2 : ZMod 381744277) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 121 * (2 : ZMod 381744277) ^ 121 := by rw [pow_add]
          _ = 248094609 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 381744277) ^ 485 = 142672433 := by
        calc
          (2 : ZMod 381744277) ^ 485 = (2 : ZMod 381744277) ^ (242 + 242 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 242 * (2 : ZMod 381744277) ^ 242) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 142672433 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 381744277) ^ 970 = 210513878 := by
        calc
          (2 : ZMod 381744277) ^ 970 = (2 : ZMod 381744277) ^ (485 + 485) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 485 * (2 : ZMod 381744277) ^ 485 := by rw [pow_add]
          _ = 210513878 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 381744277) ^ 1941 = 13088933 := by
        calc
          (2 : ZMod 381744277) ^ 1941 = (2 : ZMod 381744277) ^ (970 + 970 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 970 * (2 : ZMod 381744277) ^ 970) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 13088933 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 381744277) ^ 3883 = 32171473 := by
        calc
          (2 : ZMod 381744277) ^ 3883 = (2 : ZMod 381744277) ^ (1941 + 1941 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1941 * (2 : ZMod 381744277) ^ 1941) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 32171473 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 381744277) ^ 7766 = 267462033 := by
        calc
          (2 : ZMod 381744277) ^ 7766 = (2 : ZMod 381744277) ^ (3883 + 3883) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 3883 * (2 : ZMod 381744277) ^ 3883 := by rw [pow_add]
          _ = 267462033 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 381744277) ^ 15533 = 126530593 := by
        calc
          (2 : ZMod 381744277) ^ 15533 = (2 : ZMod 381744277) ^ (7766 + 7766 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 7766 * (2 : ZMod 381744277) ^ 7766) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 126530593 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 381744277) ^ 31066 = 171591907 := by
        calc
          (2 : ZMod 381744277) ^ 31066 = (2 : ZMod 381744277) ^ (15533 + 15533) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 15533 * (2 : ZMod 381744277) ^ 15533 := by rw [pow_add]
          _ = 171591907 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 381744277) ^ 62132 = 305830280 := by
        calc
          (2 : ZMod 381744277) ^ 62132 = (2 : ZMod 381744277) ^ (31066 + 31066) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 31066 * (2 : ZMod 381744277) ^ 31066 := by rw [pow_add]
          _ = 305830280 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 381744277) ^ 124265 = 63045076 := by
        calc
          (2 : ZMod 381744277) ^ 124265 = (2 : ZMod 381744277) ^ (62132 + 62132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 62132 * (2 : ZMod 381744277) ^ 62132) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 63045076 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 381744277) ^ 248531 = 175997445 := by
        calc
          (2 : ZMod 381744277) ^ 248531 = (2 : ZMod 381744277) ^ (124265 + 124265 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 124265 * (2 : ZMod 381744277) ^ 124265) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 175997445 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 381744277) ^ 497062 = 100543612 := by
        calc
          (2 : ZMod 381744277) ^ 497062 = (2 : ZMod 381744277) ^ (248531 + 248531) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 248531 * (2 : ZMod 381744277) ^ 248531 := by rw [pow_add]
          _ = 100543612 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 381744277) ^ 994125 = 375214115 := by
        calc
          (2 : ZMod 381744277) ^ 994125 = (2 : ZMod 381744277) ^ (497062 + 497062 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 497062 * (2 : ZMod 381744277) ^ 497062) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 375214115 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 381744277) ^ 1988251 = 160823641 := by
        calc
          (2 : ZMod 381744277) ^ 1988251 = (2 : ZMod 381744277) ^ (994125 + 994125 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 994125 * (2 : ZMod 381744277) ^ 994125) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 160823641 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 381744277) ^ 3976502 = 235515558 := by
        calc
          (2 : ZMod 381744277) ^ 3976502 = (2 : ZMod 381744277) ^ (1988251 + 1988251) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1988251 * (2 : ZMod 381744277) ^ 1988251 := by rw [pow_add]
          _ = 235515558 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 381744277) ^ 7953005 = 94187443 := by
        calc
          (2 : ZMod 381744277) ^ 7953005 = (2 : ZMod 381744277) ^ (3976502 + 3976502 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 3976502 * (2 : ZMod 381744277) ^ 3976502) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 94187443 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 381744277) ^ 15906011 = 190923946 := by
        calc
          (2 : ZMod 381744277) ^ 15906011 = (2 : ZMod 381744277) ^ (7953005 + 7953005 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 7953005 * (2 : ZMod 381744277) ^ 7953005) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 190923946 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 381744277) ^ 31812023 = 214486373 := by
        calc
          (2 : ZMod 381744277) ^ 31812023 = (2 : ZMod 381744277) ^ (15906011 + 15906011 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 15906011 * (2 : ZMod 381744277) ^ 15906011) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 214486373 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 381744277) ^ 63624046 = 168190002 := by
        calc
          (2 : ZMod 381744277) ^ 63624046 = (2 : ZMod 381744277) ^ (31812023 + 31812023) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 31812023 * (2 : ZMod 381744277) ^ 31812023 := by rw [pow_add]
          _ = 168190002 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 381744277) ^ 127248092 = 168190001 := by
        calc
          (2 : ZMod 381744277) ^ 127248092 = (2 : ZMod 381744277) ^ (63624046 + 63624046) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 63624046 * (2 : ZMod 381744277) ^ 63624046 := by rw [pow_add]
          _ = 168190001 := by rw [factor_1_25]; decide
      change (2 : ZMod 381744277) ^ 127248092 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (2 : ZMod 381744277) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 381744277) ^ 2 = 4 := by
        calc
          (2 : ZMod 381744277) ^ 2 = (2 : ZMod 381744277) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1 * (2 : ZMod 381744277) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 381744277) ^ 4 = 16 := by
        calc
          (2 : ZMod 381744277) ^ 4 = (2 : ZMod 381744277) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 2 * (2 : ZMod 381744277) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 381744277) ^ 9 = 512 := by
        calc
          (2 : ZMod 381744277) ^ 9 = (2 : ZMod 381744277) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 4 * (2 : ZMod 381744277) ^ 4) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 381744277) ^ 19 = 524288 := by
        calc
          (2 : ZMod 381744277) ^ 19 = (2 : ZMod 381744277) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 9 * (2 : ZMod 381744277) ^ 9) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 381744277) ^ 38 = 22027504 := by
        calc
          (2 : ZMod 381744277) ^ 38 = (2 : ZMod 381744277) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 19 * (2 : ZMod 381744277) ^ 19 := by rw [pow_add]
          _ = 22027504 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 381744277) ^ 76 = 213609044 := by
        calc
          (2 : ZMod 381744277) ^ 76 = (2 : ZMod 381744277) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 38 * (2 : ZMod 381744277) ^ 38 := by rw [pow_add]
          _ = 213609044 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 381744277) ^ 153 = 174240457 := by
        calc
          (2 : ZMod 381744277) ^ 153 = (2 : ZMod 381744277) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 76 * (2 : ZMod 381744277) ^ 76) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 174240457 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 381744277) ^ 306 = 67478619 := by
        calc
          (2 : ZMod 381744277) ^ 306 = (2 : ZMod 381744277) ^ (153 + 153) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 153 * (2 : ZMod 381744277) ^ 153 := by rw [pow_add]
          _ = 67478619 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 381744277) ^ 613 = 340477155 := by
        calc
          (2 : ZMod 381744277) ^ 613 = (2 : ZMod 381744277) ^ (306 + 306 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 306 * (2 : ZMod 381744277) ^ 306) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 340477155 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 381744277) ^ 1226 = 13927635 := by
        calc
          (2 : ZMod 381744277) ^ 1226 = (2 : ZMod 381744277) ^ (613 + 613) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 613 * (2 : ZMod 381744277) ^ 613 := by rw [pow_add]
          _ = 13927635 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 381744277) ^ 2452 = 243266999 := by
        calc
          (2 : ZMod 381744277) ^ 2452 = (2 : ZMod 381744277) ^ (1226 + 1226) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1226 * (2 : ZMod 381744277) ^ 1226 := by rw [pow_add]
          _ = 243266999 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 381744277) ^ 4905 = 214384404 := by
        calc
          (2 : ZMod 381744277) ^ 4905 = (2 : ZMod 381744277) ^ (2452 + 2452 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 2452 * (2 : ZMod 381744277) ^ 2452) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 214384404 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 381744277) ^ 9810 = 123070378 := by
        calc
          (2 : ZMod 381744277) ^ 9810 = (2 : ZMod 381744277) ^ (4905 + 4905) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 4905 * (2 : ZMod 381744277) ^ 4905 := by rw [pow_add]
          _ = 123070378 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 381744277) ^ 19620 = 288034745 := by
        calc
          (2 : ZMod 381744277) ^ 19620 = (2 : ZMod 381744277) ^ (9810 + 9810) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 9810 * (2 : ZMod 381744277) ^ 9810 := by rw [pow_add]
          _ = 288034745 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 381744277) ^ 39241 = 304531470 := by
        calc
          (2 : ZMod 381744277) ^ 39241 = (2 : ZMod 381744277) ^ (19620 + 19620 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 19620 * (2 : ZMod 381744277) ^ 19620) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 304531470 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 381744277) ^ 78483 = 372578697 := by
        calc
          (2 : ZMod 381744277) ^ 78483 = (2 : ZMod 381744277) ^ (39241 + 39241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 39241 * (2 : ZMod 381744277) ^ 39241) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 372578697 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 381744277) ^ 156967 = 131813898 := by
        calc
          (2 : ZMod 381744277) ^ 156967 = (2 : ZMod 381744277) ^ (78483 + 78483 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 78483 * (2 : ZMod 381744277) ^ 78483) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 131813898 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 381744277) ^ 313934 = 374739411 := by
        calc
          (2 : ZMod 381744277) ^ 313934 = (2 : ZMod 381744277) ^ (156967 + 156967) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 156967 * (2 : ZMod 381744277) ^ 156967 := by rw [pow_add]
          _ = 374739411 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 381744277) ^ 627868 = 265289484 := by
        calc
          (2 : ZMod 381744277) ^ 627868 = (2 : ZMod 381744277) ^ (313934 + 313934) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 313934 * (2 : ZMod 381744277) ^ 313934 := by rw [pow_add]
          _ = 265289484 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 381744277) ^ 1255737 = 169840119 := by
        calc
          (2 : ZMod 381744277) ^ 1255737 = (2 : ZMod 381744277) ^ (627868 + 627868 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 627868 * (2 : ZMod 381744277) ^ 627868) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 169840119 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 381744277) ^ 2511475 = 280909953 := by
        calc
          (2 : ZMod 381744277) ^ 2511475 = (2 : ZMod 381744277) ^ (1255737 + 1255737 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1255737 * (2 : ZMod 381744277) ^ 1255737) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 280909953 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 381744277) ^ 5022951 = 26099201 := by
        calc
          (2 : ZMod 381744277) ^ 5022951 = (2 : ZMod 381744277) ^ (2511475 + 2511475 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 2511475 * (2 : ZMod 381744277) ^ 2511475) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 26099201 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 381744277) ^ 10045902 = 219963512 := by
        calc
          (2 : ZMod 381744277) ^ 10045902 = (2 : ZMod 381744277) ^ (5022951 + 5022951) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 5022951 * (2 : ZMod 381744277) ^ 5022951 := by rw [pow_add]
          _ = 219963512 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 381744277) ^ 20091804 = 323529560 := by
        calc
          (2 : ZMod 381744277) ^ 20091804 = (2 : ZMod 381744277) ^ (10045902 + 10045902) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 10045902 * (2 : ZMod 381744277) ^ 10045902 := by rw [pow_add]
          _ = 323529560 := by rw [factor_2_23]; decide
      change (2 : ZMod 381744277) ^ 20091804 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (2 : ZMod 381744277) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 381744277) ^ 2 = 4 := by
        calc
          (2 : ZMod 381744277) ^ 2 = (2 : ZMod 381744277) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1 * (2 : ZMod 381744277) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 381744277) ^ 4 = 16 := by
        calc
          (2 : ZMod 381744277) ^ 4 = (2 : ZMod 381744277) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 2 * (2 : ZMod 381744277) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 381744277) ^ 8 = 256 := by
        calc
          (2 : ZMod 381744277) ^ 8 = (2 : ZMod 381744277) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 4 * (2 : ZMod 381744277) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 381744277) ^ 17 = 131072 := by
        calc
          (2 : ZMod 381744277) ^ 17 = (2 : ZMod 381744277) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 8 * (2 : ZMod 381744277) ^ 8) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 381744277) ^ 35 = 2753438 := by
        calc
          (2 : ZMod 381744277) ^ 35 = (2 : ZMod 381744277) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 17 * (2 : ZMod 381744277) ^ 17) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 2753438 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 381744277) ^ 71 = 340701525 := by
        calc
          (2 : ZMod 381744277) ^ 71 = (2 : ZMod 381744277) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 35 * (2 : ZMod 381744277) ^ 35) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 340701525 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 381744277) ^ 142 = 172130961 := by
        calc
          (2 : ZMod 381744277) ^ 142 = (2 : ZMod 381744277) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 71 * (2 : ZMod 381744277) ^ 71 := by rw [pow_add]
          _ = 172130961 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 381744277) ^ 284 = 181711047 := by
        calc
          (2 : ZMod 381744277) ^ 284 = (2 : ZMod 381744277) ^ (142 + 142) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 142 * (2 : ZMod 381744277) ^ 142 := by rw [pow_add]
          _ = 181711047 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 381744277) ^ 568 = 167969684 := by
        calc
          (2 : ZMod 381744277) ^ 568 = (2 : ZMod 381744277) ^ (284 + 284) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 284 * (2 : ZMod 381744277) ^ 284 := by rw [pow_add]
          _ = 167969684 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 381744277) ^ 1136 = 345670623 := by
        calc
          (2 : ZMod 381744277) ^ 1136 = (2 : ZMod 381744277) ^ (568 + 568) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 568 * (2 : ZMod 381744277) ^ 568 := by rw [pow_add]
          _ = 345670623 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 381744277) ^ 2273 = 213753363 := by
        calc
          (2 : ZMod 381744277) ^ 2273 = (2 : ZMod 381744277) ^ (1136 + 1136 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1136 * (2 : ZMod 381744277) ^ 1136) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 213753363 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 381744277) ^ 4546 = 279094695 := by
        calc
          (2 : ZMod 381744277) ^ 4546 = (2 : ZMod 381744277) ^ (2273 + 2273) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 2273 * (2 : ZMod 381744277) ^ 2273 := by rw [pow_add]
          _ = 279094695 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 381744277) ^ 9092 = 229734287 := by
        calc
          (2 : ZMod 381744277) ^ 9092 = (2 : ZMod 381744277) ^ (4546 + 4546) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 4546 * (2 : ZMod 381744277) ^ 4546 := by rw [pow_add]
          _ = 229734287 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 381744277) ^ 18185 = 94907039 := by
        calc
          (2 : ZMod 381744277) ^ 18185 = (2 : ZMod 381744277) ^ (9092 + 9092 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 9092 * (2 : ZMod 381744277) ^ 9092) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 94907039 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 381744277) ^ 36370 = 126027426 := by
        calc
          (2 : ZMod 381744277) ^ 36370 = (2 : ZMod 381744277) ^ (18185 + 18185) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 18185 * (2 : ZMod 381744277) ^ 18185 := by rw [pow_add]
          _ = 126027426 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 381744277) ^ 72740 = 163216264 := by
        calc
          (2 : ZMod 381744277) ^ 72740 = (2 : ZMod 381744277) ^ (36370 + 36370) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 36370 * (2 : ZMod 381744277) ^ 36370 := by rw [pow_add]
          _ = 163216264 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 381744277) ^ 145481 = 234083676 := by
        calc
          (2 : ZMod 381744277) ^ 145481 = (2 : ZMod 381744277) ^ (72740 + 72740 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 72740 * (2 : ZMod 381744277) ^ 72740) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 234083676 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 381744277) ^ 290963 = 50007408 := by
        calc
          (2 : ZMod 381744277) ^ 290963 = (2 : ZMod 381744277) ^ (145481 + 145481 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 145481 * (2 : ZMod 381744277) ^ 145481) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 50007408 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 381744277) ^ 581927 = 276022770 := by
        calc
          (2 : ZMod 381744277) ^ 581927 = (2 : ZMod 381744277) ^ (290963 + 290963 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 290963 * (2 : ZMod 381744277) ^ 290963) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 276022770 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 381744277) ^ 1163854 = 182011106 := by
        calc
          (2 : ZMod 381744277) ^ 1163854 = (2 : ZMod 381744277) ^ (581927 + 581927) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 581927 * (2 : ZMod 381744277) ^ 581927 := by rw [pow_add]
          _ = 182011106 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 381744277) ^ 2327709 = 132040423 := by
        calc
          (2 : ZMod 381744277) ^ 2327709 = (2 : ZMod 381744277) ^ (1163854 + 1163854 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1163854 * (2 : ZMod 381744277) ^ 1163854) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 132040423 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 381744277) ^ 4655418 = 273354046 := by
        calc
          (2 : ZMod 381744277) ^ 4655418 = (2 : ZMod 381744277) ^ (2327709 + 2327709) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 2327709 * (2 : ZMod 381744277) ^ 2327709 := by rw [pow_add]
          _ = 273354046 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 381744277) ^ 9310836 = 174984339 := by
        calc
          (2 : ZMod 381744277) ^ 9310836 = (2 : ZMod 381744277) ^ (4655418 + 4655418) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 4655418 * (2 : ZMod 381744277) ^ 4655418 := by rw [pow_add]
          _ = 174984339 := by rw [factor_3_22]; decide
      change (2 : ZMod 381744277) ^ 9310836 ≠ 1
      rw [factor_3_23]
      decide
    ·
      have factor_4_0 : (2 : ZMod 381744277) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 381744277) ^ 3 = 8 := by
        calc
          (2 : ZMod 381744277) ^ 3 = (2 : ZMod 381744277) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1 * (2 : ZMod 381744277) ^ 1) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 381744277) ^ 7 = 128 := by
        calc
          (2 : ZMod 381744277) ^ 7 = (2 : ZMod 381744277) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 3 * (2 : ZMod 381744277) ^ 3) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 381744277) ^ 15 = 32768 := by
        calc
          (2 : ZMod 381744277) ^ 15 = (2 : ZMod 381744277) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 7 * (2 : ZMod 381744277) ^ 7) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 381744277) ^ 30 = 310253270 := by
        calc
          (2 : ZMod 381744277) ^ 30 = (2 : ZMod 381744277) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 15 * (2 : ZMod 381744277) ^ 15 := by rw [pow_add]
          _ = 310253270 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 381744277) ^ 60 = 298217676 := by
        calc
          (2 : ZMod 381744277) ^ 60 = (2 : ZMod 381744277) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 30 * (2 : ZMod 381744277) ^ 30 := by rw [pow_add]
          _ = 298217676 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 381744277) ^ 120 = 328176845 := by
        calc
          (2 : ZMod 381744277) ^ 120 = (2 : ZMod 381744277) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 60 * (2 : ZMod 381744277) ^ 60 := by rw [pow_add]
          _ = 328176845 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 381744277) ^ 240 = 348331860 := by
        calc
          (2 : ZMod 381744277) ^ 240 = (2 : ZMod 381744277) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 120 * (2 : ZMod 381744277) ^ 120 := by rw [pow_add]
          _ = 348331860 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 381744277) ^ 480 = 231119178 := by
        calc
          (2 : ZMod 381744277) ^ 480 = (2 : ZMod 381744277) ^ (240 + 240) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 240 * (2 : ZMod 381744277) ^ 240 := by rw [pow_add]
          _ = 231119178 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 381744277) ^ 960 = 287259382 := by
        calc
          (2 : ZMod 381744277) ^ 960 = (2 : ZMod 381744277) ^ (480 + 480) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 480 * (2 : ZMod 381744277) ^ 480 := by rw [pow_add]
          _ = 287259382 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 381744277) ^ 1921 = 140188850 := by
        calc
          (2 : ZMod 381744277) ^ 1921 = (2 : ZMod 381744277) ^ (960 + 960 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 960 * (2 : ZMod 381744277) ^ 960) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 140188850 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 381744277) ^ 3843 = 65010649 := by
        calc
          (2 : ZMod 381744277) ^ 3843 = (2 : ZMod 381744277) ^ (1921 + 1921 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1921 * (2 : ZMod 381744277) ^ 1921) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 65010649 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 381744277) ^ 7686 = 65386336 := by
        calc
          (2 : ZMod 381744277) ^ 7686 = (2 : ZMod 381744277) ^ (3843 + 3843) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 3843 * (2 : ZMod 381744277) ^ 3843 := by rw [pow_add]
          _ = 65386336 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 381744277) ^ 15373 = 75822350 := by
        calc
          (2 : ZMod 381744277) ^ 15373 = (2 : ZMod 381744277) ^ (7686 + 7686 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 7686 * (2 : ZMod 381744277) ^ 7686) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 75822350 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 381744277) ^ 30746 = 31051585 := by
        calc
          (2 : ZMod 381744277) ^ 30746 = (2 : ZMod 381744277) ^ (15373 + 15373) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 15373 * (2 : ZMod 381744277) ^ 15373 := by rw [pow_add]
          _ = 31051585 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 381744277) ^ 61492 = 16283996 := by
        calc
          (2 : ZMod 381744277) ^ 61492 = (2 : ZMod 381744277) ^ (30746 + 30746) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 30746 * (2 : ZMod 381744277) ^ 30746 := by rw [pow_add]
          _ = 16283996 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 381744277) ^ 122984 = 170805445 := by
        calc
          (2 : ZMod 381744277) ^ 122984 = (2 : ZMod 381744277) ^ (61492 + 61492) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 61492 * (2 : ZMod 381744277) ^ 61492 := by rw [pow_add]
          _ = 170805445 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 381744277) ^ 245969 = 43410635 := by
        calc
          (2 : ZMod 381744277) ^ 245969 = (2 : ZMod 381744277) ^ (122984 + 122984 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 122984 * (2 : ZMod 381744277) ^ 122984) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 43410635 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 381744277) ^ 491938 = 317227063 := by
        calc
          (2 : ZMod 381744277) ^ 491938 = (2 : ZMod 381744277) ^ (245969 + 245969) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 245969 * (2 : ZMod 381744277) ^ 245969 := by rw [pow_add]
          _ = 317227063 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 381744277) ^ 983877 = 39767312 := by
        calc
          (2 : ZMod 381744277) ^ 983877 = (2 : ZMod 381744277) ^ (491938 + 491938 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 491938 * (2 : ZMod 381744277) ^ 491938) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 39767312 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 381744277) ^ 1967754 = 66682862 := by
        calc
          (2 : ZMod 381744277) ^ 1967754 = (2 : ZMod 381744277) ^ (983877 + 983877) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 983877 * (2 : ZMod 381744277) ^ 983877 := by rw [pow_add]
          _ = 66682862 := by rw [factor_4_19]; decide
      have factor_4_21 : (2 : ZMod 381744277) ^ 3935508 = 173213250 := by
        calc
          (2 : ZMod 381744277) ^ 3935508 = (2 : ZMod 381744277) ^ (1967754 + 1967754) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1967754 * (2 : ZMod 381744277) ^ 1967754 := by rw [pow_add]
          _ = 173213250 := by rw [factor_4_20]; decide
      change (2 : ZMod 381744277) ^ 3935508 ≠ 1
      rw [factor_4_21]
      decide
    ·
      have factor_5_0 : (2 : ZMod 381744277) ^ 1 = 2 := by norm_num
      have factor_5_1 : (2 : ZMod 381744277) ^ 3 = 8 := by
        calc
          (2 : ZMod 381744277) ^ 3 = (2 : ZMod 381744277) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 1 * (2 : ZMod 381744277) ^ 1) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_5_0]; decide
      have factor_5_2 : (2 : ZMod 381744277) ^ 6 = 64 := by
        calc
          (2 : ZMod 381744277) ^ 6 = (2 : ZMod 381744277) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 3 * (2 : ZMod 381744277) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_5_1]; decide
      have factor_5_3 : (2 : ZMod 381744277) ^ 13 = 8192 := by
        calc
          (2 : ZMod 381744277) ^ 13 = (2 : ZMod 381744277) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 6 * (2 : ZMod 381744277) ^ 6) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_5_2]; decide
      have factor_5_4 : (2 : ZMod 381744277) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 381744277) ^ 27 = (2 : ZMod 381744277) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 13 * (2 : ZMod 381744277) ^ 13) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_5_3]; decide
      have factor_5_5 : (2 : ZMod 381744277) ^ 55 = 57037337 := by
        calc
          (2 : ZMod 381744277) ^ 55 = (2 : ZMod 381744277) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 27 * (2 : ZMod 381744277) ^ 27) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 57037337 := by rw [factor_5_4]; decide
      have factor_5_6 : (2 : ZMod 381744277) ^ 110 = 253449747 := by
        calc
          (2 : ZMod 381744277) ^ 110 = (2 : ZMod 381744277) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 55 * (2 : ZMod 381744277) ^ 55 := by rw [pow_add]
          _ = 253449747 := by rw [factor_5_5]; decide
      have factor_5_7 : (2 : ZMod 381744277) ^ 221 = 293575504 := by
        calc
          (2 : ZMod 381744277) ^ 221 = (2 : ZMod 381744277) ^ (110 + 110 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 110 * (2 : ZMod 381744277) ^ 110) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 293575504 := by rw [factor_5_6]; decide
      have factor_5_8 : (2 : ZMod 381744277) ^ 442 = 109127920 := by
        calc
          (2 : ZMod 381744277) ^ 442 = (2 : ZMod 381744277) ^ (221 + 221) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 221 * (2 : ZMod 381744277) ^ 221 := by rw [pow_add]
          _ = 109127920 := by rw [factor_5_7]; decide
      have factor_5_9 : (2 : ZMod 381744277) ^ 885 = 119720612 := by
        calc
          (2 : ZMod 381744277) ^ 885 = (2 : ZMod 381744277) ^ (442 + 442 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 442 * (2 : ZMod 381744277) ^ 442) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 119720612 := by rw [factor_5_8]; decide
      have factor_5_10 : (2 : ZMod 381744277) ^ 1771 = 211450420 := by
        calc
          (2 : ZMod 381744277) ^ 1771 = (2 : ZMod 381744277) ^ (885 + 885 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 885 * (2 : ZMod 381744277) ^ 885) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 211450420 := by rw [factor_5_9]; decide
      have factor_5_11 : (2 : ZMod 381744277) ^ 3542 = 83279566 := by
        calc
          (2 : ZMod 381744277) ^ 3542 = (2 : ZMod 381744277) ^ (1771 + 1771) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 1771 * (2 : ZMod 381744277) ^ 1771 := by rw [pow_add]
          _ = 83279566 := by rw [factor_5_10]; decide
      have factor_5_12 : (2 : ZMod 381744277) ^ 7084 = 370948488 := by
        calc
          (2 : ZMod 381744277) ^ 7084 = (2 : ZMod 381744277) ^ (3542 + 3542) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 3542 * (2 : ZMod 381744277) ^ 3542 := by rw [pow_add]
          _ = 370948488 := by rw [factor_5_11]; decide
      have factor_5_13 : (2 : ZMod 381744277) ^ 14168 = 241898759 := by
        calc
          (2 : ZMod 381744277) ^ 14168 = (2 : ZMod 381744277) ^ (7084 + 7084) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 7084 * (2 : ZMod 381744277) ^ 7084 := by rw [pow_add]
          _ = 241898759 := by rw [factor_5_12]; decide
      have factor_5_14 : (2 : ZMod 381744277) ^ 28336 = 50371399 := by
        calc
          (2 : ZMod 381744277) ^ 28336 = (2 : ZMod 381744277) ^ (14168 + 14168) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 14168 * (2 : ZMod 381744277) ^ 14168 := by rw [pow_add]
          _ = 50371399 := by rw [factor_5_13]; decide
      have factor_5_15 : (2 : ZMod 381744277) ^ 56672 = 375598452 := by
        calc
          (2 : ZMod 381744277) ^ 56672 = (2 : ZMod 381744277) ^ (28336 + 28336) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 28336 * (2 : ZMod 381744277) ^ 28336 := by rw [pow_add]
          _ = 375598452 := by rw [factor_5_14]; decide
      have factor_5_16 : (2 : ZMod 381744277) ^ 113344 = 240931414 := by
        calc
          (2 : ZMod 381744277) ^ 113344 = (2 : ZMod 381744277) ^ (56672 + 56672) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 56672 * (2 : ZMod 381744277) ^ 56672 := by rw [pow_add]
          _ = 240931414 := by rw [factor_5_15]; decide
      have factor_5_17 : (2 : ZMod 381744277) ^ 226689 = 112183320 := by
        calc
          (2 : ZMod 381744277) ^ 226689 = (2 : ZMod 381744277) ^ (113344 + 113344 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = ((2 : ZMod 381744277) ^ 113344 * (2 : ZMod 381744277) ^ 113344) * (2 : ZMod 381744277) := by rw [pow_succ, pow_add]
          _ = 112183320 := by rw [factor_5_16]; decide
      have factor_5_18 : (2 : ZMod 381744277) ^ 453378 = 95866450 := by
        calc
          (2 : ZMod 381744277) ^ 453378 = (2 : ZMod 381744277) ^ (226689 + 226689) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 226689 * (2 : ZMod 381744277) ^ 226689 := by rw [pow_add]
          _ = 95866450 := by rw [factor_5_17]; decide
      have factor_5_19 : (2 : ZMod 381744277) ^ 906756 = 344064816 := by
        calc
          (2 : ZMod 381744277) ^ 906756 = (2 : ZMod 381744277) ^ (453378 + 453378) :=
            congrArg (fun n : ℕ => (2 : ZMod 381744277) ^ n) (by norm_num)
          _ = (2 : ZMod 381744277) ^ 453378 * (2 : ZMod 381744277) ^ 453378 := by rw [pow_add]
          _ = 344064816 := by rw [factor_5_18]; decide
      change (2 : ZMod 381744277) ^ 906756 ≠ 1
      rw [factor_5_19]
      decide

#print axioms prime_lucas_381744277

end TotientTailPeriodKiller
end Erdos249257
