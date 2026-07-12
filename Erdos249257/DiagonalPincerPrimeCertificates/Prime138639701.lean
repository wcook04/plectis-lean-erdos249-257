import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_138639701 : Nat.Prime 138639701 := by
  apply lucas_primality 138639701 (2 : ZMod 138639701)
  ·
      have fermat_0 : (2 : ZMod 138639701) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 138639701) ^ 2 = 4 := by
        calc
          (2 : ZMod 138639701) ^ 2 = (2 : ZMod 138639701) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 1 * (2 : ZMod 138639701) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 138639701) ^ 4 = 16 := by
        calc
          (2 : ZMod 138639701) ^ 4 = (2 : ZMod 138639701) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 2 * (2 : ZMod 138639701) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 138639701) ^ 8 = 256 := by
        calc
          (2 : ZMod 138639701) ^ 8 = (2 : ZMod 138639701) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 4 * (2 : ZMod 138639701) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 138639701) ^ 16 = 65536 := by
        calc
          (2 : ZMod 138639701) ^ 16 = (2 : ZMod 138639701) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 8 * (2 : ZMod 138639701) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 138639701) ^ 33 = 132912831 := by
        calc
          (2 : ZMod 138639701) ^ 33 = (2 : ZMod 138639701) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 16 * (2 : ZMod 138639701) ^ 16) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 132912831 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 138639701) ^ 66 = 16409237 := by
        calc
          (2 : ZMod 138639701) ^ 66 = (2 : ZMod 138639701) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 33 * (2 : ZMod 138639701) ^ 33 := by rw [pow_add]
          _ = 16409237 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 138639701) ^ 132 = 81713391 := by
        calc
          (2 : ZMod 138639701) ^ 132 = (2 : ZMod 138639701) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 66 * (2 : ZMod 138639701) ^ 66 := by rw [pow_add]
          _ = 81713391 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 138639701) ^ 264 = 54889109 := by
        calc
          (2 : ZMod 138639701) ^ 264 = (2 : ZMod 138639701) ^ (132 + 132) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 132 * (2 : ZMod 138639701) ^ 132 := by rw [pow_add]
          _ = 54889109 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 138639701) ^ 528 = 7178229 := by
        calc
          (2 : ZMod 138639701) ^ 528 = (2 : ZMod 138639701) ^ (264 + 264) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 264 * (2 : ZMod 138639701) ^ 264 := by rw [pow_add]
          _ = 7178229 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 138639701) ^ 1057 = 3326160 := by
        calc
          (2 : ZMod 138639701) ^ 1057 = (2 : ZMod 138639701) ^ (528 + 528 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 528 * (2 : ZMod 138639701) ^ 528) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 3326160 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 138639701) ^ 2115 = 61691002 := by
        calc
          (2 : ZMod 138639701) ^ 2115 = (2 : ZMod 138639701) ^ (1057 + 1057 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 1057 * (2 : ZMod 138639701) ^ 1057) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 61691002 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 138639701) ^ 4230 = 11972639 := by
        calc
          (2 : ZMod 138639701) ^ 4230 = (2 : ZMod 138639701) ^ (2115 + 2115) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 2115 * (2 : ZMod 138639701) ^ 2115 := by rw [pow_add]
          _ = 11972639 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 138639701) ^ 8461 = 122579978 := by
        calc
          (2 : ZMod 138639701) ^ 8461 = (2 : ZMod 138639701) ^ (4230 + 4230 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 4230 * (2 : ZMod 138639701) ^ 4230) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 122579978 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 138639701) ^ 16923 = 18066911 := by
        calc
          (2 : ZMod 138639701) ^ 16923 = (2 : ZMod 138639701) ^ (8461 + 8461 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 8461 * (2 : ZMod 138639701) ^ 8461) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 18066911 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 138639701) ^ 33847 = 60734743 := by
        calc
          (2 : ZMod 138639701) ^ 33847 = (2 : ZMod 138639701) ^ (16923 + 16923 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 16923 * (2 : ZMod 138639701) ^ 16923) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 60734743 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 138639701) ^ 67695 = 103363517 := by
        calc
          (2 : ZMod 138639701) ^ 67695 = (2 : ZMod 138639701) ^ (33847 + 33847 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 33847 * (2 : ZMod 138639701) ^ 33847) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 103363517 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 138639701) ^ 135390 = 136020707 := by
        calc
          (2 : ZMod 138639701) ^ 135390 = (2 : ZMod 138639701) ^ (67695 + 67695) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 67695 * (2 : ZMod 138639701) ^ 67695 := by rw [pow_add]
          _ = 136020707 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 138639701) ^ 270780 = 69004762 := by
        calc
          (2 : ZMod 138639701) ^ 270780 = (2 : ZMod 138639701) ^ (135390 + 135390) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 135390 * (2 : ZMod 138639701) ^ 135390 := by rw [pow_add]
          _ = 69004762 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 138639701) ^ 541561 = 98793683 := by
        calc
          (2 : ZMod 138639701) ^ 541561 = (2 : ZMod 138639701) ^ (270780 + 270780 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 270780 * (2 : ZMod 138639701) ^ 270780) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 98793683 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 138639701) ^ 1083122 = 105891201 := by
        calc
          (2 : ZMod 138639701) ^ 1083122 = (2 : ZMod 138639701) ^ (541561 + 541561) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 541561 * (2 : ZMod 138639701) ^ 541561 := by rw [pow_add]
          _ = 105891201 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 138639701) ^ 2166245 = 881657 := by
        calc
          (2 : ZMod 138639701) ^ 2166245 = (2 : ZMod 138639701) ^ (1083122 + 1083122 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 1083122 * (2 : ZMod 138639701) ^ 1083122) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 881657 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 138639701) ^ 4332490 = 104901843 := by
        calc
          (2 : ZMod 138639701) ^ 4332490 = (2 : ZMod 138639701) ^ (2166245 + 2166245) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 2166245 * (2 : ZMod 138639701) ^ 2166245 := by rw [pow_add]
          _ = 104901843 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 138639701) ^ 8664981 = 52084168 := by
        calc
          (2 : ZMod 138639701) ^ 8664981 = (2 : ZMod 138639701) ^ (4332490 + 4332490 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 4332490 * (2 : ZMod 138639701) ^ 4332490) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 52084168 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 138639701) ^ 17329962 = 22299842 := by
        calc
          (2 : ZMod 138639701) ^ 17329962 = (2 : ZMod 138639701) ^ (8664981 + 8664981) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 8664981 * (2 : ZMod 138639701) ^ 8664981 := by rw [pow_add]
          _ = 22299842 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 138639701) ^ 34659925 = 44599683 := by
        calc
          (2 : ZMod 138639701) ^ 34659925 = (2 : ZMod 138639701) ^ (17329962 + 17329962 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 17329962 * (2 : ZMod 138639701) ^ 17329962) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 44599683 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 138639701) ^ 69319850 = 138639700 := by
        calc
          (2 : ZMod 138639701) ^ 69319850 = (2 : ZMod 138639701) ^ (34659925 + 34659925) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 34659925 * (2 : ZMod 138639701) ^ 34659925 := by rw [pow_add]
          _ = 138639700 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 138639701) ^ 138639700 = 1 := by
        calc
          (2 : ZMod 138639701) ^ 138639700 = (2 : ZMod 138639701) ^ (69319850 + 69319850) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 69319850 * (2 : ZMod 138639701) ^ 69319850 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (113, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (113, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod = 138639701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 138639701) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 138639701) ^ 2 = 4 := by
        calc
          (2 : ZMod 138639701) ^ 2 = (2 : ZMod 138639701) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 1 * (2 : ZMod 138639701) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 138639701) ^ 4 = 16 := by
        calc
          (2 : ZMod 138639701) ^ 4 = (2 : ZMod 138639701) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 2 * (2 : ZMod 138639701) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 138639701) ^ 8 = 256 := by
        calc
          (2 : ZMod 138639701) ^ 8 = (2 : ZMod 138639701) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 4 * (2 : ZMod 138639701) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 138639701) ^ 16 = 65536 := by
        calc
          (2 : ZMod 138639701) ^ 16 = (2 : ZMod 138639701) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 8 * (2 : ZMod 138639701) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 138639701) ^ 33 = 132912831 := by
        calc
          (2 : ZMod 138639701) ^ 33 = (2 : ZMod 138639701) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 16 * (2 : ZMod 138639701) ^ 16) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 132912831 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 138639701) ^ 66 = 16409237 := by
        calc
          (2 : ZMod 138639701) ^ 66 = (2 : ZMod 138639701) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 33 * (2 : ZMod 138639701) ^ 33 := by rw [pow_add]
          _ = 16409237 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 138639701) ^ 132 = 81713391 := by
        calc
          (2 : ZMod 138639701) ^ 132 = (2 : ZMod 138639701) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 66 * (2 : ZMod 138639701) ^ 66 := by rw [pow_add]
          _ = 81713391 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 138639701) ^ 264 = 54889109 := by
        calc
          (2 : ZMod 138639701) ^ 264 = (2 : ZMod 138639701) ^ (132 + 132) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 132 * (2 : ZMod 138639701) ^ 132 := by rw [pow_add]
          _ = 54889109 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 138639701) ^ 528 = 7178229 := by
        calc
          (2 : ZMod 138639701) ^ 528 = (2 : ZMod 138639701) ^ (264 + 264) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 264 * (2 : ZMod 138639701) ^ 264 := by rw [pow_add]
          _ = 7178229 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 138639701) ^ 1057 = 3326160 := by
        calc
          (2 : ZMod 138639701) ^ 1057 = (2 : ZMod 138639701) ^ (528 + 528 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 528 * (2 : ZMod 138639701) ^ 528) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 3326160 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 138639701) ^ 2115 = 61691002 := by
        calc
          (2 : ZMod 138639701) ^ 2115 = (2 : ZMod 138639701) ^ (1057 + 1057 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 1057 * (2 : ZMod 138639701) ^ 1057) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 61691002 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 138639701) ^ 4230 = 11972639 := by
        calc
          (2 : ZMod 138639701) ^ 4230 = (2 : ZMod 138639701) ^ (2115 + 2115) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 2115 * (2 : ZMod 138639701) ^ 2115 := by rw [pow_add]
          _ = 11972639 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 138639701) ^ 8461 = 122579978 := by
        calc
          (2 : ZMod 138639701) ^ 8461 = (2 : ZMod 138639701) ^ (4230 + 4230 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 4230 * (2 : ZMod 138639701) ^ 4230) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 122579978 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 138639701) ^ 16923 = 18066911 := by
        calc
          (2 : ZMod 138639701) ^ 16923 = (2 : ZMod 138639701) ^ (8461 + 8461 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 8461 * (2 : ZMod 138639701) ^ 8461) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 18066911 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 138639701) ^ 33847 = 60734743 := by
        calc
          (2 : ZMod 138639701) ^ 33847 = (2 : ZMod 138639701) ^ (16923 + 16923 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 16923 * (2 : ZMod 138639701) ^ 16923) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 60734743 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 138639701) ^ 67695 = 103363517 := by
        calc
          (2 : ZMod 138639701) ^ 67695 = (2 : ZMod 138639701) ^ (33847 + 33847 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 33847 * (2 : ZMod 138639701) ^ 33847) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 103363517 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 138639701) ^ 135390 = 136020707 := by
        calc
          (2 : ZMod 138639701) ^ 135390 = (2 : ZMod 138639701) ^ (67695 + 67695) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 67695 * (2 : ZMod 138639701) ^ 67695 := by rw [pow_add]
          _ = 136020707 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 138639701) ^ 270780 = 69004762 := by
        calc
          (2 : ZMod 138639701) ^ 270780 = (2 : ZMod 138639701) ^ (135390 + 135390) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 135390 * (2 : ZMod 138639701) ^ 135390 := by rw [pow_add]
          _ = 69004762 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 138639701) ^ 541561 = 98793683 := by
        calc
          (2 : ZMod 138639701) ^ 541561 = (2 : ZMod 138639701) ^ (270780 + 270780 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 270780 * (2 : ZMod 138639701) ^ 270780) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 98793683 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 138639701) ^ 1083122 = 105891201 := by
        calc
          (2 : ZMod 138639701) ^ 1083122 = (2 : ZMod 138639701) ^ (541561 + 541561) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 541561 * (2 : ZMod 138639701) ^ 541561 := by rw [pow_add]
          _ = 105891201 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 138639701) ^ 2166245 = 881657 := by
        calc
          (2 : ZMod 138639701) ^ 2166245 = (2 : ZMod 138639701) ^ (1083122 + 1083122 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 1083122 * (2 : ZMod 138639701) ^ 1083122) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 881657 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 138639701) ^ 4332490 = 104901843 := by
        calc
          (2 : ZMod 138639701) ^ 4332490 = (2 : ZMod 138639701) ^ (2166245 + 2166245) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 2166245 * (2 : ZMod 138639701) ^ 2166245 := by rw [pow_add]
          _ = 104901843 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 138639701) ^ 8664981 = 52084168 := by
        calc
          (2 : ZMod 138639701) ^ 8664981 = (2 : ZMod 138639701) ^ (4332490 + 4332490 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 4332490 * (2 : ZMod 138639701) ^ 4332490) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 52084168 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 138639701) ^ 17329962 = 22299842 := by
        calc
          (2 : ZMod 138639701) ^ 17329962 = (2 : ZMod 138639701) ^ (8664981 + 8664981) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 8664981 * (2 : ZMod 138639701) ^ 8664981 := by rw [pow_add]
          _ = 22299842 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 138639701) ^ 34659925 = 44599683 := by
        calc
          (2 : ZMod 138639701) ^ 34659925 = (2 : ZMod 138639701) ^ (17329962 + 17329962 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 17329962 * (2 : ZMod 138639701) ^ 17329962) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 44599683 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 138639701) ^ 69319850 = 138639700 := by
        calc
          (2 : ZMod 138639701) ^ 69319850 = (2 : ZMod 138639701) ^ (34659925 + 34659925) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 34659925 * (2 : ZMod 138639701) ^ 34659925 := by rw [pow_add]
          _ = 138639700 := by rw [factor_0_25]; decide
      change (2 : ZMod 138639701) ^ 69319850 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (2 : ZMod 138639701) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 138639701) ^ 3 = 8 := by
        calc
          (2 : ZMod 138639701) ^ 3 = (2 : ZMod 138639701) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 1 * (2 : ZMod 138639701) ^ 1) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 138639701) ^ 6 = 64 := by
        calc
          (2 : ZMod 138639701) ^ 6 = (2 : ZMod 138639701) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 3 * (2 : ZMod 138639701) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 138639701) ^ 13 = 8192 := by
        calc
          (2 : ZMod 138639701) ^ 13 = (2 : ZMod 138639701) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 6 * (2 : ZMod 138639701) ^ 6) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 138639701) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 138639701) ^ 26 = (2 : ZMod 138639701) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 13 * (2 : ZMod 138639701) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 138639701) ^ 52 = 129425698 := by
        calc
          (2 : ZMod 138639701) ^ 52 = (2 : ZMod 138639701) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 26 * (2 : ZMod 138639701) ^ 26 := by rw [pow_add]
          _ = 129425698 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 138639701) ^ 105 = 56121092 := by
        calc
          (2 : ZMod 138639701) ^ 105 = (2 : ZMod 138639701) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 52 * (2 : ZMod 138639701) ^ 52) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 56121092 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 138639701) ^ 211 = 59097302 := by
        calc
          (2 : ZMod 138639701) ^ 211 = (2 : ZMod 138639701) ^ (105 + 105 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 105 * (2 : ZMod 138639701) ^ 105) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 59097302 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 138639701) ^ 423 = 52055643 := by
        calc
          (2 : ZMod 138639701) ^ 423 = (2 : ZMod 138639701) ^ (211 + 211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 211 * (2 : ZMod 138639701) ^ 211) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 52055643 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 138639701) ^ 846 = 67064394 := by
        calc
          (2 : ZMod 138639701) ^ 846 = (2 : ZMod 138639701) ^ (423 + 423) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 423 * (2 : ZMod 138639701) ^ 423 := by rw [pow_add]
          _ = 67064394 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 138639701) ^ 1692 = 81454375 := by
        calc
          (2 : ZMod 138639701) ^ 1692 = (2 : ZMod 138639701) ^ (846 + 846) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 846 * (2 : ZMod 138639701) ^ 846 := by rw [pow_add]
          _ = 81454375 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 138639701) ^ 3384 = 57903394 := by
        calc
          (2 : ZMod 138639701) ^ 3384 = (2 : ZMod 138639701) ^ (1692 + 1692) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 1692 * (2 : ZMod 138639701) ^ 1692 := by rw [pow_add]
          _ = 57903394 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 138639701) ^ 6769 = 106973631 := by
        calc
          (2 : ZMod 138639701) ^ 6769 = (2 : ZMod 138639701) ^ (3384 + 3384 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 3384 * (2 : ZMod 138639701) ^ 3384) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 106973631 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 138639701) ^ 13539 = 138526792 := by
        calc
          (2 : ZMod 138639701) ^ 13539 = (2 : ZMod 138639701) ^ (6769 + 6769 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 6769 * (2 : ZMod 138639701) ^ 6769) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 138526792 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 138639701) ^ 27078 = 132229490 := by
        calc
          (2 : ZMod 138639701) ^ 27078 = (2 : ZMod 138639701) ^ (13539 + 13539) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 13539 * (2 : ZMod 138639701) ^ 13539 := by rw [pow_add]
          _ = 132229490 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 138639701) ^ 54156 = 77283636 := by
        calc
          (2 : ZMod 138639701) ^ 54156 = (2 : ZMod 138639701) ^ (27078 + 27078) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 27078 * (2 : ZMod 138639701) ^ 27078 := by rw [pow_add]
          _ = 77283636 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 138639701) ^ 108312 = 4490027 := by
        calc
          (2 : ZMod 138639701) ^ 108312 = (2 : ZMod 138639701) ^ (54156 + 54156) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 54156 * (2 : ZMod 138639701) ^ 54156 := by rw [pow_add]
          _ = 4490027 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 138639701) ^ 216624 = 50339814 := by
        calc
          (2 : ZMod 138639701) ^ 216624 = (2 : ZMod 138639701) ^ (108312 + 108312) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 108312 * (2 : ZMod 138639701) ^ 108312 := by rw [pow_add]
          _ = 50339814 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 138639701) ^ 433249 = 10407509 := by
        calc
          (2 : ZMod 138639701) ^ 433249 = (2 : ZMod 138639701) ^ (216624 + 216624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 216624 * (2 : ZMod 138639701) ^ 216624) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 10407509 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 138639701) ^ 866498 = 95267203 := by
        calc
          (2 : ZMod 138639701) ^ 866498 = (2 : ZMod 138639701) ^ (433249 + 433249) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 433249 * (2 : ZMod 138639701) ^ 433249 := by rw [pow_add]
          _ = 95267203 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 138639701) ^ 1732996 = 39669410 := by
        calc
          (2 : ZMod 138639701) ^ 1732996 = (2 : ZMod 138639701) ^ (866498 + 866498) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 866498 * (2 : ZMod 138639701) ^ 866498 := by rw [pow_add]
          _ = 39669410 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 138639701) ^ 3465992 = 137776669 := by
        calc
          (2 : ZMod 138639701) ^ 3465992 = (2 : ZMod 138639701) ^ (1732996 + 1732996) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 1732996 * (2 : ZMod 138639701) ^ 1732996 := by rw [pow_add]
          _ = 137776669 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 138639701) ^ 6931985 = 103518504 := by
        calc
          (2 : ZMod 138639701) ^ 6931985 = (2 : ZMod 138639701) ^ (3465992 + 3465992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 3465992 * (2 : ZMod 138639701) ^ 3465992) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 103518504 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 138639701) ^ 13863970 = 124320958 := by
        calc
          (2 : ZMod 138639701) ^ 13863970 = (2 : ZMod 138639701) ^ (6931985 + 6931985) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 6931985 * (2 : ZMod 138639701) ^ 6931985 := by rw [pow_add]
          _ = 124320958 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 138639701) ^ 27727940 = 49754106 := by
        calc
          (2 : ZMod 138639701) ^ 27727940 = (2 : ZMod 138639701) ^ (13863970 + 13863970) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 13863970 * (2 : ZMod 138639701) ^ 13863970 := by rw [pow_add]
          _ = 49754106 := by rw [factor_1_23]; decide
      change (2 : ZMod 138639701) ^ 27727940 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (2 : ZMod 138639701) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 138639701) ^ 2 = 4 := by
        calc
          (2 : ZMod 138639701) ^ 2 = (2 : ZMod 138639701) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 1 * (2 : ZMod 138639701) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 138639701) ^ 4 = 16 := by
        calc
          (2 : ZMod 138639701) ^ 4 = (2 : ZMod 138639701) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 2 * (2 : ZMod 138639701) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 138639701) ^ 9 = 512 := by
        calc
          (2 : ZMod 138639701) ^ 9 = (2 : ZMod 138639701) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 4 * (2 : ZMod 138639701) ^ 4) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 138639701) ^ 18 = 262144 := by
        calc
          (2 : ZMod 138639701) ^ 18 = (2 : ZMod 138639701) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 9 * (2 : ZMod 138639701) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 138639701) ^ 37 = 47009781 := by
        calc
          (2 : ZMod 138639701) ^ 37 = (2 : ZMod 138639701) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 18 * (2 : ZMod 138639701) ^ 18) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 47009781 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 138639701) ^ 74 = 41573642 := by
        calc
          (2 : ZMod 138639701) ^ 74 = (2 : ZMod 138639701) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 37 * (2 : ZMod 138639701) ^ 37 := by rw [pow_add]
          _ = 41573642 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 138639701) ^ 149 = 4763799 := by
        calc
          (2 : ZMod 138639701) ^ 149 = (2 : ZMod 138639701) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 74 * (2 : ZMod 138639701) ^ 74) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 4763799 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 138639701) ^ 299 = 112430525 := by
        calc
          (2 : ZMod 138639701) ^ 299 = (2 : ZMod 138639701) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 149 * (2 : ZMod 138639701) ^ 149) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 112430525 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 138639701) ^ 599 = 14520512 := by
        calc
          (2 : ZMod 138639701) ^ 599 = (2 : ZMod 138639701) ^ (299 + 299 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 299 * (2 : ZMod 138639701) ^ 299) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 14520512 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 138639701) ^ 1198 = 70505530 := by
        calc
          (2 : ZMod 138639701) ^ 1198 = (2 : ZMod 138639701) ^ (599 + 599) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 599 * (2 : ZMod 138639701) ^ 599 := by rw [pow_add]
          _ = 70505530 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 138639701) ^ 2396 = 133288356 := by
        calc
          (2 : ZMod 138639701) ^ 2396 = (2 : ZMod 138639701) ^ (1198 + 1198) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 1198 * (2 : ZMod 138639701) ^ 1198 := by rw [pow_add]
          _ = 133288356 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 138639701) ^ 4792 = 31229269 := by
        calc
          (2 : ZMod 138639701) ^ 4792 = (2 : ZMod 138639701) ^ (2396 + 2396) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 2396 * (2 : ZMod 138639701) ^ 2396 := by rw [pow_add]
          _ = 31229269 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 138639701) ^ 9585 = 53606632 := by
        calc
          (2 : ZMod 138639701) ^ 9585 = (2 : ZMod 138639701) ^ (4792 + 4792 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 4792 * (2 : ZMod 138639701) ^ 4792) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 53606632 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 138639701) ^ 19170 = 93781505 := by
        calc
          (2 : ZMod 138639701) ^ 19170 = (2 : ZMod 138639701) ^ (9585 + 9585) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 9585 * (2 : ZMod 138639701) ^ 9585 := by rw [pow_add]
          _ = 93781505 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 138639701) ^ 38340 = 90708920 := by
        calc
          (2 : ZMod 138639701) ^ 38340 = (2 : ZMod 138639701) ^ (19170 + 19170) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 19170 * (2 : ZMod 138639701) ^ 19170 := by rw [pow_add]
          _ = 90708920 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 138639701) ^ 76681 = 63590781 := by
        calc
          (2 : ZMod 138639701) ^ 76681 = (2 : ZMod 138639701) ^ (38340 + 38340 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 38340 * (2 : ZMod 138639701) ^ 38340) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 63590781 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 138639701) ^ 153362 = 85302361 := by
        calc
          (2 : ZMod 138639701) ^ 153362 = (2 : ZMod 138639701) ^ (76681 + 76681) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 76681 * (2 : ZMod 138639701) ^ 76681 := by rw [pow_add]
          _ = 85302361 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 138639701) ^ 306725 = 16407214 := by
        calc
          (2 : ZMod 138639701) ^ 306725 = (2 : ZMod 138639701) ^ (153362 + 153362 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 153362 * (2 : ZMod 138639701) ^ 153362) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 16407214 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 138639701) ^ 613450 = 102449797 := by
        calc
          (2 : ZMod 138639701) ^ 613450 = (2 : ZMod 138639701) ^ (306725 + 306725) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 306725 * (2 : ZMod 138639701) ^ 306725 := by rw [pow_add]
          _ = 102449797 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 138639701) ^ 1226900 = 137578562 := by
        calc
          (2 : ZMod 138639701) ^ 1226900 = (2 : ZMod 138639701) ^ (613450 + 613450) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 613450 * (2 : ZMod 138639701) ^ 613450 := by rw [pow_add]
          _ = 137578562 := by rw [factor_2_19]; decide
      change (2 : ZMod 138639701) ^ 1226900 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (2 : ZMod 138639701) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 138639701) ^ 2 = 4 := by
        calc
          (2 : ZMod 138639701) ^ 2 = (2 : ZMod 138639701) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 1 * (2 : ZMod 138639701) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 138639701) ^ 5 = 32 := by
        calc
          (2 : ZMod 138639701) ^ 5 = (2 : ZMod 138639701) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 2 * (2 : ZMod 138639701) ^ 2) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 138639701) ^ 11 = 2048 := by
        calc
          (2 : ZMod 138639701) ^ 11 = (2 : ZMod 138639701) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 5 * (2 : ZMod 138639701) ^ 5) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 138639701) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 138639701) ^ 22 = (2 : ZMod 138639701) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 11 * (2 : ZMod 138639701) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 138639701) ^ 44 = 55744825 := by
        calc
          (2 : ZMod 138639701) ^ 44 = (2 : ZMod 138639701) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 22 * (2 : ZMod 138639701) ^ 22 := by rw [pow_add]
          _ = 55744825 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 138639701) ^ 88 = 5699515 := by
        calc
          (2 : ZMod 138639701) ^ 88 = (2 : ZMod 138639701) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 44 * (2 : ZMod 138639701) ^ 44 := by rw [pow_add]
          _ = 5699515 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 138639701) ^ 176 = 80173317 := by
        calc
          (2 : ZMod 138639701) ^ 176 = (2 : ZMod 138639701) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 88 * (2 : ZMod 138639701) ^ 88 := by rw [pow_add]
          _ = 80173317 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 138639701) ^ 353 = 104514559 := by
        calc
          (2 : ZMod 138639701) ^ 353 = (2 : ZMod 138639701) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 176 * (2 : ZMod 138639701) ^ 176) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 104514559 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 138639701) ^ 706 = 74736112 := by
        calc
          (2 : ZMod 138639701) ^ 706 = (2 : ZMod 138639701) ^ (353 + 353) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 353 * (2 : ZMod 138639701) ^ 353 := by rw [pow_add]
          _ = 74736112 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 138639701) ^ 1412 = 109163960 := by
        calc
          (2 : ZMod 138639701) ^ 1412 = (2 : ZMod 138639701) ^ (706 + 706) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 706 * (2 : ZMod 138639701) ^ 706 := by rw [pow_add]
          _ = 109163960 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 138639701) ^ 2825 = 2110177 := by
        calc
          (2 : ZMod 138639701) ^ 2825 = (2 : ZMod 138639701) ^ (1412 + 1412 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = ((2 : ZMod 138639701) ^ 1412 * (2 : ZMod 138639701) ^ 1412) * (2 : ZMod 138639701) := by rw [pow_succ, pow_add]
          _ = 2110177 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 138639701) ^ 5650 = 17054611 := by
        calc
          (2 : ZMod 138639701) ^ 5650 = (2 : ZMod 138639701) ^ (2825 + 2825) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 2825 * (2 : ZMod 138639701) ^ 2825 := by rw [pow_add]
          _ = 17054611 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 138639701) ^ 11300 = 41089567 := by
        calc
          (2 : ZMod 138639701) ^ 11300 = (2 : ZMod 138639701) ^ (5650 + 5650) :=
            congrArg (fun n : ℕ => (2 : ZMod 138639701) ^ n) (by norm_num)
          _ = (2 : ZMod 138639701) ^ 5650 * (2 : ZMod 138639701) ^ 5650 := by rw [pow_add]
          _ = 41089567 := by rw [factor_3_12]; decide
      change (2 : ZMod 138639701) ^ 11300 ≠ 1
      rw [factor_3_13]
      decide

#print axioms prime_lucas_138639701

end TotientTailPeriodKiller
end Erdos249257
