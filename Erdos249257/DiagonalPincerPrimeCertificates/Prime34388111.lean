import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_34388111 : Nat.Prime 34388111 := by
  apply lucas_primality 34388111 (14 : ZMod 34388111)
  ·
      have fermat_0 : (14 : ZMod 34388111) ^ 1 = 14 := by norm_num
      have fermat_1 : (14 : ZMod 34388111) ^ 2 = 196 := by
        calc
          (14 : ZMod 34388111) ^ 2 = (14 : ZMod 34388111) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1 * (14 : ZMod 34388111) ^ 1 := by rw [pow_add]
          _ = 196 := by rw [fermat_0]; decide
      have fermat_2 : (14 : ZMod 34388111) ^ 4 = 38416 := by
        calc
          (14 : ZMod 34388111) ^ 4 = (14 : ZMod 34388111) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 2 * (14 : ZMod 34388111) ^ 2 := by rw [pow_add]
          _ = 38416 := by rw [fermat_1]; decide
      have fermat_3 : (14 : ZMod 34388111) ^ 8 = 31488394 := by
        calc
          (14 : ZMod 34388111) ^ 8 = (14 : ZMod 34388111) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 4 * (14 : ZMod 34388111) ^ 4 := by rw [pow_add]
          _ = 31488394 := by rw [fermat_2]; decide
      have fermat_4 : (14 : ZMod 34388111) ^ 16 = 18495146 := by
        calc
          (14 : ZMod 34388111) ^ 16 = (14 : ZMod 34388111) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 8 * (14 : ZMod 34388111) ^ 8 := by rw [pow_add]
          _ = 18495146 := by rw [fermat_3]; decide
      have fermat_5 : (14 : ZMod 34388111) ^ 32 = 21546021 := by
        calc
          (14 : ZMod 34388111) ^ 32 = (14 : ZMod 34388111) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 16 * (14 : ZMod 34388111) ^ 16 := by rw [pow_add]
          _ = 21546021 := by rw [fermat_4]; decide
      have fermat_6 : (14 : ZMod 34388111) ^ 65 = 21813346 := by
        calc
          (14 : ZMod 34388111) ^ 65 = (14 : ZMod 34388111) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 32 * (14 : ZMod 34388111) ^ 32) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 21813346 := by rw [fermat_5]; decide
      have fermat_7 : (14 : ZMod 34388111) ^ 131 = 13571520 := by
        calc
          (14 : ZMod 34388111) ^ 131 = (14 : ZMod 34388111) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 65 * (14 : ZMod 34388111) ^ 65) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 13571520 := by rw [fermat_6]; decide
      have fermat_8 : (14 : ZMod 34388111) ^ 262 = 28171411 := by
        calc
          (14 : ZMod 34388111) ^ 262 = (14 : ZMod 34388111) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 131 * (14 : ZMod 34388111) ^ 131 := by rw [pow_add]
          _ = 28171411 := by rw [fermat_7]; decide
      have fermat_9 : (14 : ZMod 34388111) ^ 524 = 5237762 := by
        calc
          (14 : ZMod 34388111) ^ 524 = (14 : ZMod 34388111) ^ (262 + 262) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 262 * (14 : ZMod 34388111) ^ 262 := by rw [pow_add]
          _ = 5237762 := by rw [fermat_8]; decide
      have fermat_10 : (14 : ZMod 34388111) ^ 1049 = 15662785 := by
        calc
          (14 : ZMod 34388111) ^ 1049 = (14 : ZMod 34388111) ^ (524 + 524 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 524 * (14 : ZMod 34388111) ^ 524) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 15662785 := by rw [fermat_9]; decide
      have fermat_11 : (14 : ZMod 34388111) ^ 2098 = 10204552 := by
        calc
          (14 : ZMod 34388111) ^ 2098 = (14 : ZMod 34388111) ^ (1049 + 1049) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1049 * (14 : ZMod 34388111) ^ 1049 := by rw [pow_add]
          _ = 10204552 := by rw [fermat_10]; decide
      have fermat_12 : (14 : ZMod 34388111) ^ 4197 = 77113 := by
        calc
          (14 : ZMod 34388111) ^ 4197 = (14 : ZMod 34388111) ^ (2098 + 2098 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 2098 * (14 : ZMod 34388111) ^ 2098) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 77113 := by rw [fermat_11]; decide
      have fermat_13 : (14 : ZMod 34388111) ^ 8395 = 30578146 := by
        calc
          (14 : ZMod 34388111) ^ 8395 = (14 : ZMod 34388111) ^ (4197 + 4197 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 4197 * (14 : ZMod 34388111) ^ 4197) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 30578146 := by rw [fermat_12]; decide
      have fermat_14 : (14 : ZMod 34388111) ^ 16791 = 434111 := by
        calc
          (14 : ZMod 34388111) ^ 16791 = (14 : ZMod 34388111) ^ (8395 + 8395 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 8395 * (14 : ZMod 34388111) ^ 8395) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 434111 := by rw [fermat_13]; decide
      have fermat_15 : (14 : ZMod 34388111) ^ 33582 = 5512041 := by
        calc
          (14 : ZMod 34388111) ^ 33582 = (14 : ZMod 34388111) ^ (16791 + 16791) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 16791 * (14 : ZMod 34388111) ^ 16791 := by rw [pow_add]
          _ = 5512041 := by rw [fermat_14]; decide
      have fermat_16 : (14 : ZMod 34388111) ^ 67164 = 12154961 := by
        calc
          (14 : ZMod 34388111) ^ 67164 = (14 : ZMod 34388111) ^ (33582 + 33582) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 33582 * (14 : ZMod 34388111) ^ 33582 := by rw [pow_add]
          _ = 12154961 := by rw [fermat_15]; decide
      have fermat_17 : (14 : ZMod 34388111) ^ 134328 = 25709670 := by
        calc
          (14 : ZMod 34388111) ^ 134328 = (14 : ZMod 34388111) ^ (67164 + 67164) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 67164 * (14 : ZMod 34388111) ^ 67164 := by rw [pow_add]
          _ = 25709670 := by rw [fermat_16]; decide
      have fermat_18 : (14 : ZMod 34388111) ^ 268657 = 10219866 := by
        calc
          (14 : ZMod 34388111) ^ 268657 = (14 : ZMod 34388111) ^ (134328 + 134328 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 134328 * (14 : ZMod 34388111) ^ 134328) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 10219866 := by rw [fermat_17]; decide
      have fermat_19 : (14 : ZMod 34388111) ^ 537314 = 27042096 := by
        calc
          (14 : ZMod 34388111) ^ 537314 = (14 : ZMod 34388111) ^ (268657 + 268657) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 268657 * (14 : ZMod 34388111) ^ 268657 := by rw [pow_add]
          _ = 27042096 := by rw [fermat_18]; decide
      have fermat_20 : (14 : ZMod 34388111) ^ 1074628 = 14924254 := by
        calc
          (14 : ZMod 34388111) ^ 1074628 = (14 : ZMod 34388111) ^ (537314 + 537314) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 537314 * (14 : ZMod 34388111) ^ 537314 := by rw [pow_add]
          _ = 14924254 := by rw [fermat_19]; decide
      have fermat_21 : (14 : ZMod 34388111) ^ 2149256 = 15044521 := by
        calc
          (14 : ZMod 34388111) ^ 2149256 = (14 : ZMod 34388111) ^ (1074628 + 1074628) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1074628 * (14 : ZMod 34388111) ^ 1074628 := by rw [pow_add]
          _ = 15044521 := by rw [fermat_20]; decide
      have fermat_22 : (14 : ZMod 34388111) ^ 4298513 = 2959173 := by
        calc
          (14 : ZMod 34388111) ^ 4298513 = (14 : ZMod 34388111) ^ (2149256 + 2149256 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 2149256 * (14 : ZMod 34388111) ^ 2149256) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 2959173 := by rw [fermat_21]; decide
      have fermat_23 : (14 : ZMod 34388111) ^ 8597027 = 11383229 := by
        calc
          (14 : ZMod 34388111) ^ 8597027 = (14 : ZMod 34388111) ^ (4298513 + 4298513 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 4298513 * (14 : ZMod 34388111) ^ 4298513) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 11383229 := by rw [fermat_22]; decide
      have fermat_24 : (14 : ZMod 34388111) ^ 17194055 = 34388110 := by
        calc
          (14 : ZMod 34388111) ^ 17194055 = (14 : ZMod 34388111) ^ (8597027 + 8597027 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 8597027 * (14 : ZMod 34388111) ^ 8597027) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 34388110 := by rw [fermat_23]; decide
      have fermat_25 : (14 : ZMod 34388111) ^ 34388110 = 1 := by
        calc
          (14 : ZMod 34388111) ^ 34388110 = (14 : ZMod 34388111) ^ (17194055 + 17194055) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 17194055 * (14 : ZMod 34388111) ^ 17194055 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 2), (73, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 2), (73, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod = 34388111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (14 : ZMod 34388111) ^ 1 = 14 := by norm_num
      have factor_0_1 : (14 : ZMod 34388111) ^ 2 = 196 := by
        calc
          (14 : ZMod 34388111) ^ 2 = (14 : ZMod 34388111) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1 * (14 : ZMod 34388111) ^ 1 := by rw [pow_add]
          _ = 196 := by rw [factor_0_0]; decide
      have factor_0_2 : (14 : ZMod 34388111) ^ 4 = 38416 := by
        calc
          (14 : ZMod 34388111) ^ 4 = (14 : ZMod 34388111) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 2 * (14 : ZMod 34388111) ^ 2 := by rw [pow_add]
          _ = 38416 := by rw [factor_0_1]; decide
      have factor_0_3 : (14 : ZMod 34388111) ^ 8 = 31488394 := by
        calc
          (14 : ZMod 34388111) ^ 8 = (14 : ZMod 34388111) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 4 * (14 : ZMod 34388111) ^ 4 := by rw [pow_add]
          _ = 31488394 := by rw [factor_0_2]; decide
      have factor_0_4 : (14 : ZMod 34388111) ^ 16 = 18495146 := by
        calc
          (14 : ZMod 34388111) ^ 16 = (14 : ZMod 34388111) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 8 * (14 : ZMod 34388111) ^ 8 := by rw [pow_add]
          _ = 18495146 := by rw [factor_0_3]; decide
      have factor_0_5 : (14 : ZMod 34388111) ^ 32 = 21546021 := by
        calc
          (14 : ZMod 34388111) ^ 32 = (14 : ZMod 34388111) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 16 * (14 : ZMod 34388111) ^ 16 := by rw [pow_add]
          _ = 21546021 := by rw [factor_0_4]; decide
      have factor_0_6 : (14 : ZMod 34388111) ^ 65 = 21813346 := by
        calc
          (14 : ZMod 34388111) ^ 65 = (14 : ZMod 34388111) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 32 * (14 : ZMod 34388111) ^ 32) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 21813346 := by rw [factor_0_5]; decide
      have factor_0_7 : (14 : ZMod 34388111) ^ 131 = 13571520 := by
        calc
          (14 : ZMod 34388111) ^ 131 = (14 : ZMod 34388111) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 65 * (14 : ZMod 34388111) ^ 65) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 13571520 := by rw [factor_0_6]; decide
      have factor_0_8 : (14 : ZMod 34388111) ^ 262 = 28171411 := by
        calc
          (14 : ZMod 34388111) ^ 262 = (14 : ZMod 34388111) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 131 * (14 : ZMod 34388111) ^ 131 := by rw [pow_add]
          _ = 28171411 := by rw [factor_0_7]; decide
      have factor_0_9 : (14 : ZMod 34388111) ^ 524 = 5237762 := by
        calc
          (14 : ZMod 34388111) ^ 524 = (14 : ZMod 34388111) ^ (262 + 262) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 262 * (14 : ZMod 34388111) ^ 262 := by rw [pow_add]
          _ = 5237762 := by rw [factor_0_8]; decide
      have factor_0_10 : (14 : ZMod 34388111) ^ 1049 = 15662785 := by
        calc
          (14 : ZMod 34388111) ^ 1049 = (14 : ZMod 34388111) ^ (524 + 524 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 524 * (14 : ZMod 34388111) ^ 524) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 15662785 := by rw [factor_0_9]; decide
      have factor_0_11 : (14 : ZMod 34388111) ^ 2098 = 10204552 := by
        calc
          (14 : ZMod 34388111) ^ 2098 = (14 : ZMod 34388111) ^ (1049 + 1049) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1049 * (14 : ZMod 34388111) ^ 1049 := by rw [pow_add]
          _ = 10204552 := by rw [factor_0_10]; decide
      have factor_0_12 : (14 : ZMod 34388111) ^ 4197 = 77113 := by
        calc
          (14 : ZMod 34388111) ^ 4197 = (14 : ZMod 34388111) ^ (2098 + 2098 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 2098 * (14 : ZMod 34388111) ^ 2098) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 77113 := by rw [factor_0_11]; decide
      have factor_0_13 : (14 : ZMod 34388111) ^ 8395 = 30578146 := by
        calc
          (14 : ZMod 34388111) ^ 8395 = (14 : ZMod 34388111) ^ (4197 + 4197 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 4197 * (14 : ZMod 34388111) ^ 4197) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 30578146 := by rw [factor_0_12]; decide
      have factor_0_14 : (14 : ZMod 34388111) ^ 16791 = 434111 := by
        calc
          (14 : ZMod 34388111) ^ 16791 = (14 : ZMod 34388111) ^ (8395 + 8395 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 8395 * (14 : ZMod 34388111) ^ 8395) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 434111 := by rw [factor_0_13]; decide
      have factor_0_15 : (14 : ZMod 34388111) ^ 33582 = 5512041 := by
        calc
          (14 : ZMod 34388111) ^ 33582 = (14 : ZMod 34388111) ^ (16791 + 16791) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 16791 * (14 : ZMod 34388111) ^ 16791 := by rw [pow_add]
          _ = 5512041 := by rw [factor_0_14]; decide
      have factor_0_16 : (14 : ZMod 34388111) ^ 67164 = 12154961 := by
        calc
          (14 : ZMod 34388111) ^ 67164 = (14 : ZMod 34388111) ^ (33582 + 33582) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 33582 * (14 : ZMod 34388111) ^ 33582 := by rw [pow_add]
          _ = 12154961 := by rw [factor_0_15]; decide
      have factor_0_17 : (14 : ZMod 34388111) ^ 134328 = 25709670 := by
        calc
          (14 : ZMod 34388111) ^ 134328 = (14 : ZMod 34388111) ^ (67164 + 67164) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 67164 * (14 : ZMod 34388111) ^ 67164 := by rw [pow_add]
          _ = 25709670 := by rw [factor_0_16]; decide
      have factor_0_18 : (14 : ZMod 34388111) ^ 268657 = 10219866 := by
        calc
          (14 : ZMod 34388111) ^ 268657 = (14 : ZMod 34388111) ^ (134328 + 134328 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 134328 * (14 : ZMod 34388111) ^ 134328) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 10219866 := by rw [factor_0_17]; decide
      have factor_0_19 : (14 : ZMod 34388111) ^ 537314 = 27042096 := by
        calc
          (14 : ZMod 34388111) ^ 537314 = (14 : ZMod 34388111) ^ (268657 + 268657) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 268657 * (14 : ZMod 34388111) ^ 268657 := by rw [pow_add]
          _ = 27042096 := by rw [factor_0_18]; decide
      have factor_0_20 : (14 : ZMod 34388111) ^ 1074628 = 14924254 := by
        calc
          (14 : ZMod 34388111) ^ 1074628 = (14 : ZMod 34388111) ^ (537314 + 537314) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 537314 * (14 : ZMod 34388111) ^ 537314 := by rw [pow_add]
          _ = 14924254 := by rw [factor_0_19]; decide
      have factor_0_21 : (14 : ZMod 34388111) ^ 2149256 = 15044521 := by
        calc
          (14 : ZMod 34388111) ^ 2149256 = (14 : ZMod 34388111) ^ (1074628 + 1074628) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1074628 * (14 : ZMod 34388111) ^ 1074628 := by rw [pow_add]
          _ = 15044521 := by rw [factor_0_20]; decide
      have factor_0_22 : (14 : ZMod 34388111) ^ 4298513 = 2959173 := by
        calc
          (14 : ZMod 34388111) ^ 4298513 = (14 : ZMod 34388111) ^ (2149256 + 2149256 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 2149256 * (14 : ZMod 34388111) ^ 2149256) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 2959173 := by rw [factor_0_21]; decide
      have factor_0_23 : (14 : ZMod 34388111) ^ 8597027 = 11383229 := by
        calc
          (14 : ZMod 34388111) ^ 8597027 = (14 : ZMod 34388111) ^ (4298513 + 4298513 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 4298513 * (14 : ZMod 34388111) ^ 4298513) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 11383229 := by rw [factor_0_22]; decide
      have factor_0_24 : (14 : ZMod 34388111) ^ 17194055 = 34388110 := by
        calc
          (14 : ZMod 34388111) ^ 17194055 = (14 : ZMod 34388111) ^ (8597027 + 8597027 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 8597027 * (14 : ZMod 34388111) ^ 8597027) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 34388110 := by rw [factor_0_23]; decide
      change (14 : ZMod 34388111) ^ 17194055 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (14 : ZMod 34388111) ^ 1 = 14 := by norm_num
      have factor_1_1 : (14 : ZMod 34388111) ^ 3 = 2744 := by
        calc
          (14 : ZMod 34388111) ^ 3 = (14 : ZMod 34388111) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 1 * (14 : ZMod 34388111) ^ 1) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 2744 := by rw [factor_1_0]; decide
      have factor_1_2 : (14 : ZMod 34388111) ^ 6 = 7529536 := by
        calc
          (14 : ZMod 34388111) ^ 6 = (14 : ZMod 34388111) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 3 * (14 : ZMod 34388111) ^ 3 := by rw [pow_add]
          _ = 7529536 := by rw [factor_1_1]; decide
      have factor_1_3 : (14 : ZMod 34388111) ^ 13 = 32214264 := by
        calc
          (14 : ZMod 34388111) ^ 13 = (14 : ZMod 34388111) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 6 * (14 : ZMod 34388111) ^ 6) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 32214264 := by rw [factor_1_2]; decide
      have factor_1_4 : (14 : ZMod 34388111) ^ 26 = 30953900 := by
        calc
          (14 : ZMod 34388111) ^ 26 = (14 : ZMod 34388111) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 13 * (14 : ZMod 34388111) ^ 13 := by rw [pow_add]
          _ = 30953900 := by rw [factor_1_3]; decide
      have factor_1_5 : (14 : ZMod 34388111) ^ 52 = 24255850 := by
        calc
          (14 : ZMod 34388111) ^ 52 = (14 : ZMod 34388111) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 26 * (14 : ZMod 34388111) ^ 26 := by rw [pow_add]
          _ = 24255850 := by rw [factor_1_4]; decide
      have factor_1_6 : (14 : ZMod 34388111) ^ 104 = 33735389 := by
        calc
          (14 : ZMod 34388111) ^ 104 = (14 : ZMod 34388111) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 52 * (14 : ZMod 34388111) ^ 52 := by rw [pow_add]
          _ = 33735389 := by rw [factor_1_5]; decide
      have factor_1_7 : (14 : ZMod 34388111) ^ 209 = 26277026 := by
        calc
          (14 : ZMod 34388111) ^ 209 = (14 : ZMod 34388111) ^ (104 + 104 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 104 * (14 : ZMod 34388111) ^ 104) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 26277026 := by rw [factor_1_6]; decide
      have factor_1_8 : (14 : ZMod 34388111) ^ 419 = 25250276 := by
        calc
          (14 : ZMod 34388111) ^ 419 = (14 : ZMod 34388111) ^ (209 + 209 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 209 * (14 : ZMod 34388111) ^ 209) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 25250276 := by rw [factor_1_7]; decide
      have factor_1_9 : (14 : ZMod 34388111) ^ 839 = 18067852 := by
        calc
          (14 : ZMod 34388111) ^ 839 = (14 : ZMod 34388111) ^ (419 + 419 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 419 * (14 : ZMod 34388111) ^ 419) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 18067852 := by rw [factor_1_8]; decide
      have factor_1_10 : (14 : ZMod 34388111) ^ 1679 = 32522365 := by
        calc
          (14 : ZMod 34388111) ^ 1679 = (14 : ZMod 34388111) ^ (839 + 839 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 839 * (14 : ZMod 34388111) ^ 839) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 32522365 := by rw [factor_1_9]; decide
      have factor_1_11 : (14 : ZMod 34388111) ^ 3358 = 2824319 := by
        calc
          (14 : ZMod 34388111) ^ 3358 = (14 : ZMod 34388111) ^ (1679 + 1679) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1679 * (14 : ZMod 34388111) ^ 1679 := by rw [pow_add]
          _ = 2824319 := by rw [factor_1_10]; decide
      have factor_1_12 : (14 : ZMod 34388111) ^ 6716 = 8421868 := by
        calc
          (14 : ZMod 34388111) ^ 6716 = (14 : ZMod 34388111) ^ (3358 + 3358) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 3358 * (14 : ZMod 34388111) ^ 3358 := by rw [pow_add]
          _ = 8421868 := by rw [factor_1_11]; decide
      have factor_1_13 : (14 : ZMod 34388111) ^ 13432 = 8892265 := by
        calc
          (14 : ZMod 34388111) ^ 13432 = (14 : ZMod 34388111) ^ (6716 + 6716) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 6716 * (14 : ZMod 34388111) ^ 6716 := by rw [pow_add]
          _ = 8892265 := by rw [factor_1_12]; decide
      have factor_1_14 : (14 : ZMod 34388111) ^ 26865 = 9667566 := by
        calc
          (14 : ZMod 34388111) ^ 26865 = (14 : ZMod 34388111) ^ (13432 + 13432 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 13432 * (14 : ZMod 34388111) ^ 13432) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 9667566 := by rw [factor_1_13]; decide
      have factor_1_15 : (14 : ZMod 34388111) ^ 53731 = 24061422 := by
        calc
          (14 : ZMod 34388111) ^ 53731 = (14 : ZMod 34388111) ^ (26865 + 26865 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 26865 * (14 : ZMod 34388111) ^ 26865) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 24061422 := by rw [factor_1_14]; decide
      have factor_1_16 : (14 : ZMod 34388111) ^ 107462 = 16114175 := by
        calc
          (14 : ZMod 34388111) ^ 107462 = (14 : ZMod 34388111) ^ (53731 + 53731) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 53731 * (14 : ZMod 34388111) ^ 53731 := by rw [pow_add]
          _ = 16114175 := by rw [factor_1_15]; decide
      have factor_1_17 : (14 : ZMod 34388111) ^ 214925 = 7299952 := by
        calc
          (14 : ZMod 34388111) ^ 214925 = (14 : ZMod 34388111) ^ (107462 + 107462 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 107462 * (14 : ZMod 34388111) ^ 107462) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 7299952 := by rw [factor_1_16]; decide
      have factor_1_18 : (14 : ZMod 34388111) ^ 429851 = 17522923 := by
        calc
          (14 : ZMod 34388111) ^ 429851 = (14 : ZMod 34388111) ^ (214925 + 214925 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 214925 * (14 : ZMod 34388111) ^ 214925) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 17522923 := by rw [factor_1_17]; decide
      have factor_1_19 : (14 : ZMod 34388111) ^ 859702 = 11820489 := by
        calc
          (14 : ZMod 34388111) ^ 859702 = (14 : ZMod 34388111) ^ (429851 + 429851) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 429851 * (14 : ZMod 34388111) ^ 429851 := by rw [pow_add]
          _ = 11820489 := by rw [factor_1_18]; decide
      have factor_1_20 : (14 : ZMod 34388111) ^ 1719405 = 4600812 := by
        calc
          (14 : ZMod 34388111) ^ 1719405 = (14 : ZMod 34388111) ^ (859702 + 859702 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 859702 * (14 : ZMod 34388111) ^ 859702) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 4600812 := by rw [factor_1_19]; decide
      have factor_1_21 : (14 : ZMod 34388111) ^ 3438811 = 27624110 := by
        calc
          (14 : ZMod 34388111) ^ 3438811 = (14 : ZMod 34388111) ^ (1719405 + 1719405 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 1719405 * (14 : ZMod 34388111) ^ 1719405) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 27624110 := by rw [factor_1_20]; decide
      have factor_1_22 : (14 : ZMod 34388111) ^ 6877622 = 12859940 := by
        calc
          (14 : ZMod 34388111) ^ 6877622 = (14 : ZMod 34388111) ^ (3438811 + 3438811) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 3438811 * (14 : ZMod 34388111) ^ 3438811 := by rw [pow_add]
          _ = 12859940 := by rw [factor_1_21]; decide
      change (14 : ZMod 34388111) ^ 6877622 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (14 : ZMod 34388111) ^ 1 = 14 := by norm_num
      have factor_2_1 : (14 : ZMod 34388111) ^ 3 = 2744 := by
        calc
          (14 : ZMod 34388111) ^ 3 = (14 : ZMod 34388111) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 1 * (14 : ZMod 34388111) ^ 1) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 2744 := by rw [factor_2_0]; decide
      have factor_2_2 : (14 : ZMod 34388111) ^ 7 = 2249171 := by
        calc
          (14 : ZMod 34388111) ^ 7 = (14 : ZMod 34388111) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 3 * (14 : ZMod 34388111) ^ 3) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 2249171 := by rw [factor_2_1]; decide
      have factor_2_3 : (14 : ZMod 34388111) ^ 15 = 20971431 := by
        calc
          (14 : ZMod 34388111) ^ 15 = (14 : ZMod 34388111) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 7 * (14 : ZMod 34388111) ^ 7) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 20971431 := by rw [factor_2_2]; decide
      have factor_2_4 : (14 : ZMod 34388111) ^ 30 = 18532131 := by
        calc
          (14 : ZMod 34388111) ^ 30 = (14 : ZMod 34388111) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 15 * (14 : ZMod 34388111) ^ 15 := by rw [pow_add]
          _ = 18532131 := by rw [factor_2_3]; decide
      have factor_2_5 : (14 : ZMod 34388111) ^ 61 = 11159517 := by
        calc
          (14 : ZMod 34388111) ^ 61 = (14 : ZMod 34388111) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 30 * (14 : ZMod 34388111) ^ 30) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 11159517 := by rw [factor_2_4]; decide
      have factor_2_6 : (14 : ZMod 34388111) ^ 123 = 68968 := by
        calc
          (14 : ZMod 34388111) ^ 123 = (14 : ZMod 34388111) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 61 * (14 : ZMod 34388111) ^ 61) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 68968 := by rw [factor_2_5]; decide
      have factor_2_7 : (14 : ZMod 34388111) ^ 246 = 11025706 := by
        calc
          (14 : ZMod 34388111) ^ 246 = (14 : ZMod 34388111) ^ (123 + 123) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 123 * (14 : ZMod 34388111) ^ 123 := by rw [pow_add]
          _ = 11025706 := by rw [factor_2_6]; decide
      have factor_2_8 : (14 : ZMod 34388111) ^ 493 = 7013406 := by
        calc
          (14 : ZMod 34388111) ^ 493 = (14 : ZMod 34388111) ^ (246 + 246 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 246 * (14 : ZMod 34388111) ^ 246) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 7013406 := by rw [factor_2_7]; decide
      have factor_2_9 : (14 : ZMod 34388111) ^ 987 = 19334397 := by
        calc
          (14 : ZMod 34388111) ^ 987 = (14 : ZMod 34388111) ^ (493 + 493 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 493 * (14 : ZMod 34388111) ^ 493) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 19334397 := by rw [factor_2_8]; decide
      have factor_2_10 : (14 : ZMod 34388111) ^ 1975 = 22848437 := by
        calc
          (14 : ZMod 34388111) ^ 1975 = (14 : ZMod 34388111) ^ (987 + 987 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 987 * (14 : ZMod 34388111) ^ 987) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 22848437 := by rw [factor_2_9]; decide
      have factor_2_11 : (14 : ZMod 34388111) ^ 3950 = 2035319 := by
        calc
          (14 : ZMod 34388111) ^ 3950 = (14 : ZMod 34388111) ^ (1975 + 1975) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1975 * (14 : ZMod 34388111) ^ 1975 := by rw [pow_add]
          _ = 2035319 := by rw [factor_2_10]; decide
      have factor_2_12 : (14 : ZMod 34388111) ^ 7901 = 19559931 := by
        calc
          (14 : ZMod 34388111) ^ 7901 = (14 : ZMod 34388111) ^ (3950 + 3950 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 3950 * (14 : ZMod 34388111) ^ 3950) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 19559931 := by rw [factor_2_11]; decide
      have factor_2_13 : (14 : ZMod 34388111) ^ 15803 = 7621813 := by
        calc
          (14 : ZMod 34388111) ^ 15803 = (14 : ZMod 34388111) ^ (7901 + 7901 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 7901 * (14 : ZMod 34388111) ^ 7901) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 7621813 := by rw [factor_2_12]; decide
      have factor_2_14 : (14 : ZMod 34388111) ^ 31606 = 25554114 := by
        calc
          (14 : ZMod 34388111) ^ 31606 = (14 : ZMod 34388111) ^ (15803 + 15803) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 15803 * (14 : ZMod 34388111) ^ 15803 := by rw [pow_add]
          _ = 25554114 := by rw [factor_2_13]; decide
      have factor_2_15 : (14 : ZMod 34388111) ^ 63213 = 11052153 := by
        calc
          (14 : ZMod 34388111) ^ 63213 = (14 : ZMod 34388111) ^ (31606 + 31606 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 31606 * (14 : ZMod 34388111) ^ 31606) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 11052153 := by rw [factor_2_14]; decide
      have factor_2_16 : (14 : ZMod 34388111) ^ 126426 = 8076087 := by
        calc
          (14 : ZMod 34388111) ^ 126426 = (14 : ZMod 34388111) ^ (63213 + 63213) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 63213 * (14 : ZMod 34388111) ^ 63213 := by rw [pow_add]
          _ = 8076087 := by rw [factor_2_15]; decide
      have factor_2_17 : (14 : ZMod 34388111) ^ 252853 = 3744021 := by
        calc
          (14 : ZMod 34388111) ^ 252853 = (14 : ZMod 34388111) ^ (126426 + 126426 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 126426 * (14 : ZMod 34388111) ^ 126426) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 3744021 := by rw [factor_2_16]; decide
      have factor_2_18 : (14 : ZMod 34388111) ^ 505707 = 17382157 := by
        calc
          (14 : ZMod 34388111) ^ 505707 = (14 : ZMod 34388111) ^ (252853 + 252853 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 252853 * (14 : ZMod 34388111) ^ 252853) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 17382157 := by rw [factor_2_17]; decide
      have factor_2_19 : (14 : ZMod 34388111) ^ 1011415 = 6895332 := by
        calc
          (14 : ZMod 34388111) ^ 1011415 = (14 : ZMod 34388111) ^ (505707 + 505707 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 505707 * (14 : ZMod 34388111) ^ 505707) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 6895332 := by rw [factor_2_18]; decide
      have factor_2_20 : (14 : ZMod 34388111) ^ 2022830 = 16523737 := by
        calc
          (14 : ZMod 34388111) ^ 2022830 = (14 : ZMod 34388111) ^ (1011415 + 1011415) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1011415 * (14 : ZMod 34388111) ^ 1011415 := by rw [pow_add]
          _ = 16523737 := by rw [factor_2_19]; decide
      change (14 : ZMod 34388111) ^ 2022830 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (14 : ZMod 34388111) ^ 1 = 14 := by norm_num
      have factor_3_1 : (14 : ZMod 34388111) ^ 3 = 2744 := by
        calc
          (14 : ZMod 34388111) ^ 3 = (14 : ZMod 34388111) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 1 * (14 : ZMod 34388111) ^ 1) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 2744 := by rw [factor_3_0]; decide
      have factor_3_2 : (14 : ZMod 34388111) ^ 7 = 2249171 := by
        calc
          (14 : ZMod 34388111) ^ 7 = (14 : ZMod 34388111) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 3 * (14 : ZMod 34388111) ^ 3) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 2249171 := by rw [factor_3_1]; decide
      have factor_3_3 : (14 : ZMod 34388111) ^ 14 = 3954253 := by
        calc
          (14 : ZMod 34388111) ^ 14 = (14 : ZMod 34388111) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 7 * (14 : ZMod 34388111) ^ 7 := by rw [pow_add]
          _ = 3954253 := by rw [factor_3_2]; decide
      have factor_3_4 : (14 : ZMod 34388111) ^ 28 = 14656864 := by
        calc
          (14 : ZMod 34388111) ^ 28 = (14 : ZMod 34388111) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 14 * (14 : ZMod 34388111) ^ 14 := by rw [pow_add]
          _ = 14656864 := by rw [factor_3_3]; decide
      have factor_3_5 : (14 : ZMod 34388111) ^ 57 = 7645773 := by
        calc
          (14 : ZMod 34388111) ^ 57 = (14 : ZMod 34388111) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 28 * (14 : ZMod 34388111) ^ 28) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 7645773 := by rw [factor_3_4]; decide
      have factor_3_6 : (14 : ZMod 34388111) ^ 115 = 20329318 := by
        calc
          (14 : ZMod 34388111) ^ 115 = (14 : ZMod 34388111) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 57 * (14 : ZMod 34388111) ^ 57) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 20329318 := by rw [factor_3_5]; decide
      have factor_3_7 : (14 : ZMod 34388111) ^ 230 = 3623473 := by
        calc
          (14 : ZMod 34388111) ^ 230 = (14 : ZMod 34388111) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 115 * (14 : ZMod 34388111) ^ 115 := by rw [pow_add]
          _ = 3623473 := by rw [factor_3_6]; decide
      have factor_3_8 : (14 : ZMod 34388111) ^ 460 = 3861374 := by
        calc
          (14 : ZMod 34388111) ^ 460 = (14 : ZMod 34388111) ^ (230 + 230) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 230 * (14 : ZMod 34388111) ^ 230 := by rw [pow_add]
          _ = 3861374 := by rw [factor_3_7]; decide
      have factor_3_9 : (14 : ZMod 34388111) ^ 920 = 5671830 := by
        calc
          (14 : ZMod 34388111) ^ 920 = (14 : ZMod 34388111) ^ (460 + 460) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 460 * (14 : ZMod 34388111) ^ 460 := by rw [pow_add]
          _ = 5671830 := by rw [factor_3_8]; decide
      have factor_3_10 : (14 : ZMod 34388111) ^ 1840 = 24753843 := by
        calc
          (14 : ZMod 34388111) ^ 1840 = (14 : ZMod 34388111) ^ (920 + 920) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 920 * (14 : ZMod 34388111) ^ 920 := by rw [pow_add]
          _ = 24753843 := by rw [factor_3_9]; decide
      have factor_3_11 : (14 : ZMod 34388111) ^ 3680 = 3044731 := by
        calc
          (14 : ZMod 34388111) ^ 3680 = (14 : ZMod 34388111) ^ (1840 + 1840) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1840 * (14 : ZMod 34388111) ^ 1840 := by rw [pow_add]
          _ = 3044731 := by rw [factor_3_10]; decide
      have factor_3_12 : (14 : ZMod 34388111) ^ 7360 = 5510870 := by
        calc
          (14 : ZMod 34388111) ^ 7360 = (14 : ZMod 34388111) ^ (3680 + 3680) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 3680 * (14 : ZMod 34388111) ^ 3680 := by rw [pow_add]
          _ = 5510870 := by rw [factor_3_11]; decide
      have factor_3_13 : (14 : ZMod 34388111) ^ 14720 = 34255916 := by
        calc
          (14 : ZMod 34388111) ^ 14720 = (14 : ZMod 34388111) ^ (7360 + 7360) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 7360 * (14 : ZMod 34388111) ^ 7360 := by rw [pow_add]
          _ = 34255916 := by rw [factor_3_12]; decide
      have factor_3_14 : (14 : ZMod 34388111) ^ 29441 = 20230696 := by
        calc
          (14 : ZMod 34388111) ^ 29441 = (14 : ZMod 34388111) ^ (14720 + 14720 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 14720 * (14 : ZMod 34388111) ^ 14720) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 20230696 := by rw [factor_3_13]; decide
      have factor_3_15 : (14 : ZMod 34388111) ^ 58883 = 727653 := by
        calc
          (14 : ZMod 34388111) ^ 58883 = (14 : ZMod 34388111) ^ (29441 + 29441 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 29441 * (14 : ZMod 34388111) ^ 29441) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 727653 := by rw [factor_3_14]; decide
      have factor_3_16 : (14 : ZMod 34388111) ^ 117767 = 3230566 := by
        calc
          (14 : ZMod 34388111) ^ 117767 = (14 : ZMod 34388111) ^ (58883 + 58883 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 58883 * (14 : ZMod 34388111) ^ 58883) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 3230566 := by rw [factor_3_15]; decide
      have factor_3_17 : (14 : ZMod 34388111) ^ 235535 = 11144640 := by
        calc
          (14 : ZMod 34388111) ^ 235535 = (14 : ZMod 34388111) ^ (117767 + 117767 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 117767 * (14 : ZMod 34388111) ^ 117767) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 11144640 := by rw [factor_3_16]; decide
      have factor_3_18 : (14 : ZMod 34388111) ^ 471070 = 21419800 := by
        calc
          (14 : ZMod 34388111) ^ 471070 = (14 : ZMod 34388111) ^ (235535 + 235535) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 235535 * (14 : ZMod 34388111) ^ 235535 := by rw [pow_add]
          _ = 21419800 := by rw [factor_3_17]; decide
      change (14 : ZMod 34388111) ^ 471070 ≠ 1
      rw [factor_3_18]
      decide
    ·
      have factor_4_0 : (14 : ZMod 34388111) ^ 1 = 14 := by norm_num
      have factor_4_1 : (14 : ZMod 34388111) ^ 3 = 2744 := by
        calc
          (14 : ZMod 34388111) ^ 3 = (14 : ZMod 34388111) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 1 * (14 : ZMod 34388111) ^ 1) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 2744 := by rw [factor_4_0]; decide
      have factor_4_2 : (14 : ZMod 34388111) ^ 6 = 7529536 := by
        calc
          (14 : ZMod 34388111) ^ 6 = (14 : ZMod 34388111) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 3 * (14 : ZMod 34388111) ^ 3 := by rw [pow_add]
          _ = 7529536 := by rw [factor_4_1]; decide
      have factor_4_3 : (14 : ZMod 34388111) ^ 12 = 21951368 := by
        calc
          (14 : ZMod 34388111) ^ 12 = (14 : ZMod 34388111) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 6 * (14 : ZMod 34388111) ^ 6 := by rw [pow_add]
          _ = 21951368 := by rw [factor_4_2]; decide
      have factor_4_4 : (14 : ZMod 34388111) ^ 25 = 21861342 := by
        calc
          (14 : ZMod 34388111) ^ 25 = (14 : ZMod 34388111) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 12 * (14 : ZMod 34388111) ^ 12) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 21861342 := by rw [factor_4_3]; decide
      have factor_4_5 : (14 : ZMod 34388111) ^ 51 = 6645148 := by
        calc
          (14 : ZMod 34388111) ^ 51 = (14 : ZMod 34388111) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 25 * (14 : ZMod 34388111) ^ 25) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 6645148 := by rw [factor_4_4]; decide
      have factor_4_6 : (14 : ZMod 34388111) ^ 103 = 34341488 := by
        calc
          (14 : ZMod 34388111) ^ 103 = (14 : ZMod 34388111) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 51 * (14 : ZMod 34388111) ^ 51) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 34341488 := by rw [factor_4_5]; decide
      have factor_4_7 : (14 : ZMod 34388111) ^ 206 = 7253136 := by
        calc
          (14 : ZMod 34388111) ^ 206 = (14 : ZMod 34388111) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 103 * (14 : ZMod 34388111) ^ 103 := by rw [pow_add]
          _ = 7253136 := by rw [factor_4_6]; decide
      have factor_4_8 : (14 : ZMod 34388111) ^ 412 = 17983366 := by
        calc
          (14 : ZMod 34388111) ^ 412 = (14 : ZMod 34388111) ^ (206 + 206) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 206 * (14 : ZMod 34388111) ^ 206 := by rw [pow_add]
          _ = 17983366 := by rw [factor_4_7]; decide
      have factor_4_9 : (14 : ZMod 34388111) ^ 824 = 10255451 := by
        calc
          (14 : ZMod 34388111) ^ 824 = (14 : ZMod 34388111) ^ (412 + 412) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 412 * (14 : ZMod 34388111) ^ 412 := by rw [pow_add]
          _ = 10255451 := by rw [factor_4_8]; decide
      have factor_4_10 : (14 : ZMod 34388111) ^ 1648 = 25901673 := by
        calc
          (14 : ZMod 34388111) ^ 1648 = (14 : ZMod 34388111) ^ (824 + 824) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 824 * (14 : ZMod 34388111) ^ 824 := by rw [pow_add]
          _ = 25901673 := by rw [factor_4_9]; decide
      have factor_4_11 : (14 : ZMod 34388111) ^ 3296 = 24462657 := by
        calc
          (14 : ZMod 34388111) ^ 3296 = (14 : ZMod 34388111) ^ (1648 + 1648) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 1648 * (14 : ZMod 34388111) ^ 1648 := by rw [pow_add]
          _ = 24462657 := by rw [factor_4_10]; decide
      have factor_4_12 : (14 : ZMod 34388111) ^ 6592 = 23758759 := by
        calc
          (14 : ZMod 34388111) ^ 6592 = (14 : ZMod 34388111) ^ (3296 + 3296) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 3296 * (14 : ZMod 34388111) ^ 3296 := by rw [pow_add]
          _ = 23758759 := by rw [factor_4_11]; decide
      have factor_4_13 : (14 : ZMod 34388111) ^ 13185 = 3859145 := by
        calc
          (14 : ZMod 34388111) ^ 13185 = (14 : ZMod 34388111) ^ (6592 + 6592 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 6592 * (14 : ZMod 34388111) ^ 6592) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 3859145 := by rw [factor_4_12]; decide
      have factor_4_14 : (14 : ZMod 34388111) ^ 26371 = 7219150 := by
        calc
          (14 : ZMod 34388111) ^ 26371 = (14 : ZMod 34388111) ^ (13185 + 13185 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 13185 * (14 : ZMod 34388111) ^ 13185) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 7219150 := by rw [factor_4_13]; decide
      have factor_4_15 : (14 : ZMod 34388111) ^ 52742 = 16023003 := by
        calc
          (14 : ZMod 34388111) ^ 52742 = (14 : ZMod 34388111) ^ (26371 + 26371) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 26371 * (14 : ZMod 34388111) ^ 26371 := by rw [pow_add]
          _ = 16023003 := by rw [factor_4_14]; decide
      have factor_4_16 : (14 : ZMod 34388111) ^ 105485 = 23902677 := by
        calc
          (14 : ZMod 34388111) ^ 105485 = (14 : ZMod 34388111) ^ (52742 + 52742 + 1) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = ((14 : ZMod 34388111) ^ 52742 * (14 : ZMod 34388111) ^ 52742) * (14 : ZMod 34388111) := by rw [pow_succ, pow_add]
          _ = 23902677 := by rw [factor_4_15]; decide
      have factor_4_17 : (14 : ZMod 34388111) ^ 210970 = 33203596 := by
        calc
          (14 : ZMod 34388111) ^ 210970 = (14 : ZMod 34388111) ^ (105485 + 105485) :=
            congrArg (fun n : ℕ => (14 : ZMod 34388111) ^ n) (by norm_num)
          _ = (14 : ZMod 34388111) ^ 105485 * (14 : ZMod 34388111) ^ 105485 := by rw [pow_add]
          _ = 33203596 := by rw [factor_4_16]; decide
      change (14 : ZMod 34388111) ^ 210970 ≠ 1
      rw [factor_4_17]
      decide

#print axioms prime_lucas_34388111

end TotientTailPeriodKiller
end Erdos249257
