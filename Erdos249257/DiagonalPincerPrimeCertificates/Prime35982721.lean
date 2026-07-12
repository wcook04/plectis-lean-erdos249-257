import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_35982721 : Nat.Prime 35982721 := by
  apply lucas_primality 35982721 (17 : ZMod 35982721)
  ·
      have fermat_0 : (17 : ZMod 35982721) ^ 1 = 17 := by norm_num
      have fermat_1 : (17 : ZMod 35982721) ^ 2 = 289 := by
        calc
          (17 : ZMod 35982721) ^ 2 = (17 : ZMod 35982721) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1 * (17 : ZMod 35982721) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [fermat_0]; decide
      have fermat_2 : (17 : ZMod 35982721) ^ 4 = 83521 := by
        calc
          (17 : ZMod 35982721) ^ 4 = (17 : ZMod 35982721) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 2 * (17 : ZMod 35982721) ^ 2 := by rw [pow_add]
          _ = 83521 := by rw [fermat_1]; decide
      have fermat_3 : (17 : ZMod 35982721) ^ 8 = 31092288 := by
        calc
          (17 : ZMod 35982721) ^ 8 = (17 : ZMod 35982721) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 4 * (17 : ZMod 35982721) ^ 4 := by rw [pow_add]
          _ = 31092288 := by rw [fermat_2]; decide
      have fermat_4 : (17 : ZMod 35982721) ^ 17 = 5473505 := by
        calc
          (17 : ZMod 35982721) ^ 17 = (17 : ZMod 35982721) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 8 * (17 : ZMod 35982721) ^ 8) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 5473505 := by rw [fermat_3]; decide
      have fermat_5 : (17 : ZMod 35982721) ^ 34 = 7497704 := by
        calc
          (17 : ZMod 35982721) ^ 34 = (17 : ZMod 35982721) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 17 * (17 : ZMod 35982721) ^ 17 := by rw [pow_add]
          _ = 7497704 := by rw [fermat_4]; decide
      have fermat_6 : (17 : ZMod 35982721) ^ 68 = 12132363 := by
        calc
          (17 : ZMod 35982721) ^ 68 = (17 : ZMod 35982721) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 34 * (17 : ZMod 35982721) ^ 34 := by rw [pow_add]
          _ = 12132363 := by rw [fermat_5]; decide
      have fermat_7 : (17 : ZMod 35982721) ^ 137 = 15541508 := by
        calc
          (17 : ZMod 35982721) ^ 137 = (17 : ZMod 35982721) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 68 * (17 : ZMod 35982721) ^ 68) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 15541508 := by rw [fermat_6]; decide
      have fermat_8 : (17 : ZMod 35982721) ^ 274 = 30326881 := by
        calc
          (17 : ZMod 35982721) ^ 274 = (17 : ZMod 35982721) ^ (137 + 137) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 137 * (17 : ZMod 35982721) ^ 137 := by rw [pow_add]
          _ = 30326881 := by rw [fermat_7]; decide
      have fermat_9 : (17 : ZMod 35982721) ^ 549 = 24389134 := by
        calc
          (17 : ZMod 35982721) ^ 549 = (17 : ZMod 35982721) ^ (274 + 274 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 274 * (17 : ZMod 35982721) ^ 274) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 24389134 := by rw [fermat_8]; decide
      have fermat_10 : (17 : ZMod 35982721) ^ 1098 = 177050 := by
        calc
          (17 : ZMod 35982721) ^ 1098 = (17 : ZMod 35982721) ^ (549 + 549) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 549 * (17 : ZMod 35982721) ^ 549 := by rw [pow_add]
          _ = 177050 := by rw [fermat_9]; decide
      have fermat_11 : (17 : ZMod 35982721) ^ 2196 = 5752509 := by
        calc
          (17 : ZMod 35982721) ^ 2196 = (17 : ZMod 35982721) ^ (1098 + 1098) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1098 * (17 : ZMod 35982721) ^ 1098 := by rw [pow_add]
          _ = 5752509 := by rw [fermat_10]; decide
      have fermat_12 : (17 : ZMod 35982721) ^ 4392 = 30341036 := by
        calc
          (17 : ZMod 35982721) ^ 4392 = (17 : ZMod 35982721) ^ (2196 + 2196) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 2196 * (17 : ZMod 35982721) ^ 2196 := by rw [pow_add]
          _ = 30341036 := by rw [fermat_11]; decide
      have fermat_13 : (17 : ZMod 35982721) ^ 8784 = 21813233 := by
        calc
          (17 : ZMod 35982721) ^ 8784 = (17 : ZMod 35982721) ^ (4392 + 4392) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 4392 * (17 : ZMod 35982721) ^ 4392 := by rw [pow_add]
          _ = 21813233 := by rw [fermat_12]; decide
      have fermat_14 : (17 : ZMod 35982721) ^ 17569 = 27976472 := by
        calc
          (17 : ZMod 35982721) ^ 17569 = (17 : ZMod 35982721) ^ (8784 + 8784 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 8784 * (17 : ZMod 35982721) ^ 8784) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 27976472 := by rw [fermat_13]; decide
      have fermat_15 : (17 : ZMod 35982721) ^ 35139 = 28913227 := by
        calc
          (17 : ZMod 35982721) ^ 35139 = (17 : ZMod 35982721) ^ (17569 + 17569 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 17569 * (17 : ZMod 35982721) ^ 17569) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 28913227 := by rw [fermat_14]; decide
      have fermat_16 : (17 : ZMod 35982721) ^ 70278 = 12858459 := by
        calc
          (17 : ZMod 35982721) ^ 70278 = (17 : ZMod 35982721) ^ (35139 + 35139) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 35139 * (17 : ZMod 35982721) ^ 35139 := by rw [pow_add]
          _ = 12858459 := by rw [fermat_15]; decide
      have fermat_17 : (17 : ZMod 35982721) ^ 140557 = 33413598 := by
        calc
          (17 : ZMod 35982721) ^ 140557 = (17 : ZMod 35982721) ^ (70278 + 70278 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 70278 * (17 : ZMod 35982721) ^ 70278) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 33413598 := by rw [fermat_16]; decide
      have fermat_18 : (17 : ZMod 35982721) ^ 281115 = 34750285 := by
        calc
          (17 : ZMod 35982721) ^ 281115 = (17 : ZMod 35982721) ^ (140557 + 140557 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 140557 * (17 : ZMod 35982721) ^ 140557) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 34750285 := by rw [fermat_17]; decide
      have fermat_19 : (17 : ZMod 35982721) ^ 562230 = 31857965 := by
        calc
          (17 : ZMod 35982721) ^ 562230 = (17 : ZMod 35982721) ^ (281115 + 281115) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 281115 * (17 : ZMod 35982721) ^ 281115 := by rw [pow_add]
          _ = 31857965 := by rw [fermat_18]; decide
      have fermat_20 : (17 : ZMod 35982721) ^ 1124460 = 10037269 := by
        calc
          (17 : ZMod 35982721) ^ 1124460 = (17 : ZMod 35982721) ^ (562230 + 562230) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 562230 * (17 : ZMod 35982721) ^ 562230 := by rw [pow_add]
          _ = 10037269 := by rw [fermat_19]; decide
      have fermat_21 : (17 : ZMod 35982721) ^ 2248920 = 7845696 := by
        calc
          (17 : ZMod 35982721) ^ 2248920 = (17 : ZMod 35982721) ^ (1124460 + 1124460) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1124460 * (17 : ZMod 35982721) ^ 1124460 := by rw [pow_add]
          _ = 7845696 := by rw [fermat_20]; decide
      have fermat_22 : (17 : ZMod 35982721) ^ 4497840 = 24564136 := by
        calc
          (17 : ZMod 35982721) ^ 4497840 = (17 : ZMod 35982721) ^ (2248920 + 2248920) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 2248920 * (17 : ZMod 35982721) ^ 2248920 := by rw [pow_add]
          _ = 24564136 := by rw [fermat_21]; decide
      have fermat_23 : (17 : ZMod 35982721) ^ 8995680 = 10187026 := by
        calc
          (17 : ZMod 35982721) ^ 8995680 = (17 : ZMod 35982721) ^ (4497840 + 4497840) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 4497840 * (17 : ZMod 35982721) ^ 4497840 := by rw [pow_add]
          _ = 10187026 := by rw [fermat_22]; decide
      have fermat_24 : (17 : ZMod 35982721) ^ 17991360 = 35982720 := by
        calc
          (17 : ZMod 35982721) ^ 17991360 = (17 : ZMod 35982721) ^ (8995680 + 8995680) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 8995680 * (17 : ZMod 35982721) ^ 8995680 := by rw [pow_add]
          _ = 35982720 := by rw [fermat_23]; decide
      have fermat_25 : (17 : ZMod 35982721) ^ 35982720 = 1 := by
        calc
          (17 : ZMod 35982721) ^ 35982720 = (17 : ZMod 35982721) ^ (17991360 + 17991360) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 17991360 * (17 : ZMod 35982721) ^ 17991360 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 1), (6247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 1), (6247, 1)] : List FactorBlock).map factorBlockValue).prod = 35982721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (17 : ZMod 35982721) ^ 1 = 17 := by norm_num
      have factor_0_1 : (17 : ZMod 35982721) ^ 2 = 289 := by
        calc
          (17 : ZMod 35982721) ^ 2 = (17 : ZMod 35982721) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1 * (17 : ZMod 35982721) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_0_0]; decide
      have factor_0_2 : (17 : ZMod 35982721) ^ 4 = 83521 := by
        calc
          (17 : ZMod 35982721) ^ 4 = (17 : ZMod 35982721) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 2 * (17 : ZMod 35982721) ^ 2 := by rw [pow_add]
          _ = 83521 := by rw [factor_0_1]; decide
      have factor_0_3 : (17 : ZMod 35982721) ^ 8 = 31092288 := by
        calc
          (17 : ZMod 35982721) ^ 8 = (17 : ZMod 35982721) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 4 * (17 : ZMod 35982721) ^ 4 := by rw [pow_add]
          _ = 31092288 := by rw [factor_0_2]; decide
      have factor_0_4 : (17 : ZMod 35982721) ^ 17 = 5473505 := by
        calc
          (17 : ZMod 35982721) ^ 17 = (17 : ZMod 35982721) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 8 * (17 : ZMod 35982721) ^ 8) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 5473505 := by rw [factor_0_3]; decide
      have factor_0_5 : (17 : ZMod 35982721) ^ 34 = 7497704 := by
        calc
          (17 : ZMod 35982721) ^ 34 = (17 : ZMod 35982721) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 17 * (17 : ZMod 35982721) ^ 17 := by rw [pow_add]
          _ = 7497704 := by rw [factor_0_4]; decide
      have factor_0_6 : (17 : ZMod 35982721) ^ 68 = 12132363 := by
        calc
          (17 : ZMod 35982721) ^ 68 = (17 : ZMod 35982721) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 34 * (17 : ZMod 35982721) ^ 34 := by rw [pow_add]
          _ = 12132363 := by rw [factor_0_5]; decide
      have factor_0_7 : (17 : ZMod 35982721) ^ 137 = 15541508 := by
        calc
          (17 : ZMod 35982721) ^ 137 = (17 : ZMod 35982721) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 68 * (17 : ZMod 35982721) ^ 68) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 15541508 := by rw [factor_0_6]; decide
      have factor_0_8 : (17 : ZMod 35982721) ^ 274 = 30326881 := by
        calc
          (17 : ZMod 35982721) ^ 274 = (17 : ZMod 35982721) ^ (137 + 137) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 137 * (17 : ZMod 35982721) ^ 137 := by rw [pow_add]
          _ = 30326881 := by rw [factor_0_7]; decide
      have factor_0_9 : (17 : ZMod 35982721) ^ 549 = 24389134 := by
        calc
          (17 : ZMod 35982721) ^ 549 = (17 : ZMod 35982721) ^ (274 + 274 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 274 * (17 : ZMod 35982721) ^ 274) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 24389134 := by rw [factor_0_8]; decide
      have factor_0_10 : (17 : ZMod 35982721) ^ 1098 = 177050 := by
        calc
          (17 : ZMod 35982721) ^ 1098 = (17 : ZMod 35982721) ^ (549 + 549) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 549 * (17 : ZMod 35982721) ^ 549 := by rw [pow_add]
          _ = 177050 := by rw [factor_0_9]; decide
      have factor_0_11 : (17 : ZMod 35982721) ^ 2196 = 5752509 := by
        calc
          (17 : ZMod 35982721) ^ 2196 = (17 : ZMod 35982721) ^ (1098 + 1098) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1098 * (17 : ZMod 35982721) ^ 1098 := by rw [pow_add]
          _ = 5752509 := by rw [factor_0_10]; decide
      have factor_0_12 : (17 : ZMod 35982721) ^ 4392 = 30341036 := by
        calc
          (17 : ZMod 35982721) ^ 4392 = (17 : ZMod 35982721) ^ (2196 + 2196) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 2196 * (17 : ZMod 35982721) ^ 2196 := by rw [pow_add]
          _ = 30341036 := by rw [factor_0_11]; decide
      have factor_0_13 : (17 : ZMod 35982721) ^ 8784 = 21813233 := by
        calc
          (17 : ZMod 35982721) ^ 8784 = (17 : ZMod 35982721) ^ (4392 + 4392) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 4392 * (17 : ZMod 35982721) ^ 4392 := by rw [pow_add]
          _ = 21813233 := by rw [factor_0_12]; decide
      have factor_0_14 : (17 : ZMod 35982721) ^ 17569 = 27976472 := by
        calc
          (17 : ZMod 35982721) ^ 17569 = (17 : ZMod 35982721) ^ (8784 + 8784 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 8784 * (17 : ZMod 35982721) ^ 8784) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 27976472 := by rw [factor_0_13]; decide
      have factor_0_15 : (17 : ZMod 35982721) ^ 35139 = 28913227 := by
        calc
          (17 : ZMod 35982721) ^ 35139 = (17 : ZMod 35982721) ^ (17569 + 17569 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 17569 * (17 : ZMod 35982721) ^ 17569) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 28913227 := by rw [factor_0_14]; decide
      have factor_0_16 : (17 : ZMod 35982721) ^ 70278 = 12858459 := by
        calc
          (17 : ZMod 35982721) ^ 70278 = (17 : ZMod 35982721) ^ (35139 + 35139) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 35139 * (17 : ZMod 35982721) ^ 35139 := by rw [pow_add]
          _ = 12858459 := by rw [factor_0_15]; decide
      have factor_0_17 : (17 : ZMod 35982721) ^ 140557 = 33413598 := by
        calc
          (17 : ZMod 35982721) ^ 140557 = (17 : ZMod 35982721) ^ (70278 + 70278 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 70278 * (17 : ZMod 35982721) ^ 70278) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 33413598 := by rw [factor_0_16]; decide
      have factor_0_18 : (17 : ZMod 35982721) ^ 281115 = 34750285 := by
        calc
          (17 : ZMod 35982721) ^ 281115 = (17 : ZMod 35982721) ^ (140557 + 140557 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 140557 * (17 : ZMod 35982721) ^ 140557) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 34750285 := by rw [factor_0_17]; decide
      have factor_0_19 : (17 : ZMod 35982721) ^ 562230 = 31857965 := by
        calc
          (17 : ZMod 35982721) ^ 562230 = (17 : ZMod 35982721) ^ (281115 + 281115) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 281115 * (17 : ZMod 35982721) ^ 281115 := by rw [pow_add]
          _ = 31857965 := by rw [factor_0_18]; decide
      have factor_0_20 : (17 : ZMod 35982721) ^ 1124460 = 10037269 := by
        calc
          (17 : ZMod 35982721) ^ 1124460 = (17 : ZMod 35982721) ^ (562230 + 562230) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 562230 * (17 : ZMod 35982721) ^ 562230 := by rw [pow_add]
          _ = 10037269 := by rw [factor_0_19]; decide
      have factor_0_21 : (17 : ZMod 35982721) ^ 2248920 = 7845696 := by
        calc
          (17 : ZMod 35982721) ^ 2248920 = (17 : ZMod 35982721) ^ (1124460 + 1124460) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1124460 * (17 : ZMod 35982721) ^ 1124460 := by rw [pow_add]
          _ = 7845696 := by rw [factor_0_20]; decide
      have factor_0_22 : (17 : ZMod 35982721) ^ 4497840 = 24564136 := by
        calc
          (17 : ZMod 35982721) ^ 4497840 = (17 : ZMod 35982721) ^ (2248920 + 2248920) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 2248920 * (17 : ZMod 35982721) ^ 2248920 := by rw [pow_add]
          _ = 24564136 := by rw [factor_0_21]; decide
      have factor_0_23 : (17 : ZMod 35982721) ^ 8995680 = 10187026 := by
        calc
          (17 : ZMod 35982721) ^ 8995680 = (17 : ZMod 35982721) ^ (4497840 + 4497840) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 4497840 * (17 : ZMod 35982721) ^ 4497840 := by rw [pow_add]
          _ = 10187026 := by rw [factor_0_22]; decide
      have factor_0_24 : (17 : ZMod 35982721) ^ 17991360 = 35982720 := by
        calc
          (17 : ZMod 35982721) ^ 17991360 = (17 : ZMod 35982721) ^ (8995680 + 8995680) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 8995680 * (17 : ZMod 35982721) ^ 8995680 := by rw [pow_add]
          _ = 35982720 := by rw [factor_0_23]; decide
      change (17 : ZMod 35982721) ^ 17991360 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (17 : ZMod 35982721) ^ 1 = 17 := by norm_num
      have factor_1_1 : (17 : ZMod 35982721) ^ 2 = 289 := by
        calc
          (17 : ZMod 35982721) ^ 2 = (17 : ZMod 35982721) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1 * (17 : ZMod 35982721) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_1_0]; decide
      have factor_1_2 : (17 : ZMod 35982721) ^ 5 = 1419857 := by
        calc
          (17 : ZMod 35982721) ^ 5 = (17 : ZMod 35982721) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 2 * (17 : ZMod 35982721) ^ 2) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 1419857 := by rw [factor_1_1]; decide
      have factor_1_3 : (17 : ZMod 35982721) ^ 11 = 9760299 := by
        calc
          (17 : ZMod 35982721) ^ 11 = (17 : ZMod 35982721) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 5 * (17 : ZMod 35982721) ^ 5) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 9760299 := by rw [factor_1_2]; decide
      have factor_1_4 : (17 : ZMod 35982721) ^ 22 = 10324484 := by
        calc
          (17 : ZMod 35982721) ^ 22 = (17 : ZMod 35982721) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 11 * (17 : ZMod 35982721) ^ 11 := by rw [pow_add]
          _ = 10324484 := by rw [factor_1_3]; decide
      have factor_1_5 : (17 : ZMod 35982721) ^ 45 = 10002467 := by
        calc
          (17 : ZMod 35982721) ^ 45 = (17 : ZMod 35982721) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 22 * (17 : ZMod 35982721) ^ 22) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 10002467 := by rw [factor_1_4]; decide
      have factor_1_6 : (17 : ZMod 35982721) ^ 91 = 34881382 := by
        calc
          (17 : ZMod 35982721) ^ 91 = (17 : ZMod 35982721) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 45 * (17 : ZMod 35982721) ^ 45) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 34881382 := by rw [factor_1_5]; decide
      have factor_1_7 : (17 : ZMod 35982721) ^ 183 = 30897002 := by
        calc
          (17 : ZMod 35982721) ^ 183 = (17 : ZMod 35982721) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 91 * (17 : ZMod 35982721) ^ 91) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 30897002 := by rw [factor_1_6]; decide
      have factor_1_8 : (17 : ZMod 35982721) ^ 366 = 13961277 := by
        calc
          (17 : ZMod 35982721) ^ 366 = (17 : ZMod 35982721) ^ (183 + 183) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 183 * (17 : ZMod 35982721) ^ 183 := by rw [pow_add]
          _ = 13961277 := by rw [factor_1_7]; decide
      have factor_1_9 : (17 : ZMod 35982721) ^ 732 = 7260801 := by
        calc
          (17 : ZMod 35982721) ^ 732 = (17 : ZMod 35982721) ^ (366 + 366) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 366 * (17 : ZMod 35982721) ^ 366 := by rw [pow_add]
          _ = 7260801 := by rw [factor_1_8]; decide
      have factor_1_10 : (17 : ZMod 35982721) ^ 1464 = 11073755 := by
        calc
          (17 : ZMod 35982721) ^ 1464 = (17 : ZMod 35982721) ^ (732 + 732) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 732 * (17 : ZMod 35982721) ^ 732 := by rw [pow_add]
          _ = 11073755 := by rw [factor_1_9]; decide
      have factor_1_11 : (17 : ZMod 35982721) ^ 2928 = 16113655 := by
        calc
          (17 : ZMod 35982721) ^ 2928 = (17 : ZMod 35982721) ^ (1464 + 1464) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1464 * (17 : ZMod 35982721) ^ 1464 := by rw [pow_add]
          _ = 16113655 := by rw [factor_1_10]; decide
      have factor_1_12 : (17 : ZMod 35982721) ^ 5856 = 2031865 := by
        calc
          (17 : ZMod 35982721) ^ 5856 = (17 : ZMod 35982721) ^ (2928 + 2928) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 2928 * (17 : ZMod 35982721) ^ 2928 := by rw [pow_add]
          _ = 2031865 := by rw [factor_1_11]; decide
      have factor_1_13 : (17 : ZMod 35982721) ^ 11713 = 15651 := by
        calc
          (17 : ZMod 35982721) ^ 11713 = (17 : ZMod 35982721) ^ (5856 + 5856 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 5856 * (17 : ZMod 35982721) ^ 5856) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 15651 := by rw [factor_1_12]; decide
      have factor_1_14 : (17 : ZMod 35982721) ^ 23426 = 29057475 := by
        calc
          (17 : ZMod 35982721) ^ 23426 = (17 : ZMod 35982721) ^ (11713 + 11713) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 11713 * (17 : ZMod 35982721) ^ 11713 := by rw [pow_add]
          _ = 29057475 := by rw [factor_1_13]; decide
      have factor_1_15 : (17 : ZMod 35982721) ^ 46852 = 2216481 := by
        calc
          (17 : ZMod 35982721) ^ 46852 = (17 : ZMod 35982721) ^ (23426 + 23426) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 23426 * (17 : ZMod 35982721) ^ 23426 := by rw [pow_add]
          _ = 2216481 := by rw [factor_1_14]; decide
      have factor_1_16 : (17 : ZMod 35982721) ^ 93705 = 25664576 := by
        calc
          (17 : ZMod 35982721) ^ 93705 = (17 : ZMod 35982721) ^ (46852 + 46852 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 46852 * (17 : ZMod 35982721) ^ 46852) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 25664576 := by rw [factor_1_15]; decide
      have factor_1_17 : (17 : ZMod 35982721) ^ 187410 = 24585949 := by
        calc
          (17 : ZMod 35982721) ^ 187410 = (17 : ZMod 35982721) ^ (93705 + 93705) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 93705 * (17 : ZMod 35982721) ^ 93705 := by rw [pow_add]
          _ = 24585949 := by rw [factor_1_16]; decide
      have factor_1_18 : (17 : ZMod 35982721) ^ 374820 = 15818936 := by
        calc
          (17 : ZMod 35982721) ^ 374820 = (17 : ZMod 35982721) ^ (187410 + 187410) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 187410 * (17 : ZMod 35982721) ^ 187410 := by rw [pow_add]
          _ = 15818936 := by rw [factor_1_17]; decide
      have factor_1_19 : (17 : ZMod 35982721) ^ 749640 = 33474323 := by
        calc
          (17 : ZMod 35982721) ^ 749640 = (17 : ZMod 35982721) ^ (374820 + 374820) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 374820 * (17 : ZMod 35982721) ^ 374820 := by rw [pow_add]
          _ = 33474323 := by rw [factor_1_18]; decide
      have factor_1_20 : (17 : ZMod 35982721) ^ 1499280 = 13984181 := by
        calc
          (17 : ZMod 35982721) ^ 1499280 = (17 : ZMod 35982721) ^ (749640 + 749640) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 749640 * (17 : ZMod 35982721) ^ 749640 := by rw [pow_add]
          _ = 13984181 := by rw [factor_1_19]; decide
      have factor_1_21 : (17 : ZMod 35982721) ^ 2998560 = 9389685 := by
        calc
          (17 : ZMod 35982721) ^ 2998560 = (17 : ZMod 35982721) ^ (1499280 + 1499280) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1499280 * (17 : ZMod 35982721) ^ 1499280 := by rw [pow_add]
          _ = 9389685 := by rw [factor_1_20]; decide
      have factor_1_22 : (17 : ZMod 35982721) ^ 5997120 = 26027069 := by
        calc
          (17 : ZMod 35982721) ^ 5997120 = (17 : ZMod 35982721) ^ (2998560 + 2998560) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 2998560 * (17 : ZMod 35982721) ^ 2998560 := by rw [pow_add]
          _ = 26027069 := by rw [factor_1_21]; decide
      have factor_1_23 : (17 : ZMod 35982721) ^ 11994240 = 26027068 := by
        calc
          (17 : ZMod 35982721) ^ 11994240 = (17 : ZMod 35982721) ^ (5997120 + 5997120) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 5997120 * (17 : ZMod 35982721) ^ 5997120 := by rw [pow_add]
          _ = 26027068 := by rw [factor_1_22]; decide
      change (17 : ZMod 35982721) ^ 11994240 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (17 : ZMod 35982721) ^ 1 = 17 := by norm_num
      have factor_2_1 : (17 : ZMod 35982721) ^ 3 = 4913 := by
        calc
          (17 : ZMod 35982721) ^ 3 = (17 : ZMod 35982721) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 1 * (17 : ZMod 35982721) ^ 1) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 4913 := by rw [factor_2_0]; decide
      have factor_2_2 : (17 : ZMod 35982721) ^ 6 = 24137569 := by
        calc
          (17 : ZMod 35982721) ^ 6 = (17 : ZMod 35982721) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 3 * (17 : ZMod 35982721) ^ 3 := by rw [pow_add]
          _ = 24137569 := by rw [factor_2_1]; decide
      have factor_2_3 : (17 : ZMod 35982721) ^ 13 = 14074173 := by
        calc
          (17 : ZMod 35982721) ^ 13 = (17 : ZMod 35982721) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 6 * (17 : ZMod 35982721) ^ 6) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 14074173 := by rw [factor_2_2]; decide
      have factor_2_4 : (17 : ZMod 35982721) ^ 27 = 2308830 := by
        calc
          (17 : ZMod 35982721) ^ 27 = (17 : ZMod 35982721) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 13 * (17 : ZMod 35982721) ^ 13) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 2308830 := by rw [factor_2_3]; decide
      have factor_2_5 : (17 : ZMod 35982721) ^ 54 = 35766355 := by
        calc
          (17 : ZMod 35982721) ^ 54 = (17 : ZMod 35982721) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 27 * (17 : ZMod 35982721) ^ 27 := by rw [pow_add]
          _ = 35766355 := by rw [factor_2_4]; decide
      have factor_2_6 : (17 : ZMod 35982721) ^ 109 = 12340895 := by
        calc
          (17 : ZMod 35982721) ^ 109 = (17 : ZMod 35982721) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 54 * (17 : ZMod 35982721) ^ 54) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 12340895 := by rw [factor_2_5]; decide
      have factor_2_7 : (17 : ZMod 35982721) ^ 219 = 25769177 := by
        calc
          (17 : ZMod 35982721) ^ 219 = (17 : ZMod 35982721) ^ (109 + 109 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 109 * (17 : ZMod 35982721) ^ 109) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 25769177 := by rw [factor_2_6]; decide
      have factor_2_8 : (17 : ZMod 35982721) ^ 439 = 19629897 := by
        calc
          (17 : ZMod 35982721) ^ 439 = (17 : ZMod 35982721) ^ (219 + 219 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 219 * (17 : ZMod 35982721) ^ 219) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 19629897 := by rw [factor_2_7]; decide
      have factor_2_9 : (17 : ZMod 35982721) ^ 878 = 14104179 := by
        calc
          (17 : ZMod 35982721) ^ 878 = (17 : ZMod 35982721) ^ (439 + 439) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 439 * (17 : ZMod 35982721) ^ 439 := by rw [pow_add]
          _ = 14104179 := by rw [factor_2_8]; decide
      have factor_2_10 : (17 : ZMod 35982721) ^ 1756 = 18954174 := by
        calc
          (17 : ZMod 35982721) ^ 1756 = (17 : ZMod 35982721) ^ (878 + 878) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 878 * (17 : ZMod 35982721) ^ 878 := by rw [pow_add]
          _ = 18954174 := by rw [factor_2_9]; decide
      have factor_2_11 : (17 : ZMod 35982721) ^ 3513 = 21792574 := by
        calc
          (17 : ZMod 35982721) ^ 3513 = (17 : ZMod 35982721) ^ (1756 + 1756 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 1756 * (17 : ZMod 35982721) ^ 1756) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 21792574 := by rw [factor_2_10]; decide
      have factor_2_12 : (17 : ZMod 35982721) ^ 7027 = 35677298 := by
        calc
          (17 : ZMod 35982721) ^ 7027 = (17 : ZMod 35982721) ^ (3513 + 3513 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 3513 * (17 : ZMod 35982721) ^ 3513) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 35677298 := by rw [factor_2_11]; decide
      have factor_2_13 : (17 : ZMod 35982721) ^ 14055 = 20054602 := by
        calc
          (17 : ZMod 35982721) ^ 14055 = (17 : ZMod 35982721) ^ (7027 + 7027 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 7027 * (17 : ZMod 35982721) ^ 7027) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 20054602 := by rw [factor_2_12]; decide
      have factor_2_14 : (17 : ZMod 35982721) ^ 28111 = 27779040 := by
        calc
          (17 : ZMod 35982721) ^ 28111 = (17 : ZMod 35982721) ^ (14055 + 14055 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 14055 * (17 : ZMod 35982721) ^ 14055) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 27779040 := by rw [factor_2_13]; decide
      have factor_2_15 : (17 : ZMod 35982721) ^ 56223 = 4178100 := by
        calc
          (17 : ZMod 35982721) ^ 56223 = (17 : ZMod 35982721) ^ (28111 + 28111 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 28111 * (17 : ZMod 35982721) ^ 28111) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 4178100 := by rw [factor_2_14]; decide
      have factor_2_16 : (17 : ZMod 35982721) ^ 112446 = 6274944 := by
        calc
          (17 : ZMod 35982721) ^ 112446 = (17 : ZMod 35982721) ^ (56223 + 56223) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 56223 * (17 : ZMod 35982721) ^ 56223 := by rw [pow_add]
          _ = 6274944 := by rw [factor_2_15]; decide
      have factor_2_17 : (17 : ZMod 35982721) ^ 224892 = 2146303 := by
        calc
          (17 : ZMod 35982721) ^ 224892 = (17 : ZMod 35982721) ^ (112446 + 112446) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 112446 * (17 : ZMod 35982721) ^ 112446 := by rw [pow_add]
          _ = 2146303 := by rw [factor_2_16]; decide
      have factor_2_18 : (17 : ZMod 35982721) ^ 449784 = 677226 := by
        calc
          (17 : ZMod 35982721) ^ 449784 = (17 : ZMod 35982721) ^ (224892 + 224892) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 224892 * (17 : ZMod 35982721) ^ 224892 := by rw [pow_add]
          _ = 677226 := by rw [factor_2_17]; decide
      have factor_2_19 : (17 : ZMod 35982721) ^ 899568 = 35275931 := by
        calc
          (17 : ZMod 35982721) ^ 899568 = (17 : ZMod 35982721) ^ (449784 + 449784) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 449784 * (17 : ZMod 35982721) ^ 449784 := by rw [pow_add]
          _ = 35275931 := by rw [factor_2_18]; decide
      have factor_2_20 : (17 : ZMod 35982721) ^ 1799136 = 3988457 := by
        calc
          (17 : ZMod 35982721) ^ 1799136 = (17 : ZMod 35982721) ^ (899568 + 899568) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 899568 * (17 : ZMod 35982721) ^ 899568 := by rw [pow_add]
          _ = 3988457 := by rw [factor_2_19]; decide
      have factor_2_21 : (17 : ZMod 35982721) ^ 3598272 = 8200354 := by
        calc
          (17 : ZMod 35982721) ^ 3598272 = (17 : ZMod 35982721) ^ (1799136 + 1799136) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1799136 * (17 : ZMod 35982721) ^ 1799136 := by rw [pow_add]
          _ = 8200354 := by rw [factor_2_20]; decide
      have factor_2_22 : (17 : ZMod 35982721) ^ 7196544 = 1342560 := by
        calc
          (17 : ZMod 35982721) ^ 7196544 = (17 : ZMod 35982721) ^ (3598272 + 3598272) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 3598272 * (17 : ZMod 35982721) ^ 3598272 := by rw [pow_add]
          _ = 1342560 := by rw [factor_2_21]; decide
      change (17 : ZMod 35982721) ^ 7196544 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (17 : ZMod 35982721) ^ 1 = 17 := by norm_num
      have factor_3_1 : (17 : ZMod 35982721) ^ 2 = 289 := by
        calc
          (17 : ZMod 35982721) ^ 2 = (17 : ZMod 35982721) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1 * (17 : ZMod 35982721) ^ 1 := by rw [pow_add]
          _ = 289 := by rw [factor_3_0]; decide
      have factor_3_2 : (17 : ZMod 35982721) ^ 5 = 1419857 := by
        calc
          (17 : ZMod 35982721) ^ 5 = (17 : ZMod 35982721) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 2 * (17 : ZMod 35982721) ^ 2) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 1419857 := by rw [factor_3_1]; decide
      have factor_3_3 : (17 : ZMod 35982721) ^ 11 = 9760299 := by
        calc
          (17 : ZMod 35982721) ^ 11 = (17 : ZMod 35982721) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 5 * (17 : ZMod 35982721) ^ 5) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 9760299 := by rw [factor_3_2]; decide
      have factor_3_4 : (17 : ZMod 35982721) ^ 22 = 10324484 := by
        calc
          (17 : ZMod 35982721) ^ 22 = (17 : ZMod 35982721) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 11 * (17 : ZMod 35982721) ^ 11 := by rw [pow_add]
          _ = 10324484 := by rw [factor_3_3]; decide
      have factor_3_5 : (17 : ZMod 35982721) ^ 45 = 10002467 := by
        calc
          (17 : ZMod 35982721) ^ 45 = (17 : ZMod 35982721) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = ((17 : ZMod 35982721) ^ 22 * (17 : ZMod 35982721) ^ 22) * (17 : ZMod 35982721) := by rw [pow_succ, pow_add]
          _ = 10002467 := by rw [factor_3_4]; decide
      have factor_3_6 : (17 : ZMod 35982721) ^ 90 = 2051846 := by
        calc
          (17 : ZMod 35982721) ^ 90 = (17 : ZMod 35982721) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 45 * (17 : ZMod 35982721) ^ 45 := by rw [pow_add]
          _ = 2051846 := by rw [factor_3_5]; decide
      have factor_3_7 : (17 : ZMod 35982721) ^ 180 = 21685274 := by
        calc
          (17 : ZMod 35982721) ^ 180 = (17 : ZMod 35982721) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 90 * (17 : ZMod 35982721) ^ 90 := by rw [pow_add]
          _ = 21685274 := by rw [factor_3_6]; decide
      have factor_3_8 : (17 : ZMod 35982721) ^ 360 = 16302113 := by
        calc
          (17 : ZMod 35982721) ^ 360 = (17 : ZMod 35982721) ^ (180 + 180) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 180 * (17 : ZMod 35982721) ^ 180 := by rw [pow_add]
          _ = 16302113 := by rw [factor_3_7]; decide
      have factor_3_9 : (17 : ZMod 35982721) ^ 720 = 10397113 := by
        calc
          (17 : ZMod 35982721) ^ 720 = (17 : ZMod 35982721) ^ (360 + 360) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 360 * (17 : ZMod 35982721) ^ 360 := by rw [pow_add]
          _ = 10397113 := by rw [factor_3_8]; decide
      have factor_3_10 : (17 : ZMod 35982721) ^ 1440 = 20617591 := by
        calc
          (17 : ZMod 35982721) ^ 1440 = (17 : ZMod 35982721) ^ (720 + 720) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 720 * (17 : ZMod 35982721) ^ 720 := by rw [pow_add]
          _ = 20617591 := by rw [factor_3_9]; decide
      have factor_3_11 : (17 : ZMod 35982721) ^ 2880 = 17630333 := by
        calc
          (17 : ZMod 35982721) ^ 2880 = (17 : ZMod 35982721) ^ (1440 + 1440) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 1440 * (17 : ZMod 35982721) ^ 1440 := by rw [pow_add]
          _ = 17630333 := by rw [factor_3_10]; decide
      have factor_3_12 : (17 : ZMod 35982721) ^ 5760 = 2444614 := by
        calc
          (17 : ZMod 35982721) ^ 5760 = (17 : ZMod 35982721) ^ (2880 + 2880) :=
            congrArg (fun n : ℕ => (17 : ZMod 35982721) ^ n) (by norm_num)
          _ = (17 : ZMod 35982721) ^ 2880 * (17 : ZMod 35982721) ^ 2880 := by rw [pow_add]
          _ = 2444614 := by rw [factor_3_11]; decide
      change (17 : ZMod 35982721) ^ 5760 ≠ 1
      rw [factor_3_12]
      decide

#print axioms prime_lucas_35982721

end TotientTailPeriodKiller
end Erdos249257
