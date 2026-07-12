import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_34581109 : Nat.Prime 34581109 := by
  apply lucas_primality 34581109 (6 : ZMod 34581109)
  ·
      have fermat_0 : (6 : ZMod 34581109) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 34581109) ^ 2 = 36 := by
        calc
          (6 : ZMod 34581109) ^ 2 = (6 : ZMod 34581109) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 1 * (6 : ZMod 34581109) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 34581109) ^ 4 = 1296 := by
        calc
          (6 : ZMod 34581109) ^ 4 = (6 : ZMod 34581109) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 2 * (6 : ZMod 34581109) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 34581109) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 34581109) ^ 8 = (6 : ZMod 34581109) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 4 * (6 : ZMod 34581109) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 34581109) ^ 16 = 17616345 := by
        calc
          (6 : ZMod 34581109) ^ 16 = (6 : ZMod 34581109) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 8 * (6 : ZMod 34581109) ^ 8 := by rw [pow_add]
          _ = 17616345 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 34581109) ^ 32 = 1381092 := by
        calc
          (6 : ZMod 34581109) ^ 32 = (6 : ZMod 34581109) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 16 * (6 : ZMod 34581109) ^ 16 := by rw [pow_add]
          _ = 1381092 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 34581109) ^ 65 = 10975670 := by
        calc
          (6 : ZMod 34581109) ^ 65 = (6 : ZMod 34581109) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 32 * (6 : ZMod 34581109) ^ 32) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 10975670 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 34581109) ^ 131 = 25352923 := by
        calc
          (6 : ZMod 34581109) ^ 131 = (6 : ZMod 34581109) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 65 * (6 : ZMod 34581109) ^ 65) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 25352923 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 34581109) ^ 263 = 5287612 := by
        calc
          (6 : ZMod 34581109) ^ 263 = (6 : ZMod 34581109) ^ (131 + 131 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 131 * (6 : ZMod 34581109) ^ 131) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 5287612 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 34581109) ^ 527 = 15054046 := by
        calc
          (6 : ZMod 34581109) ^ 527 = (6 : ZMod 34581109) ^ (263 + 263 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 263 * (6 : ZMod 34581109) ^ 263) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 15054046 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 34581109) ^ 1055 = 1008376 := by
        calc
          (6 : ZMod 34581109) ^ 1055 = (6 : ZMod 34581109) ^ (527 + 527 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 527 * (6 : ZMod 34581109) ^ 527) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 1008376 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 34581109) ^ 2110 = 33809449 := by
        calc
          (6 : ZMod 34581109) ^ 2110 = (6 : ZMod 34581109) ^ (1055 + 1055) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 1055 * (6 : ZMod 34581109) ^ 1055 := by rw [pow_add]
          _ = 33809449 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 34581109) ^ 4221 = 7657265 := by
        calc
          (6 : ZMod 34581109) ^ 4221 = (6 : ZMod 34581109) ^ (2110 + 2110 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 2110 * (6 : ZMod 34581109) ^ 2110) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 7657265 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 34581109) ^ 8442 = 19145256 := by
        calc
          (6 : ZMod 34581109) ^ 8442 = (6 : ZMod 34581109) ^ (4221 + 4221) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 4221 * (6 : ZMod 34581109) ^ 4221 := by rw [pow_add]
          _ = 19145256 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 34581109) ^ 16885 = 30376281 := by
        calc
          (6 : ZMod 34581109) ^ 16885 = (6 : ZMod 34581109) ^ (8442 + 8442 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 8442 * (6 : ZMod 34581109) ^ 8442) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 30376281 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 34581109) ^ 33770 = 18262282 := by
        calc
          (6 : ZMod 34581109) ^ 33770 = (6 : ZMod 34581109) ^ (16885 + 16885) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 16885 * (6 : ZMod 34581109) ^ 16885 := by rw [pow_add]
          _ = 18262282 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 34581109) ^ 67541 = 16465295 := by
        calc
          (6 : ZMod 34581109) ^ 67541 = (6 : ZMod 34581109) ^ (33770 + 33770 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 33770 * (6 : ZMod 34581109) ^ 33770) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 16465295 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 34581109) ^ 135082 = 4236417 := by
        calc
          (6 : ZMod 34581109) ^ 135082 = (6 : ZMod 34581109) ^ (67541 + 67541) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 67541 * (6 : ZMod 34581109) ^ 67541 := by rw [pow_add]
          _ = 4236417 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 34581109) ^ 270164 = 13819088 := by
        calc
          (6 : ZMod 34581109) ^ 270164 = (6 : ZMod 34581109) ^ (135082 + 135082) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 135082 * (6 : ZMod 34581109) ^ 135082 := by rw [pow_add]
          _ = 13819088 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 34581109) ^ 540329 = 24499572 := by
        calc
          (6 : ZMod 34581109) ^ 540329 = (6 : ZMod 34581109) ^ (270164 + 270164 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 270164 * (6 : ZMod 34581109) ^ 270164) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 24499572 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 34581109) ^ 1080659 = 28273942 := by
        calc
          (6 : ZMod 34581109) ^ 1080659 = (6 : ZMod 34581109) ^ (540329 + 540329 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 540329 * (6 : ZMod 34581109) ^ 540329) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 28273942 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 34581109) ^ 2161319 = 33871979 := by
        calc
          (6 : ZMod 34581109) ^ 2161319 = (6 : ZMod 34581109) ^ (1080659 + 1080659 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 1080659 * (6 : ZMod 34581109) ^ 1080659) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 33871979 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 34581109) ^ 4322638 = 21450931 := by
        calc
          (6 : ZMod 34581109) ^ 4322638 = (6 : ZMod 34581109) ^ (2161319 + 2161319) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 2161319 * (6 : ZMod 34581109) ^ 2161319 := by rw [pow_add]
          _ = 21450931 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 34581109) ^ 8645277 = 17203282 := by
        calc
          (6 : ZMod 34581109) ^ 8645277 = (6 : ZMod 34581109) ^ (4322638 + 4322638 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 4322638 * (6 : ZMod 34581109) ^ 4322638) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 17203282 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 34581109) ^ 17290554 = 34581108 := by
        calc
          (6 : ZMod 34581109) ^ 17290554 = (6 : ZMod 34581109) ^ (8645277 + 8645277) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 8645277 * (6 : ZMod 34581109) ^ 8645277 := by rw [pow_add]
          _ = 34581108 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 34581109) ^ 34581108 = 1 := by
        calc
          (6 : ZMod 34581109) ^ 34581108 = (6 : ZMod 34581109) ^ (17290554 + 17290554) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 17290554 * (6 : ZMod 34581109) ^ 17290554 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (29, 1), (99371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (29, 1), (99371, 1)] : List FactorBlock).map factorBlockValue).prod = 34581109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 34581109) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 34581109) ^ 2 = 36 := by
        calc
          (6 : ZMod 34581109) ^ 2 = (6 : ZMod 34581109) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 1 * (6 : ZMod 34581109) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 34581109) ^ 4 = 1296 := by
        calc
          (6 : ZMod 34581109) ^ 4 = (6 : ZMod 34581109) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 2 * (6 : ZMod 34581109) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 34581109) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 34581109) ^ 8 = (6 : ZMod 34581109) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 4 * (6 : ZMod 34581109) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 34581109) ^ 16 = 17616345 := by
        calc
          (6 : ZMod 34581109) ^ 16 = (6 : ZMod 34581109) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 8 * (6 : ZMod 34581109) ^ 8 := by rw [pow_add]
          _ = 17616345 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 34581109) ^ 32 = 1381092 := by
        calc
          (6 : ZMod 34581109) ^ 32 = (6 : ZMod 34581109) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 16 * (6 : ZMod 34581109) ^ 16 := by rw [pow_add]
          _ = 1381092 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 34581109) ^ 65 = 10975670 := by
        calc
          (6 : ZMod 34581109) ^ 65 = (6 : ZMod 34581109) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 32 * (6 : ZMod 34581109) ^ 32) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 10975670 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 34581109) ^ 131 = 25352923 := by
        calc
          (6 : ZMod 34581109) ^ 131 = (6 : ZMod 34581109) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 65 * (6 : ZMod 34581109) ^ 65) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 25352923 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 34581109) ^ 263 = 5287612 := by
        calc
          (6 : ZMod 34581109) ^ 263 = (6 : ZMod 34581109) ^ (131 + 131 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 131 * (6 : ZMod 34581109) ^ 131) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 5287612 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 34581109) ^ 527 = 15054046 := by
        calc
          (6 : ZMod 34581109) ^ 527 = (6 : ZMod 34581109) ^ (263 + 263 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 263 * (6 : ZMod 34581109) ^ 263) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 15054046 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 34581109) ^ 1055 = 1008376 := by
        calc
          (6 : ZMod 34581109) ^ 1055 = (6 : ZMod 34581109) ^ (527 + 527 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 527 * (6 : ZMod 34581109) ^ 527) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 1008376 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 34581109) ^ 2110 = 33809449 := by
        calc
          (6 : ZMod 34581109) ^ 2110 = (6 : ZMod 34581109) ^ (1055 + 1055) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 1055 * (6 : ZMod 34581109) ^ 1055 := by rw [pow_add]
          _ = 33809449 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 34581109) ^ 4221 = 7657265 := by
        calc
          (6 : ZMod 34581109) ^ 4221 = (6 : ZMod 34581109) ^ (2110 + 2110 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 2110 * (6 : ZMod 34581109) ^ 2110) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 7657265 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 34581109) ^ 8442 = 19145256 := by
        calc
          (6 : ZMod 34581109) ^ 8442 = (6 : ZMod 34581109) ^ (4221 + 4221) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 4221 * (6 : ZMod 34581109) ^ 4221 := by rw [pow_add]
          _ = 19145256 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 34581109) ^ 16885 = 30376281 := by
        calc
          (6 : ZMod 34581109) ^ 16885 = (6 : ZMod 34581109) ^ (8442 + 8442 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 8442 * (6 : ZMod 34581109) ^ 8442) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 30376281 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 34581109) ^ 33770 = 18262282 := by
        calc
          (6 : ZMod 34581109) ^ 33770 = (6 : ZMod 34581109) ^ (16885 + 16885) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 16885 * (6 : ZMod 34581109) ^ 16885 := by rw [pow_add]
          _ = 18262282 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 34581109) ^ 67541 = 16465295 := by
        calc
          (6 : ZMod 34581109) ^ 67541 = (6 : ZMod 34581109) ^ (33770 + 33770 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 33770 * (6 : ZMod 34581109) ^ 33770) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 16465295 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 34581109) ^ 135082 = 4236417 := by
        calc
          (6 : ZMod 34581109) ^ 135082 = (6 : ZMod 34581109) ^ (67541 + 67541) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 67541 * (6 : ZMod 34581109) ^ 67541 := by rw [pow_add]
          _ = 4236417 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 34581109) ^ 270164 = 13819088 := by
        calc
          (6 : ZMod 34581109) ^ 270164 = (6 : ZMod 34581109) ^ (135082 + 135082) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 135082 * (6 : ZMod 34581109) ^ 135082 := by rw [pow_add]
          _ = 13819088 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 34581109) ^ 540329 = 24499572 := by
        calc
          (6 : ZMod 34581109) ^ 540329 = (6 : ZMod 34581109) ^ (270164 + 270164 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 270164 * (6 : ZMod 34581109) ^ 270164) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 24499572 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 34581109) ^ 1080659 = 28273942 := by
        calc
          (6 : ZMod 34581109) ^ 1080659 = (6 : ZMod 34581109) ^ (540329 + 540329 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 540329 * (6 : ZMod 34581109) ^ 540329) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 28273942 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 34581109) ^ 2161319 = 33871979 := by
        calc
          (6 : ZMod 34581109) ^ 2161319 = (6 : ZMod 34581109) ^ (1080659 + 1080659 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 1080659 * (6 : ZMod 34581109) ^ 1080659) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 33871979 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 34581109) ^ 4322638 = 21450931 := by
        calc
          (6 : ZMod 34581109) ^ 4322638 = (6 : ZMod 34581109) ^ (2161319 + 2161319) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 2161319 * (6 : ZMod 34581109) ^ 2161319 := by rw [pow_add]
          _ = 21450931 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 34581109) ^ 8645277 = 17203282 := by
        calc
          (6 : ZMod 34581109) ^ 8645277 = (6 : ZMod 34581109) ^ (4322638 + 4322638 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 4322638 * (6 : ZMod 34581109) ^ 4322638) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 17203282 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 34581109) ^ 17290554 = 34581108 := by
        calc
          (6 : ZMod 34581109) ^ 17290554 = (6 : ZMod 34581109) ^ (8645277 + 8645277) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 8645277 * (6 : ZMod 34581109) ^ 8645277 := by rw [pow_add]
          _ = 34581108 := by rw [factor_0_23]; decide
      change (6 : ZMod 34581109) ^ 17290554 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (6 : ZMod 34581109) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 34581109) ^ 2 = 36 := by
        calc
          (6 : ZMod 34581109) ^ 2 = (6 : ZMod 34581109) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 1 * (6 : ZMod 34581109) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 34581109) ^ 5 = 7776 := by
        calc
          (6 : ZMod 34581109) ^ 5 = (6 : ZMod 34581109) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 2 * (6 : ZMod 34581109) ^ 2) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 34581109) ^ 10 = 25885067 := by
        calc
          (6 : ZMod 34581109) ^ 10 = (6 : ZMod 34581109) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 5 * (6 : ZMod 34581109) ^ 5 := by rw [pow_add]
          _ = 25885067 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 34581109) ^ 21 = 8925971 := by
        calc
          (6 : ZMod 34581109) ^ 21 = (6 : ZMod 34581109) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 10 * (6 : ZMod 34581109) ^ 10) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 8925971 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 34581109) ^ 43 = 14450343 := by
        calc
          (6 : ZMod 34581109) ^ 43 = (6 : ZMod 34581109) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 21 * (6 : ZMod 34581109) ^ 21) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 14450343 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 34581109) ^ 87 = 33308169 := by
        calc
          (6 : ZMod 34581109) ^ 87 = (6 : ZMod 34581109) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 43 * (6 : ZMod 34581109) ^ 43) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 33308169 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 34581109) ^ 175 = 20734013 := by
        calc
          (6 : ZMod 34581109) ^ 175 = (6 : ZMod 34581109) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 87 * (6 : ZMod 34581109) ^ 87) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 20734013 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 34581109) ^ 351 = 14188899 := by
        calc
          (6 : ZMod 34581109) ^ 351 = (6 : ZMod 34581109) ^ (175 + 175 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 175 * (6 : ZMod 34581109) ^ 175) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 14188899 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 34581109) ^ 703 = 6949542 := by
        calc
          (6 : ZMod 34581109) ^ 703 = (6 : ZMod 34581109) ^ (351 + 351 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 351 * (6 : ZMod 34581109) ^ 351) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 6949542 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 34581109) ^ 1407 = 9392241 := by
        calc
          (6 : ZMod 34581109) ^ 1407 = (6 : ZMod 34581109) ^ (703 + 703 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 703 * (6 : ZMod 34581109) ^ 703) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 9392241 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 34581109) ^ 2814 = 29715166 := by
        calc
          (6 : ZMod 34581109) ^ 2814 = (6 : ZMod 34581109) ^ (1407 + 1407) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 1407 * (6 : ZMod 34581109) ^ 1407 := by rw [pow_add]
          _ = 29715166 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 34581109) ^ 5628 = 27176930 := by
        calc
          (6 : ZMod 34581109) ^ 5628 = (6 : ZMod 34581109) ^ (2814 + 2814) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 2814 * (6 : ZMod 34581109) ^ 2814 := by rw [pow_add]
          _ = 27176930 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 34581109) ^ 11256 = 19593033 := by
        calc
          (6 : ZMod 34581109) ^ 11256 = (6 : ZMod 34581109) ^ (5628 + 5628) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 5628 * (6 : ZMod 34581109) ^ 5628 := by rw [pow_add]
          _ = 19593033 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 34581109) ^ 22513 = 30486839 := by
        calc
          (6 : ZMod 34581109) ^ 22513 = (6 : ZMod 34581109) ^ (11256 + 11256 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 11256 * (6 : ZMod 34581109) ^ 11256) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 30486839 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 34581109) ^ 45027 = 24579734 := by
        calc
          (6 : ZMod 34581109) ^ 45027 = (6 : ZMod 34581109) ^ (22513 + 22513 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 22513 * (6 : ZMod 34581109) ^ 22513) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 24579734 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 34581109) ^ 90054 = 18796002 := by
        calc
          (6 : ZMod 34581109) ^ 90054 = (6 : ZMod 34581109) ^ (45027 + 45027) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 45027 * (6 : ZMod 34581109) ^ 45027 := by rw [pow_add]
          _ = 18796002 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 34581109) ^ 180109 = 24593349 := by
        calc
          (6 : ZMod 34581109) ^ 180109 = (6 : ZMod 34581109) ^ (90054 + 90054 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 90054 * (6 : ZMod 34581109) ^ 90054) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 24593349 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 34581109) ^ 360219 = 16561515 := by
        calc
          (6 : ZMod 34581109) ^ 360219 = (6 : ZMod 34581109) ^ (180109 + 180109 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 180109 * (6 : ZMod 34581109) ^ 180109) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 16561515 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 34581109) ^ 720439 = 8136154 := by
        calc
          (6 : ZMod 34581109) ^ 720439 = (6 : ZMod 34581109) ^ (360219 + 360219 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 360219 * (6 : ZMod 34581109) ^ 360219) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 8136154 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 34581109) ^ 1440879 = 27009725 := by
        calc
          (6 : ZMod 34581109) ^ 1440879 = (6 : ZMod 34581109) ^ (720439 + 720439 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 720439 * (6 : ZMod 34581109) ^ 720439) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 27009725 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 34581109) ^ 2881759 = 12172766 := by
        calc
          (6 : ZMod 34581109) ^ 2881759 = (6 : ZMod 34581109) ^ (1440879 + 1440879 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 1440879 * (6 : ZMod 34581109) ^ 1440879) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 12172766 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 34581109) ^ 5763518 = 18528855 := by
        calc
          (6 : ZMod 34581109) ^ 5763518 = (6 : ZMod 34581109) ^ (2881759 + 2881759) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 2881759 * (6 : ZMod 34581109) ^ 2881759 := by rw [pow_add]
          _ = 18528855 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 34581109) ^ 11527036 = 18528854 := by
        calc
          (6 : ZMod 34581109) ^ 11527036 = (6 : ZMod 34581109) ^ (5763518 + 5763518) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 5763518 * (6 : ZMod 34581109) ^ 5763518 := by rw [pow_add]
          _ = 18528854 := by rw [factor_1_22]; decide
      change (6 : ZMod 34581109) ^ 11527036 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (6 : ZMod 34581109) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 34581109) ^ 2 = 36 := by
        calc
          (6 : ZMod 34581109) ^ 2 = (6 : ZMod 34581109) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 1 * (6 : ZMod 34581109) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 34581109) ^ 4 = 1296 := by
        calc
          (6 : ZMod 34581109) ^ 4 = (6 : ZMod 34581109) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 2 * (6 : ZMod 34581109) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 34581109) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 34581109) ^ 9 = (6 : ZMod 34581109) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 4 * (6 : ZMod 34581109) ^ 4) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 34581109) ^ 18 = 11728458 := by
        calc
          (6 : ZMod 34581109) ^ 18 = (6 : ZMod 34581109) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 9 * (6 : ZMod 34581109) ^ 9 := by rw [pow_add]
          _ = 11728458 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 34581109) ^ 36 = 26258673 := by
        calc
          (6 : ZMod 34581109) ^ 36 = (6 : ZMod 34581109) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 18 * (6 : ZMod 34581109) ^ 18 := by rw [pow_add]
          _ = 26258673 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 34581109) ^ 72 = 22784688 := by
        calc
          (6 : ZMod 34581109) ^ 72 = (6 : ZMod 34581109) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 36 * (6 : ZMod 34581109) ^ 36 := by rw [pow_add]
          _ = 22784688 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 34581109) ^ 145 = 9375428 := by
        calc
          (6 : ZMod 34581109) ^ 145 = (6 : ZMod 34581109) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 72 * (6 : ZMod 34581109) ^ 72) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 9375428 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 34581109) ^ 291 = 7027601 := by
        calc
          (6 : ZMod 34581109) ^ 291 = (6 : ZMod 34581109) ^ (145 + 145 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 145 * (6 : ZMod 34581109) ^ 145) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 7027601 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 34581109) ^ 582 = 26672415 := by
        calc
          (6 : ZMod 34581109) ^ 582 = (6 : ZMod 34581109) ^ (291 + 291) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 291 * (6 : ZMod 34581109) ^ 291 := by rw [pow_add]
          _ = 26672415 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 34581109) ^ 1164 = 1058483 := by
        calc
          (6 : ZMod 34581109) ^ 1164 = (6 : ZMod 34581109) ^ (582 + 582) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 582 * (6 : ZMod 34581109) ^ 582 := by rw [pow_add]
          _ = 1058483 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 34581109) ^ 2329 = 26627006 := by
        calc
          (6 : ZMod 34581109) ^ 2329 = (6 : ZMod 34581109) ^ (1164 + 1164 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 1164 * (6 : ZMod 34581109) ^ 1164) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 26627006 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 34581109) ^ 4658 = 24888095 := by
        calc
          (6 : ZMod 34581109) ^ 4658 = (6 : ZMod 34581109) ^ (2329 + 2329) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 2329 * (6 : ZMod 34581109) ^ 2329 := by rw [pow_add]
          _ = 24888095 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 34581109) ^ 9316 = 33347717 := by
        calc
          (6 : ZMod 34581109) ^ 9316 = (6 : ZMod 34581109) ^ (4658 + 4658) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 4658 * (6 : ZMod 34581109) ^ 4658 := by rw [pow_add]
          _ = 33347717 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 34581109) ^ 18632 = 32840754 := by
        calc
          (6 : ZMod 34581109) ^ 18632 = (6 : ZMod 34581109) ^ (9316 + 9316) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 9316 * (6 : ZMod 34581109) ^ 9316 := by rw [pow_add]
          _ = 32840754 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 34581109) ^ 37264 = 14513151 := by
        calc
          (6 : ZMod 34581109) ^ 37264 = (6 : ZMod 34581109) ^ (18632 + 18632) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 18632 * (6 : ZMod 34581109) ^ 18632 := by rw [pow_add]
          _ = 14513151 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 34581109) ^ 74528 = 22734123 := by
        calc
          (6 : ZMod 34581109) ^ 74528 = (6 : ZMod 34581109) ^ (37264 + 37264) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 37264 * (6 : ZMod 34581109) ^ 37264 := by rw [pow_add]
          _ = 22734123 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 34581109) ^ 149056 = 15391251 := by
        calc
          (6 : ZMod 34581109) ^ 149056 = (6 : ZMod 34581109) ^ (74528 + 74528) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 74528 * (6 : ZMod 34581109) ^ 74528 := by rw [pow_add]
          _ = 15391251 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 34581109) ^ 298113 = 31364782 := by
        calc
          (6 : ZMod 34581109) ^ 298113 = (6 : ZMod 34581109) ^ (149056 + 149056 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 149056 * (6 : ZMod 34581109) ^ 149056) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 31364782 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 34581109) ^ 596226 = 28100233 := by
        calc
          (6 : ZMod 34581109) ^ 596226 = (6 : ZMod 34581109) ^ (298113 + 298113) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 298113 * (6 : ZMod 34581109) ^ 298113 := by rw [pow_add]
          _ = 28100233 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 34581109) ^ 1192452 = 22871502 := by
        calc
          (6 : ZMod 34581109) ^ 1192452 = (6 : ZMod 34581109) ^ (596226 + 596226) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 596226 * (6 : ZMod 34581109) ^ 596226 := by rw [pow_add]
          _ = 22871502 := by rw [factor_2_19]; decide
      change (6 : ZMod 34581109) ^ 1192452 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (6 : ZMod 34581109) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 34581109) ^ 2 = 36 := by
        calc
          (6 : ZMod 34581109) ^ 2 = (6 : ZMod 34581109) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 1 * (6 : ZMod 34581109) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 34581109) ^ 5 = 7776 := by
        calc
          (6 : ZMod 34581109) ^ 5 = (6 : ZMod 34581109) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 2 * (6 : ZMod 34581109) ^ 2) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 34581109) ^ 10 = 25885067 := by
        calc
          (6 : ZMod 34581109) ^ 10 = (6 : ZMod 34581109) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 5 * (6 : ZMod 34581109) ^ 5 := by rw [pow_add]
          _ = 25885067 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 34581109) ^ 21 = 8925971 := by
        calc
          (6 : ZMod 34581109) ^ 21 = (6 : ZMod 34581109) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 10 * (6 : ZMod 34581109) ^ 10) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 8925971 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 34581109) ^ 43 = 14450343 := by
        calc
          (6 : ZMod 34581109) ^ 43 = (6 : ZMod 34581109) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 21 * (6 : ZMod 34581109) ^ 21) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 14450343 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 34581109) ^ 87 = 33308169 := by
        calc
          (6 : ZMod 34581109) ^ 87 = (6 : ZMod 34581109) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = ((6 : ZMod 34581109) ^ 43 * (6 : ZMod 34581109) ^ 43) * (6 : ZMod 34581109) := by rw [pow_succ, pow_add]
          _ = 33308169 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 34581109) ^ 174 = 9219187 := by
        calc
          (6 : ZMod 34581109) ^ 174 = (6 : ZMod 34581109) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 87 * (6 : ZMod 34581109) ^ 87 := by rw [pow_add]
          _ = 9219187 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 34581109) ^ 348 = 28402987 := by
        calc
          (6 : ZMod 34581109) ^ 348 = (6 : ZMod 34581109) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (6 : ZMod 34581109) ^ n) (by norm_num)
          _ = (6 : ZMod 34581109) ^ 174 * (6 : ZMod 34581109) ^ 174 := by rw [pow_add]
          _ = 28402987 := by rw [factor_3_7]; decide
      change (6 : ZMod 34581109) ^ 348 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_34581109

end TotientTailPeriodKiller
end Erdos249257
