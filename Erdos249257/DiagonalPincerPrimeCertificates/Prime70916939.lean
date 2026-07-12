import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_70916939 : Nat.Prime 70916939 := by
  apply lucas_primality 70916939 (2 : ZMod 70916939)
  ·
      have fermat_0 : (2 : ZMod 70916939) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 70916939) ^ 2 = 4 := by
        calc
          (2 : ZMod 70916939) ^ 2 = (2 : ZMod 70916939) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 1 * (2 : ZMod 70916939) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 70916939) ^ 4 = 16 := by
        calc
          (2 : ZMod 70916939) ^ 4 = (2 : ZMod 70916939) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 2 * (2 : ZMod 70916939) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 70916939) ^ 8 = 256 := by
        calc
          (2 : ZMod 70916939) ^ 8 = (2 : ZMod 70916939) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 4 * (2 : ZMod 70916939) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 70916939) ^ 16 = 65536 := by
        calc
          (2 : ZMod 70916939) ^ 16 = (2 : ZMod 70916939) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 8 * (2 : ZMod 70916939) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 70916939) ^ 33 = 8984973 := by
        calc
          (2 : ZMod 70916939) ^ 33 = (2 : ZMod 70916939) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 16 * (2 : ZMod 70916939) ^ 16) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 8984973 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 70916939) ^ 67 = 47922598 := by
        calc
          (2 : ZMod 70916939) ^ 67 = (2 : ZMod 70916939) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 33 * (2 : ZMod 70916939) ^ 33) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 47922598 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 70916939) ^ 135 = 10894343 := by
        calc
          (2 : ZMod 70916939) ^ 135 = (2 : ZMod 70916939) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 67 * (2 : ZMod 70916939) ^ 67) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 10894343 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 70916939) ^ 270 = 49374310 := by
        calc
          (2 : ZMod 70916939) ^ 270 = (2 : ZMod 70916939) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 135 * (2 : ZMod 70916939) ^ 135 := by rw [pow_add]
          _ = 49374310 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 70916939) ^ 541 = 37130846 := by
        calc
          (2 : ZMod 70916939) ^ 541 = (2 : ZMod 70916939) ^ (270 + 270 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 270 * (2 : ZMod 70916939) ^ 270) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 37130846 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 70916939) ^ 1082 = 38646705 := by
        calc
          (2 : ZMod 70916939) ^ 1082 = (2 : ZMod 70916939) ^ (541 + 541) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 541 * (2 : ZMod 70916939) ^ 541 := by rw [pow_add]
          _ = 38646705 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 70916939) ^ 2164 = 54798069 := by
        calc
          (2 : ZMod 70916939) ^ 2164 = (2 : ZMod 70916939) ^ (1082 + 1082) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 1082 * (2 : ZMod 70916939) ^ 1082 := by rw [pow_add]
          _ = 54798069 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 70916939) ^ 4328 = 6164234 := by
        calc
          (2 : ZMod 70916939) ^ 4328 = (2 : ZMod 70916939) ^ (2164 + 2164) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 2164 * (2 : ZMod 70916939) ^ 2164 := by rw [pow_add]
          _ = 6164234 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 70916939) ^ 8656 = 59388922 := by
        calc
          (2 : ZMod 70916939) ^ 8656 = (2 : ZMod 70916939) ^ (4328 + 4328) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 4328 * (2 : ZMod 70916939) ^ 4328 := by rw [pow_add]
          _ = 59388922 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 70916939) ^ 17313 = 47057088 := by
        calc
          (2 : ZMod 70916939) ^ 17313 = (2 : ZMod 70916939) ^ (8656 + 8656 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 8656 * (2 : ZMod 70916939) ^ 8656) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 47057088 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 70916939) ^ 34627 = 49620992 := by
        calc
          (2 : ZMod 70916939) ^ 34627 = (2 : ZMod 70916939) ^ (17313 + 17313 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 17313 * (2 : ZMod 70916939) ^ 17313) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 49620992 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 70916939) ^ 69254 = 58791798 := by
        calc
          (2 : ZMod 70916939) ^ 69254 = (2 : ZMod 70916939) ^ (34627 + 34627) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 34627 * (2 : ZMod 70916939) ^ 34627 := by rw [pow_add]
          _ = 58791798 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 70916939) ^ 138509 = 6715914 := by
        calc
          (2 : ZMod 70916939) ^ 138509 = (2 : ZMod 70916939) ^ (69254 + 69254 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 69254 * (2 : ZMod 70916939) ^ 69254) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 6715914 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 70916939) ^ 277019 = 17050341 := by
        calc
          (2 : ZMod 70916939) ^ 277019 = (2 : ZMod 70916939) ^ (138509 + 138509 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 138509 * (2 : ZMod 70916939) ^ 138509) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 17050341 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 70916939) ^ 554038 = 65157241 := by
        calc
          (2 : ZMod 70916939) ^ 554038 = (2 : ZMod 70916939) ^ (277019 + 277019) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 277019 * (2 : ZMod 70916939) ^ 277019 := by rw [pow_add]
          _ = 65157241 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 70916939) ^ 1108077 = 55980544 := by
        calc
          (2 : ZMod 70916939) ^ 1108077 = (2 : ZMod 70916939) ^ (554038 + 554038 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 554038 * (2 : ZMod 70916939) ^ 554038) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 55980544 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 70916939) ^ 2216154 = 70119400 := by
        calc
          (2 : ZMod 70916939) ^ 2216154 = (2 : ZMod 70916939) ^ (1108077 + 1108077) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 1108077 * (2 : ZMod 70916939) ^ 1108077 := by rw [pow_add]
          _ = 70119400 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 70916939) ^ 4432308 = 14430630 := by
        calc
          (2 : ZMod 70916939) ^ 4432308 = (2 : ZMod 70916939) ^ (2216154 + 2216154) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 2216154 * (2 : ZMod 70916939) ^ 2216154 := by rw [pow_add]
          _ = 14430630 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 70916939) ^ 8864617 = 59014992 := by
        calc
          (2 : ZMod 70916939) ^ 8864617 = (2 : ZMod 70916939) ^ (4432308 + 4432308 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 4432308 * (2 : ZMod 70916939) ^ 4432308) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 59014992 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 70916939) ^ 17729234 = 40406065 := by
        calc
          (2 : ZMod 70916939) ^ 17729234 = (2 : ZMod 70916939) ^ (8864617 + 8864617) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 8864617 * (2 : ZMod 70916939) ^ 8864617 := by rw [pow_add]
          _ = 40406065 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 70916939) ^ 35458469 = 70916938 := by
        calc
          (2 : ZMod 70916939) ^ 35458469 = (2 : ZMod 70916939) ^ (17729234 + 17729234 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 17729234 * (2 : ZMod 70916939) ^ 17729234) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 70916938 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 70916939) ^ 70916938 = 1 := by
        calc
          (2 : ZMod 70916939) ^ 70916938 = (2 : ZMod 70916939) ^ (35458469 + 35458469) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 35458469 * (2 : ZMod 70916939) ^ 35458469 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 2), (59, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 2), (59, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod = 70916939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 70916939) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 70916939) ^ 2 = 4 := by
        calc
          (2 : ZMod 70916939) ^ 2 = (2 : ZMod 70916939) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 1 * (2 : ZMod 70916939) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 70916939) ^ 4 = 16 := by
        calc
          (2 : ZMod 70916939) ^ 4 = (2 : ZMod 70916939) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 2 * (2 : ZMod 70916939) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 70916939) ^ 8 = 256 := by
        calc
          (2 : ZMod 70916939) ^ 8 = (2 : ZMod 70916939) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 4 * (2 : ZMod 70916939) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 70916939) ^ 16 = 65536 := by
        calc
          (2 : ZMod 70916939) ^ 16 = (2 : ZMod 70916939) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 8 * (2 : ZMod 70916939) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 70916939) ^ 33 = 8984973 := by
        calc
          (2 : ZMod 70916939) ^ 33 = (2 : ZMod 70916939) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 16 * (2 : ZMod 70916939) ^ 16) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 8984973 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 70916939) ^ 67 = 47922598 := by
        calc
          (2 : ZMod 70916939) ^ 67 = (2 : ZMod 70916939) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 33 * (2 : ZMod 70916939) ^ 33) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 47922598 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 70916939) ^ 135 = 10894343 := by
        calc
          (2 : ZMod 70916939) ^ 135 = (2 : ZMod 70916939) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 67 * (2 : ZMod 70916939) ^ 67) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 10894343 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 70916939) ^ 270 = 49374310 := by
        calc
          (2 : ZMod 70916939) ^ 270 = (2 : ZMod 70916939) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 135 * (2 : ZMod 70916939) ^ 135 := by rw [pow_add]
          _ = 49374310 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 70916939) ^ 541 = 37130846 := by
        calc
          (2 : ZMod 70916939) ^ 541 = (2 : ZMod 70916939) ^ (270 + 270 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 270 * (2 : ZMod 70916939) ^ 270) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 37130846 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 70916939) ^ 1082 = 38646705 := by
        calc
          (2 : ZMod 70916939) ^ 1082 = (2 : ZMod 70916939) ^ (541 + 541) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 541 * (2 : ZMod 70916939) ^ 541 := by rw [pow_add]
          _ = 38646705 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 70916939) ^ 2164 = 54798069 := by
        calc
          (2 : ZMod 70916939) ^ 2164 = (2 : ZMod 70916939) ^ (1082 + 1082) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 1082 * (2 : ZMod 70916939) ^ 1082 := by rw [pow_add]
          _ = 54798069 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 70916939) ^ 4328 = 6164234 := by
        calc
          (2 : ZMod 70916939) ^ 4328 = (2 : ZMod 70916939) ^ (2164 + 2164) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 2164 * (2 : ZMod 70916939) ^ 2164 := by rw [pow_add]
          _ = 6164234 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 70916939) ^ 8656 = 59388922 := by
        calc
          (2 : ZMod 70916939) ^ 8656 = (2 : ZMod 70916939) ^ (4328 + 4328) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 4328 * (2 : ZMod 70916939) ^ 4328 := by rw [pow_add]
          _ = 59388922 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 70916939) ^ 17313 = 47057088 := by
        calc
          (2 : ZMod 70916939) ^ 17313 = (2 : ZMod 70916939) ^ (8656 + 8656 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 8656 * (2 : ZMod 70916939) ^ 8656) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 47057088 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 70916939) ^ 34627 = 49620992 := by
        calc
          (2 : ZMod 70916939) ^ 34627 = (2 : ZMod 70916939) ^ (17313 + 17313 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 17313 * (2 : ZMod 70916939) ^ 17313) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 49620992 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 70916939) ^ 69254 = 58791798 := by
        calc
          (2 : ZMod 70916939) ^ 69254 = (2 : ZMod 70916939) ^ (34627 + 34627) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 34627 * (2 : ZMod 70916939) ^ 34627 := by rw [pow_add]
          _ = 58791798 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 70916939) ^ 138509 = 6715914 := by
        calc
          (2 : ZMod 70916939) ^ 138509 = (2 : ZMod 70916939) ^ (69254 + 69254 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 69254 * (2 : ZMod 70916939) ^ 69254) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 6715914 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 70916939) ^ 277019 = 17050341 := by
        calc
          (2 : ZMod 70916939) ^ 277019 = (2 : ZMod 70916939) ^ (138509 + 138509 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 138509 * (2 : ZMod 70916939) ^ 138509) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 17050341 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 70916939) ^ 554038 = 65157241 := by
        calc
          (2 : ZMod 70916939) ^ 554038 = (2 : ZMod 70916939) ^ (277019 + 277019) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 277019 * (2 : ZMod 70916939) ^ 277019 := by rw [pow_add]
          _ = 65157241 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 70916939) ^ 1108077 = 55980544 := by
        calc
          (2 : ZMod 70916939) ^ 1108077 = (2 : ZMod 70916939) ^ (554038 + 554038 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 554038 * (2 : ZMod 70916939) ^ 554038) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 55980544 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 70916939) ^ 2216154 = 70119400 := by
        calc
          (2 : ZMod 70916939) ^ 2216154 = (2 : ZMod 70916939) ^ (1108077 + 1108077) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 1108077 * (2 : ZMod 70916939) ^ 1108077 := by rw [pow_add]
          _ = 70119400 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 70916939) ^ 4432308 = 14430630 := by
        calc
          (2 : ZMod 70916939) ^ 4432308 = (2 : ZMod 70916939) ^ (2216154 + 2216154) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 2216154 * (2 : ZMod 70916939) ^ 2216154 := by rw [pow_add]
          _ = 14430630 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 70916939) ^ 8864617 = 59014992 := by
        calc
          (2 : ZMod 70916939) ^ 8864617 = (2 : ZMod 70916939) ^ (4432308 + 4432308 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 4432308 * (2 : ZMod 70916939) ^ 4432308) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 59014992 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 70916939) ^ 17729234 = 40406065 := by
        calc
          (2 : ZMod 70916939) ^ 17729234 = (2 : ZMod 70916939) ^ (8864617 + 8864617) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 8864617 * (2 : ZMod 70916939) ^ 8864617 := by rw [pow_add]
          _ = 40406065 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 70916939) ^ 35458469 = 70916938 := by
        calc
          (2 : ZMod 70916939) ^ 35458469 = (2 : ZMod 70916939) ^ (17729234 + 17729234 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 17729234 * (2 : ZMod 70916939) ^ 17729234) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 70916938 := by rw [factor_0_24]; decide
      change (2 : ZMod 70916939) ^ 35458469 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 70916939) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 70916939) ^ 3 = 8 := by
        calc
          (2 : ZMod 70916939) ^ 3 = (2 : ZMod 70916939) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 1 * (2 : ZMod 70916939) ^ 1) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 70916939) ^ 7 = 128 := by
        calc
          (2 : ZMod 70916939) ^ 7 = (2 : ZMod 70916939) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 3 * (2 : ZMod 70916939) ^ 3) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 70916939) ^ 14 = 16384 := by
        calc
          (2 : ZMod 70916939) ^ 14 = (2 : ZMod 70916939) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 7 * (2 : ZMod 70916939) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 70916939) ^ 29 = 40452339 := by
        calc
          (2 : ZMod 70916939) ^ 29 = (2 : ZMod 70916939) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 14 * (2 : ZMod 70916939) ^ 14) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 40452339 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 70916939) ^ 58 = 28626586 := by
        calc
          (2 : ZMod 70916939) ^ 58 = (2 : ZMod 70916939) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 29 * (2 : ZMod 70916939) ^ 29 := by rw [pow_add]
          _ = 28626586 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 70916939) ^ 116 = 28231506 := by
        calc
          (2 : ZMod 70916939) ^ 116 = (2 : ZMod 70916939) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 58 * (2 : ZMod 70916939) ^ 58 := by rw [pow_add]
          _ = 28231506 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 70916939) ^ 233 = 11098877 := by
        calc
          (2 : ZMod 70916939) ^ 233 = (2 : ZMod 70916939) ^ (116 + 116 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 116 * (2 : ZMod 70916939) ^ 116) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 11098877 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 70916939) ^ 467 = 14718284 := by
        calc
          (2 : ZMod 70916939) ^ 467 = (2 : ZMod 70916939) ^ (233 + 233 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 233 * (2 : ZMod 70916939) ^ 233) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 14718284 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 70916939) ^ 935 = 4782113 := by
        calc
          (2 : ZMod 70916939) ^ 935 = (2 : ZMod 70916939) ^ (467 + 467 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 467 * (2 : ZMod 70916939) ^ 467) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 4782113 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 70916939) ^ 1871 = 38850878 := by
        calc
          (2 : ZMod 70916939) ^ 1871 = (2 : ZMod 70916939) ^ (935 + 935 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 935 * (2 : ZMod 70916939) ^ 935) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 38850878 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 70916939) ^ 3743 = 33681435 := by
        calc
          (2 : ZMod 70916939) ^ 3743 = (2 : ZMod 70916939) ^ (1871 + 1871 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 1871 * (2 : ZMod 70916939) ^ 1871) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 33681435 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 70916939) ^ 7487 = 17933388 := by
        calc
          (2 : ZMod 70916939) ^ 7487 = (2 : ZMod 70916939) ^ (3743 + 3743 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 3743 * (2 : ZMod 70916939) ^ 3743) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 17933388 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 70916939) ^ 14974 = 1550897 := by
        calc
          (2 : ZMod 70916939) ^ 14974 = (2 : ZMod 70916939) ^ (7487 + 7487) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 7487 * (2 : ZMod 70916939) ^ 7487 := by rw [pow_add]
          _ = 1550897 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 70916939) ^ 29948 = 62601485 := by
        calc
          (2 : ZMod 70916939) ^ 29948 = (2 : ZMod 70916939) ^ (14974 + 14974) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 14974 * (2 : ZMod 70916939) ^ 14974 := by rw [pow_add]
          _ = 62601485 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 70916939) ^ 59896 = 64857434 := by
        calc
          (2 : ZMod 70916939) ^ 59896 = (2 : ZMod 70916939) ^ (29948 + 29948) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 29948 * (2 : ZMod 70916939) ^ 29948 := by rw [pow_add]
          _ = 64857434 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 70916939) ^ 119792 = 1093080 := by
        calc
          (2 : ZMod 70916939) ^ 119792 = (2 : ZMod 70916939) ^ (59896 + 59896) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 59896 * (2 : ZMod 70916939) ^ 59896 := by rw [pow_add]
          _ = 1093080 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 70916939) ^ 239584 = 15298128 := by
        calc
          (2 : ZMod 70916939) ^ 239584 = (2 : ZMod 70916939) ^ (119792 + 119792) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 119792 * (2 : ZMod 70916939) ^ 119792 := by rw [pow_add]
          _ = 15298128 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 70916939) ^ 479168 = 13578240 := by
        calc
          (2 : ZMod 70916939) ^ 479168 = (2 : ZMod 70916939) ^ (239584 + 239584) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 239584 * (2 : ZMod 70916939) ^ 239584 := by rw [pow_add]
          _ = 13578240 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 70916939) ^ 958337 = 39980604 := by
        calc
          (2 : ZMod 70916939) ^ 958337 = (2 : ZMod 70916939) ^ (479168 + 479168 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 479168 * (2 : ZMod 70916939) ^ 479168) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 39980604 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 70916939) ^ 1916674 = 38718346 := by
        calc
          (2 : ZMod 70916939) ^ 1916674 = (2 : ZMod 70916939) ^ (958337 + 958337) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 958337 * (2 : ZMod 70916939) ^ 958337 := by rw [pow_add]
          _ = 38718346 := by rw [factor_1_19]; decide
      change (2 : ZMod 70916939) ^ 1916674 ≠ 1
      rw [factor_1_20]
      decide
    ·
      have factor_2_0 : (2 : ZMod 70916939) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 70916939) ^ 2 = 4 := by
        calc
          (2 : ZMod 70916939) ^ 2 = (2 : ZMod 70916939) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 1 * (2 : ZMod 70916939) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 70916939) ^ 4 = 16 := by
        calc
          (2 : ZMod 70916939) ^ 4 = (2 : ZMod 70916939) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 2 * (2 : ZMod 70916939) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 70916939) ^ 9 = 512 := by
        calc
          (2 : ZMod 70916939) ^ 9 = (2 : ZMod 70916939) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 4 * (2 : ZMod 70916939) ^ 4) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 70916939) ^ 18 = 262144 := by
        calc
          (2 : ZMod 70916939) ^ 18 = (2 : ZMod 70916939) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 9 * (2 : ZMod 70916939) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 70916939) ^ 36 = 962845 := by
        calc
          (2 : ZMod 70916939) ^ 36 = (2 : ZMod 70916939) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 18 * (2 : ZMod 70916939) ^ 18 := by rw [pow_add]
          _ = 962845 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 70916939) ^ 73 = 17617895 := by
        calc
          (2 : ZMod 70916939) ^ 73 = (2 : ZMod 70916939) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 36 * (2 : ZMod 70916939) ^ 36) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 17617895 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 70916939) ^ 146 = 43695618 := by
        calc
          (2 : ZMod 70916939) ^ 146 = (2 : ZMod 70916939) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 73 * (2 : ZMod 70916939) ^ 73 := by rw [pow_add]
          _ = 43695618 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 70916939) ^ 293 = 1497538 := by
        calc
          (2 : ZMod 70916939) ^ 293 = (2 : ZMod 70916939) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 146 * (2 : ZMod 70916939) ^ 146) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 1497538 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 70916939) ^ 586 = 13699447 := by
        calc
          (2 : ZMod 70916939) ^ 586 = (2 : ZMod 70916939) ^ (293 + 293) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 293 * (2 : ZMod 70916939) ^ 293 := by rw [pow_add]
          _ = 13699447 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 70916939) ^ 1173 = 25053845 := by
        calc
          (2 : ZMod 70916939) ^ 1173 = (2 : ZMod 70916939) ^ (586 + 586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 586 * (2 : ZMod 70916939) ^ 586) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 25053845 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 70916939) ^ 2347 = 64152032 := by
        calc
          (2 : ZMod 70916939) ^ 2347 = (2 : ZMod 70916939) ^ (1173 + 1173 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 1173 * (2 : ZMod 70916939) ^ 1173) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 64152032 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 70916939) ^ 4695 = 49871033 := by
        calc
          (2 : ZMod 70916939) ^ 4695 = (2 : ZMod 70916939) ^ (2347 + 2347 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 2347 * (2 : ZMod 70916939) ^ 2347) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 49871033 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 70916939) ^ 9390 = 49349135 := by
        calc
          (2 : ZMod 70916939) ^ 9390 = (2 : ZMod 70916939) ^ (4695 + 4695) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 4695 * (2 : ZMod 70916939) ^ 4695 := by rw [pow_add]
          _ = 49349135 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 70916939) ^ 18780 = 10881742 := by
        calc
          (2 : ZMod 70916939) ^ 18780 = (2 : ZMod 70916939) ^ (9390 + 9390) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 9390 * (2 : ZMod 70916939) ^ 9390 := by rw [pow_add]
          _ = 10881742 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 70916939) ^ 37561 = 53128432 := by
        calc
          (2 : ZMod 70916939) ^ 37561 = (2 : ZMod 70916939) ^ (18780 + 18780 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 18780 * (2 : ZMod 70916939) ^ 18780) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 53128432 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 70916939) ^ 75123 = 49945366 := by
        calc
          (2 : ZMod 70916939) ^ 75123 = (2 : ZMod 70916939) ^ (37561 + 37561 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 37561 * (2 : ZMod 70916939) ^ 37561) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 49945366 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 70916939) ^ 150247 = 33986254 := by
        calc
          (2 : ZMod 70916939) ^ 150247 = (2 : ZMod 70916939) ^ (75123 + 75123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 75123 * (2 : ZMod 70916939) ^ 75123) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 33986254 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 70916939) ^ 300495 = 3602036 := by
        calc
          (2 : ZMod 70916939) ^ 300495 = (2 : ZMod 70916939) ^ (150247 + 150247 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 150247 * (2 : ZMod 70916939) ^ 150247) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 3602036 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 70916939) ^ 600991 = 38624163 := by
        calc
          (2 : ZMod 70916939) ^ 600991 = (2 : ZMod 70916939) ^ (300495 + 300495 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 300495 * (2 : ZMod 70916939) ^ 300495) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 38624163 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 70916939) ^ 1201982 = 5830392 := by
        calc
          (2 : ZMod 70916939) ^ 1201982 = (2 : ZMod 70916939) ^ (600991 + 600991) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 600991 * (2 : ZMod 70916939) ^ 600991 := by rw [pow_add]
          _ = 5830392 := by rw [factor_2_19]; decide
      change (2 : ZMod 70916939) ^ 1201982 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (2 : ZMod 70916939) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 70916939) ^ 2 = 4 := by
        calc
          (2 : ZMod 70916939) ^ 2 = (2 : ZMod 70916939) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 1 * (2 : ZMod 70916939) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 70916939) ^ 4 = 16 := by
        calc
          (2 : ZMod 70916939) ^ 4 = (2 : ZMod 70916939) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 2 * (2 : ZMod 70916939) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 70916939) ^ 9 = 512 := by
        calc
          (2 : ZMod 70916939) ^ 9 = (2 : ZMod 70916939) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 4 * (2 : ZMod 70916939) ^ 4) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 70916939) ^ 19 = 524288 := by
        calc
          (2 : ZMod 70916939) ^ 19 = (2 : ZMod 70916939) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 9 * (2 : ZMod 70916939) ^ 9) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 70916939) ^ 39 = 7702760 := by
        calc
          (2 : ZMod 70916939) ^ 39 = (2 : ZMod 70916939) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 19 * (2 : ZMod 70916939) ^ 19) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 7702760 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 70916939) ^ 78 = 67354067 := by
        calc
          (2 : ZMod 70916939) ^ 78 = (2 : ZMod 70916939) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 39 * (2 : ZMod 70916939) ^ 39 := by rw [pow_add]
          _ = 67354067 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 70916939) ^ 157 = 62365585 := by
        calc
          (2 : ZMod 70916939) ^ 157 = (2 : ZMod 70916939) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 78 * (2 : ZMod 70916939) ^ 78) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 62365585 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 70916939) ^ 315 = 16336322 := by
        calc
          (2 : ZMod 70916939) ^ 315 = (2 : ZMod 70916939) ^ (157 + 157 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 157 * (2 : ZMod 70916939) ^ 157) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 16336322 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 70916939) ^ 631 = 23113110 := by
        calc
          (2 : ZMod 70916939) ^ 631 = (2 : ZMod 70916939) ^ (315 + 315 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 315 * (2 : ZMod 70916939) ^ 315) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 23113110 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 70916939) ^ 1262 = 41640819 := by
        calc
          (2 : ZMod 70916939) ^ 1262 = (2 : ZMod 70916939) ^ (631 + 631) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 631 * (2 : ZMod 70916939) ^ 631 := by rw [pow_add]
          _ = 41640819 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 70916939) ^ 2524 = 69625945 := by
        calc
          (2 : ZMod 70916939) ^ 2524 = (2 : ZMod 70916939) ^ (1262 + 1262) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 1262 * (2 : ZMod 70916939) ^ 1262 := by rw [pow_add]
          _ = 69625945 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 70916939) ^ 5048 = 46524597 := by
        calc
          (2 : ZMod 70916939) ^ 5048 = (2 : ZMod 70916939) ^ (2524 + 2524) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 2524 * (2 : ZMod 70916939) ^ 2524 := by rw [pow_add]
          _ = 46524597 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 70916939) ^ 10096 = 38061108 := by
        calc
          (2 : ZMod 70916939) ^ 10096 = (2 : ZMod 70916939) ^ (5048 + 5048) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 5048 * (2 : ZMod 70916939) ^ 5048 := by rw [pow_add]
          _ = 38061108 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 70916939) ^ 20192 = 42545393 := by
        calc
          (2 : ZMod 70916939) ^ 20192 = (2 : ZMod 70916939) ^ (10096 + 10096) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 10096 * (2 : ZMod 70916939) ^ 10096 := by rw [pow_add]
          _ = 42545393 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 70916939) ^ 40385 = 54023465 := by
        calc
          (2 : ZMod 70916939) ^ 40385 = (2 : ZMod 70916939) ^ (20192 + 20192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 20192 * (2 : ZMod 70916939) ^ 20192) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 54023465 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 70916939) ^ 80771 = 43604207 := by
        calc
          (2 : ZMod 70916939) ^ 80771 = (2 : ZMod 70916939) ^ (40385 + 40385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = ((2 : ZMod 70916939) ^ 40385 * (2 : ZMod 70916939) ^ 40385) * (2 : ZMod 70916939) := by rw [pow_succ, pow_add]
          _ = 43604207 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 70916939) ^ 161542 = 48674425 := by
        calc
          (2 : ZMod 70916939) ^ 161542 = (2 : ZMod 70916939) ^ (80771 + 80771) :=
            congrArg (fun n : ℕ => (2 : ZMod 70916939) ^ n) (by norm_num)
          _ = (2 : ZMod 70916939) ^ 80771 * (2 : ZMod 70916939) ^ 80771 := by rw [pow_add]
          _ = 48674425 := by rw [factor_3_16]; decide
      change (2 : ZMod 70916939) ^ 161542 ≠ 1
      rw [factor_3_17]
      decide

#print axioms prime_lucas_70916939

end TotientTailPeriodKiller
end Erdos249257
