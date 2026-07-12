import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_280150093 : Nat.Prime 280150093 := by
  apply lucas_primality 280150093 (5 : ZMod 280150093)
  ·
      have fermat_0 : (5 : ZMod 280150093) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 280150093) ^ 2 = 25 := by
        calc
          (5 : ZMod 280150093) ^ 2 = (5 : ZMod 280150093) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 1 * (5 : ZMod 280150093) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 280150093) ^ 4 = 625 := by
        calc
          (5 : ZMod 280150093) ^ 4 = (5 : ZMod 280150093) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 2 * (5 : ZMod 280150093) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 280150093) ^ 8 = 390625 := by
        calc
          (5 : ZMod 280150093) ^ 8 = (5 : ZMod 280150093) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 4 * (5 : ZMod 280150093) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 280150093) ^ 16 = 186240033 := by
        calc
          (5 : ZMod 280150093) ^ 16 = (5 : ZMod 280150093) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 8 * (5 : ZMod 280150093) ^ 8 := by rw [pow_add]
          _ = 186240033 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 280150093) ^ 33 = 236410501 := by
        calc
          (5 : ZMod 280150093) ^ 33 = (5 : ZMod 280150093) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 16 * (5 : ZMod 280150093) ^ 16) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 236410501 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 280150093) ^ 66 = 199627232 := by
        calc
          (5 : ZMod 280150093) ^ 66 = (5 : ZMod 280150093) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 33 * (5 : ZMod 280150093) ^ 33 := by rw [pow_add]
          _ = 199627232 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 280150093) ^ 133 = 28138569 := by
        calc
          (5 : ZMod 280150093) ^ 133 = (5 : ZMod 280150093) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 66 * (5 : ZMod 280150093) ^ 66) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 28138569 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 280150093) ^ 267 = 232224557 := by
        calc
          (5 : ZMod 280150093) ^ 267 = (5 : ZMod 280150093) ^ (133 + 133 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 133 * (5 : ZMod 280150093) ^ 133) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 232224557 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 280150093) ^ 534 = 238661451 := by
        calc
          (5 : ZMod 280150093) ^ 534 = (5 : ZMod 280150093) ^ (267 + 267) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 267 * (5 : ZMod 280150093) ^ 267 := by rw [pow_add]
          _ = 238661451 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 280150093) ^ 1068 = 248790588 := by
        calc
          (5 : ZMod 280150093) ^ 1068 = (5 : ZMod 280150093) ^ (534 + 534) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 534 * (5 : ZMod 280150093) ^ 534 := by rw [pow_add]
          _ = 248790588 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 280150093) ^ 2137 = 31372884 := by
        calc
          (5 : ZMod 280150093) ^ 2137 = (5 : ZMod 280150093) ^ (1068 + 1068 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 1068 * (5 : ZMod 280150093) ^ 1068) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 31372884 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 280150093) ^ 4274 = 85288417 := by
        calc
          (5 : ZMod 280150093) ^ 4274 = (5 : ZMod 280150093) ^ (2137 + 2137) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 2137 * (5 : ZMod 280150093) ^ 2137 := by rw [pow_add]
          _ = 85288417 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 280150093) ^ 8549 = 222926452 := by
        calc
          (5 : ZMod 280150093) ^ 8549 = (5 : ZMod 280150093) ^ (4274 + 4274 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 4274 * (5 : ZMod 280150093) ^ 4274) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 222926452 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 280150093) ^ 17099 = 127664142 := by
        calc
          (5 : ZMod 280150093) ^ 17099 = (5 : ZMod 280150093) ^ (8549 + 8549 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 8549 * (5 : ZMod 280150093) ^ 8549) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 127664142 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 280150093) ^ 34198 = 37237895 := by
        calc
          (5 : ZMod 280150093) ^ 34198 = (5 : ZMod 280150093) ^ (17099 + 17099) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 17099 * (5 : ZMod 280150093) ^ 17099 := by rw [pow_add]
          _ = 37237895 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 280150093) ^ 68396 = 227808367 := by
        calc
          (5 : ZMod 280150093) ^ 68396 = (5 : ZMod 280150093) ^ (34198 + 34198) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 34198 * (5 : ZMod 280150093) ^ 34198 := by rw [pow_add]
          _ = 227808367 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 280150093) ^ 136792 = 164589384 := by
        calc
          (5 : ZMod 280150093) ^ 136792 = (5 : ZMod 280150093) ^ (68396 + 68396) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 68396 * (5 : ZMod 280150093) ^ 68396 := by rw [pow_add]
          _ = 164589384 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 280150093) ^ 273584 = 187181246 := by
        calc
          (5 : ZMod 280150093) ^ 273584 = (5 : ZMod 280150093) ^ (136792 + 136792) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 136792 * (5 : ZMod 280150093) ^ 136792 := by rw [pow_add]
          _ = 187181246 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 280150093) ^ 547168 = 154868201 := by
        calc
          (5 : ZMod 280150093) ^ 547168 = (5 : ZMod 280150093) ^ (273584 + 273584) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 273584 * (5 : ZMod 280150093) ^ 273584 := by rw [pow_add]
          _ = 154868201 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 280150093) ^ 1094336 = 65927048 := by
        calc
          (5 : ZMod 280150093) ^ 1094336 = (5 : ZMod 280150093) ^ (547168 + 547168) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 547168 * (5 : ZMod 280150093) ^ 547168 := by rw [pow_add]
          _ = 65927048 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 280150093) ^ 2188672 = 207200175 := by
        calc
          (5 : ZMod 280150093) ^ 2188672 = (5 : ZMod 280150093) ^ (1094336 + 1094336) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 1094336 * (5 : ZMod 280150093) ^ 1094336 := by rw [pow_add]
          _ = 207200175 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 280150093) ^ 4377345 = 236861138 := by
        calc
          (5 : ZMod 280150093) ^ 4377345 = (5 : ZMod 280150093) ^ (2188672 + 2188672 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 2188672 * (5 : ZMod 280150093) ^ 2188672) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 236861138 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 280150093) ^ 8754690 = 127811863 := by
        calc
          (5 : ZMod 280150093) ^ 8754690 = (5 : ZMod 280150093) ^ (4377345 + 4377345) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 4377345 * (5 : ZMod 280150093) ^ 4377345 := by rw [pow_add]
          _ = 127811863 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 280150093) ^ 17509380 = 189144470 := by
        calc
          (5 : ZMod 280150093) ^ 17509380 = (5 : ZMod 280150093) ^ (8754690 + 8754690) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 8754690 * (5 : ZMod 280150093) ^ 8754690 := by rw [pow_add]
          _ = 189144470 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 280150093) ^ 35018761 = 35384925 := by
        calc
          (5 : ZMod 280150093) ^ 35018761 = (5 : ZMod 280150093) ^ (17509380 + 17509380 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 17509380 * (5 : ZMod 280150093) ^ 17509380) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 35384925 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 280150093) ^ 70037523 = 44573586 := by
        calc
          (5 : ZMod 280150093) ^ 70037523 = (5 : ZMod 280150093) ^ (35018761 + 35018761 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 35018761 * (5 : ZMod 280150093) ^ 35018761) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 44573586 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 280150093) ^ 140075046 = 280150092 := by
        calc
          (5 : ZMod 280150093) ^ 140075046 = (5 : ZMod 280150093) ^ (70037523 + 70037523) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 70037523 * (5 : ZMod 280150093) ^ 70037523 := by rw [pow_add]
          _ = 280150092 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 280150093) ^ 280150092 = 1 := by
        calc
          (5 : ZMod 280150093) ^ 280150092 = (5 : ZMod 280150093) ^ (140075046 + 140075046) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 140075046 * (5 : ZMod 280150093) ^ 140075046 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (29, 1), (268343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (29, 1), (268343, 1)] : List FactorBlock).map factorBlockValue).prod = 280150093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 280150093) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 280150093) ^ 2 = 25 := by
        calc
          (5 : ZMod 280150093) ^ 2 = (5 : ZMod 280150093) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 1 * (5 : ZMod 280150093) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 280150093) ^ 4 = 625 := by
        calc
          (5 : ZMod 280150093) ^ 4 = (5 : ZMod 280150093) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 2 * (5 : ZMod 280150093) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 280150093) ^ 8 = 390625 := by
        calc
          (5 : ZMod 280150093) ^ 8 = (5 : ZMod 280150093) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 4 * (5 : ZMod 280150093) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 280150093) ^ 16 = 186240033 := by
        calc
          (5 : ZMod 280150093) ^ 16 = (5 : ZMod 280150093) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 8 * (5 : ZMod 280150093) ^ 8 := by rw [pow_add]
          _ = 186240033 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 280150093) ^ 33 = 236410501 := by
        calc
          (5 : ZMod 280150093) ^ 33 = (5 : ZMod 280150093) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 16 * (5 : ZMod 280150093) ^ 16) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 236410501 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 280150093) ^ 66 = 199627232 := by
        calc
          (5 : ZMod 280150093) ^ 66 = (5 : ZMod 280150093) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 33 * (5 : ZMod 280150093) ^ 33 := by rw [pow_add]
          _ = 199627232 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 280150093) ^ 133 = 28138569 := by
        calc
          (5 : ZMod 280150093) ^ 133 = (5 : ZMod 280150093) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 66 * (5 : ZMod 280150093) ^ 66) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 28138569 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 280150093) ^ 267 = 232224557 := by
        calc
          (5 : ZMod 280150093) ^ 267 = (5 : ZMod 280150093) ^ (133 + 133 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 133 * (5 : ZMod 280150093) ^ 133) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 232224557 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 280150093) ^ 534 = 238661451 := by
        calc
          (5 : ZMod 280150093) ^ 534 = (5 : ZMod 280150093) ^ (267 + 267) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 267 * (5 : ZMod 280150093) ^ 267 := by rw [pow_add]
          _ = 238661451 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 280150093) ^ 1068 = 248790588 := by
        calc
          (5 : ZMod 280150093) ^ 1068 = (5 : ZMod 280150093) ^ (534 + 534) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 534 * (5 : ZMod 280150093) ^ 534 := by rw [pow_add]
          _ = 248790588 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 280150093) ^ 2137 = 31372884 := by
        calc
          (5 : ZMod 280150093) ^ 2137 = (5 : ZMod 280150093) ^ (1068 + 1068 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 1068 * (5 : ZMod 280150093) ^ 1068) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 31372884 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 280150093) ^ 4274 = 85288417 := by
        calc
          (5 : ZMod 280150093) ^ 4274 = (5 : ZMod 280150093) ^ (2137 + 2137) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 2137 * (5 : ZMod 280150093) ^ 2137 := by rw [pow_add]
          _ = 85288417 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 280150093) ^ 8549 = 222926452 := by
        calc
          (5 : ZMod 280150093) ^ 8549 = (5 : ZMod 280150093) ^ (4274 + 4274 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 4274 * (5 : ZMod 280150093) ^ 4274) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 222926452 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 280150093) ^ 17099 = 127664142 := by
        calc
          (5 : ZMod 280150093) ^ 17099 = (5 : ZMod 280150093) ^ (8549 + 8549 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 8549 * (5 : ZMod 280150093) ^ 8549) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 127664142 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 280150093) ^ 34198 = 37237895 := by
        calc
          (5 : ZMod 280150093) ^ 34198 = (5 : ZMod 280150093) ^ (17099 + 17099) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 17099 * (5 : ZMod 280150093) ^ 17099 := by rw [pow_add]
          _ = 37237895 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 280150093) ^ 68396 = 227808367 := by
        calc
          (5 : ZMod 280150093) ^ 68396 = (5 : ZMod 280150093) ^ (34198 + 34198) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 34198 * (5 : ZMod 280150093) ^ 34198 := by rw [pow_add]
          _ = 227808367 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 280150093) ^ 136792 = 164589384 := by
        calc
          (5 : ZMod 280150093) ^ 136792 = (5 : ZMod 280150093) ^ (68396 + 68396) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 68396 * (5 : ZMod 280150093) ^ 68396 := by rw [pow_add]
          _ = 164589384 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 280150093) ^ 273584 = 187181246 := by
        calc
          (5 : ZMod 280150093) ^ 273584 = (5 : ZMod 280150093) ^ (136792 + 136792) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 136792 * (5 : ZMod 280150093) ^ 136792 := by rw [pow_add]
          _ = 187181246 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 280150093) ^ 547168 = 154868201 := by
        calc
          (5 : ZMod 280150093) ^ 547168 = (5 : ZMod 280150093) ^ (273584 + 273584) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 273584 * (5 : ZMod 280150093) ^ 273584 := by rw [pow_add]
          _ = 154868201 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 280150093) ^ 1094336 = 65927048 := by
        calc
          (5 : ZMod 280150093) ^ 1094336 = (5 : ZMod 280150093) ^ (547168 + 547168) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 547168 * (5 : ZMod 280150093) ^ 547168 := by rw [pow_add]
          _ = 65927048 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 280150093) ^ 2188672 = 207200175 := by
        calc
          (5 : ZMod 280150093) ^ 2188672 = (5 : ZMod 280150093) ^ (1094336 + 1094336) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 1094336 * (5 : ZMod 280150093) ^ 1094336 := by rw [pow_add]
          _ = 207200175 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 280150093) ^ 4377345 = 236861138 := by
        calc
          (5 : ZMod 280150093) ^ 4377345 = (5 : ZMod 280150093) ^ (2188672 + 2188672 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 2188672 * (5 : ZMod 280150093) ^ 2188672) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 236861138 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 280150093) ^ 8754690 = 127811863 := by
        calc
          (5 : ZMod 280150093) ^ 8754690 = (5 : ZMod 280150093) ^ (4377345 + 4377345) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 4377345 * (5 : ZMod 280150093) ^ 4377345 := by rw [pow_add]
          _ = 127811863 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 280150093) ^ 17509380 = 189144470 := by
        calc
          (5 : ZMod 280150093) ^ 17509380 = (5 : ZMod 280150093) ^ (8754690 + 8754690) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 8754690 * (5 : ZMod 280150093) ^ 8754690 := by rw [pow_add]
          _ = 189144470 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 280150093) ^ 35018761 = 35384925 := by
        calc
          (5 : ZMod 280150093) ^ 35018761 = (5 : ZMod 280150093) ^ (17509380 + 17509380 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 17509380 * (5 : ZMod 280150093) ^ 17509380) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 35384925 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 280150093) ^ 70037523 = 44573586 := by
        calc
          (5 : ZMod 280150093) ^ 70037523 = (5 : ZMod 280150093) ^ (35018761 + 35018761 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 35018761 * (5 : ZMod 280150093) ^ 35018761) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 44573586 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 280150093) ^ 140075046 = 280150092 := by
        calc
          (5 : ZMod 280150093) ^ 140075046 = (5 : ZMod 280150093) ^ (70037523 + 70037523) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 70037523 * (5 : ZMod 280150093) ^ 70037523 := by rw [pow_add]
          _ = 280150092 := by rw [factor_0_26]; decide
      change (5 : ZMod 280150093) ^ 140075046 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (5 : ZMod 280150093) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 280150093) ^ 2 = 25 := by
        calc
          (5 : ZMod 280150093) ^ 2 = (5 : ZMod 280150093) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 1 * (5 : ZMod 280150093) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 280150093) ^ 5 = 3125 := by
        calc
          (5 : ZMod 280150093) ^ 5 = (5 : ZMod 280150093) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 2 * (5 : ZMod 280150093) ^ 2) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 280150093) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 280150093) ^ 11 = (5 : ZMod 280150093) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 5 * (5 : ZMod 280150093) ^ 5) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 280150093) ^ 22 = 81499634 := by
        calc
          (5 : ZMod 280150093) ^ 22 = (5 : ZMod 280150093) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 11 * (5 : ZMod 280150093) ^ 11 := by rw [pow_add]
          _ = 81499634 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 280150093) ^ 44 = 7309849 := by
        calc
          (5 : ZMod 280150093) ^ 44 = (5 : ZMod 280150093) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 22 * (5 : ZMod 280150093) ^ 22 := by rw [pow_add]
          _ = 7309849 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 280150093) ^ 89 = 123573160 := by
        calc
          (5 : ZMod 280150093) ^ 89 = (5 : ZMod 280150093) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 44 * (5 : ZMod 280150093) ^ 44) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 123573160 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 280150093) ^ 178 = 134323313 := by
        calc
          (5 : ZMod 280150093) ^ 178 = (5 : ZMod 280150093) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 89 * (5 : ZMod 280150093) ^ 89 := by rw [pow_add]
          _ = 134323313 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 280150093) ^ 356 = 4035315 := by
        calc
          (5 : ZMod 280150093) ^ 356 = (5 : ZMod 280150093) ^ (178 + 178) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 178 * (5 : ZMod 280150093) ^ 178 := by rw [pow_add]
          _ = 4035315 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 280150093) ^ 712 = 42993600 := by
        calc
          (5 : ZMod 280150093) ^ 712 = (5 : ZMod 280150093) ^ (356 + 356) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 356 * (5 : ZMod 280150093) ^ 356 := by rw [pow_add]
          _ = 42993600 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 280150093) ^ 1424 = 277139676 := by
        calc
          (5 : ZMod 280150093) ^ 1424 = (5 : ZMod 280150093) ^ (712 + 712) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 712 * (5 : ZMod 280150093) ^ 712 := by rw [pow_add]
          _ = 277139676 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 280150093) ^ 2849 = 175777160 := by
        calc
          (5 : ZMod 280150093) ^ 2849 = (5 : ZMod 280150093) ^ (1424 + 1424 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 1424 * (5 : ZMod 280150093) ^ 1424) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 175777160 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 280150093) ^ 5699 = 248766731 := by
        calc
          (5 : ZMod 280150093) ^ 5699 = (5 : ZMod 280150093) ^ (2849 + 2849 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 2849 * (5 : ZMod 280150093) ^ 2849) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 248766731 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 280150093) ^ 11399 = 104528484 := by
        calc
          (5 : ZMod 280150093) ^ 11399 = (5 : ZMod 280150093) ^ (5699 + 5699 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 5699 * (5 : ZMod 280150093) ^ 5699) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 104528484 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 280150093) ^ 22798 = 152722006 := by
        calc
          (5 : ZMod 280150093) ^ 22798 = (5 : ZMod 280150093) ^ (11399 + 11399) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 11399 * (5 : ZMod 280150093) ^ 11399 := by rw [pow_add]
          _ = 152722006 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 280150093) ^ 45597 = 191454158 := by
        calc
          (5 : ZMod 280150093) ^ 45597 = (5 : ZMod 280150093) ^ (22798 + 22798 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 22798 * (5 : ZMod 280150093) ^ 22798) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 191454158 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 280150093) ^ 91194 = 164366673 := by
        calc
          (5 : ZMod 280150093) ^ 91194 = (5 : ZMod 280150093) ^ (45597 + 45597) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 45597 * (5 : ZMod 280150093) ^ 45597 := by rw [pow_add]
          _ = 164366673 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 280150093) ^ 182389 = 247805652 := by
        calc
          (5 : ZMod 280150093) ^ 182389 = (5 : ZMod 280150093) ^ (91194 + 91194 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 91194 * (5 : ZMod 280150093) ^ 91194) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 247805652 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 280150093) ^ 364778 = 52213139 := by
        calc
          (5 : ZMod 280150093) ^ 364778 = (5 : ZMod 280150093) ^ (182389 + 182389) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 182389 * (5 : ZMod 280150093) ^ 182389 := by rw [pow_add]
          _ = 52213139 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 280150093) ^ 729557 = 15183216 := by
        calc
          (5 : ZMod 280150093) ^ 729557 = (5 : ZMod 280150093) ^ (364778 + 364778 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 364778 * (5 : ZMod 280150093) ^ 364778) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 15183216 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 280150093) ^ 1459115 = 137573894 := by
        calc
          (5 : ZMod 280150093) ^ 1459115 = (5 : ZMod 280150093) ^ (729557 + 729557 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 729557 * (5 : ZMod 280150093) ^ 729557) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 137573894 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 280150093) ^ 2918230 = 222364136 := by
        calc
          (5 : ZMod 280150093) ^ 2918230 = (5 : ZMod 280150093) ^ (1459115 + 1459115) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 1459115 * (5 : ZMod 280150093) ^ 1459115 := by rw [pow_add]
          _ = 222364136 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 280150093) ^ 5836460 = 10153044 := by
        calc
          (5 : ZMod 280150093) ^ 5836460 = (5 : ZMod 280150093) ^ (2918230 + 2918230) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 2918230 * (5 : ZMod 280150093) ^ 2918230 := by rw [pow_add]
          _ = 10153044 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 280150093) ^ 11672920 = 274245656 := by
        calc
          (5 : ZMod 280150093) ^ 11672920 = (5 : ZMod 280150093) ^ (5836460 + 5836460) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 5836460 * (5 : ZMod 280150093) ^ 5836460 := by rw [pow_add]
          _ = 274245656 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 280150093) ^ 23345841 = 252369501 := by
        calc
          (5 : ZMod 280150093) ^ 23345841 = (5 : ZMod 280150093) ^ (11672920 + 11672920 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 11672920 * (5 : ZMod 280150093) ^ 11672920) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 252369501 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 280150093) ^ 46691682 = 173722855 := by
        calc
          (5 : ZMod 280150093) ^ 46691682 = (5 : ZMod 280150093) ^ (23345841 + 23345841) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 23345841 * (5 : ZMod 280150093) ^ 23345841 := by rw [pow_add]
          _ = 173722855 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 280150093) ^ 93383364 = 173722854 := by
        calc
          (5 : ZMod 280150093) ^ 93383364 = (5 : ZMod 280150093) ^ (46691682 + 46691682) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 46691682 * (5 : ZMod 280150093) ^ 46691682 := by rw [pow_add]
          _ = 173722854 := by rw [factor_1_25]; decide
      change (5 : ZMod 280150093) ^ 93383364 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (5 : ZMod 280150093) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 280150093) ^ 2 = 25 := by
        calc
          (5 : ZMod 280150093) ^ 2 = (5 : ZMod 280150093) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 1 * (5 : ZMod 280150093) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 280150093) ^ 4 = 625 := by
        calc
          (5 : ZMod 280150093) ^ 4 = (5 : ZMod 280150093) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 2 * (5 : ZMod 280150093) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 280150093) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 280150093) ^ 9 = (5 : ZMod 280150093) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 4 * (5 : ZMod 280150093) ^ 4) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 280150093) ^ 18 = 173599337 := by
        calc
          (5 : ZMod 280150093) ^ 18 = (5 : ZMod 280150093) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 9 * (5 : ZMod 280150093) ^ 9 := by rw [pow_add]
          _ = 173599337 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 280150093) ^ 36 = 135552860 := by
        calc
          (5 : ZMod 280150093) ^ 36 = (5 : ZMod 280150093) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 18 * (5 : ZMod 280150093) ^ 18 := by rw [pow_add]
          _ = 135552860 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 280150093) ^ 73 = 201972783 := by
        calc
          (5 : ZMod 280150093) ^ 73 = (5 : ZMod 280150093) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 36 * (5 : ZMod 280150093) ^ 36) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 201972783 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 280150093) ^ 147 = 57544474 := by
        calc
          (5 : ZMod 280150093) ^ 147 = (5 : ZMod 280150093) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 73 * (5 : ZMod 280150093) ^ 73) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 57544474 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 280150093) ^ 294 = 232879280 := by
        calc
          (5 : ZMod 280150093) ^ 294 = (5 : ZMod 280150093) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 147 * (5 : ZMod 280150093) ^ 147 := by rw [pow_add]
          _ = 232879280 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 280150093) ^ 589 = 38627518 := by
        calc
          (5 : ZMod 280150093) ^ 589 = (5 : ZMod 280150093) ^ (294 + 294 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 294 * (5 : ZMod 280150093) ^ 294) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 38627518 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 280150093) ^ 1179 = 182302134 := by
        calc
          (5 : ZMod 280150093) ^ 1179 = (5 : ZMod 280150093) ^ (589 + 589 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 589 * (5 : ZMod 280150093) ^ 589) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 182302134 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 280150093) ^ 2358 = 82059619 := by
        calc
          (5 : ZMod 280150093) ^ 2358 = (5 : ZMod 280150093) ^ (1179 + 1179) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 1179 * (5 : ZMod 280150093) ^ 1179 := by rw [pow_add]
          _ = 82059619 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 280150093) ^ 4716 = 145096192 := by
        calc
          (5 : ZMod 280150093) ^ 4716 = (5 : ZMod 280150093) ^ (2358 + 2358) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 2358 * (5 : ZMod 280150093) ^ 2358 := by rw [pow_add]
          _ = 145096192 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 280150093) ^ 9433 = 23126025 := by
        calc
          (5 : ZMod 280150093) ^ 9433 = (5 : ZMod 280150093) ^ (4716 + 4716 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 4716 * (5 : ZMod 280150093) ^ 4716) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 23126025 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 280150093) ^ 18867 = 26407337 := by
        calc
          (5 : ZMod 280150093) ^ 18867 = (5 : ZMod 280150093) ^ (9433 + 9433 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 9433 * (5 : ZMod 280150093) ^ 9433) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 26407337 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 280150093) ^ 37735 = 105533472 := by
        calc
          (5 : ZMod 280150093) ^ 37735 = (5 : ZMod 280150093) ^ (18867 + 18867 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 18867 * (5 : ZMod 280150093) ^ 18867) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 105533472 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 280150093) ^ 75471 = 248537363 := by
        calc
          (5 : ZMod 280150093) ^ 75471 = (5 : ZMod 280150093) ^ (37735 + 37735 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 37735 * (5 : ZMod 280150093) ^ 37735) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 248537363 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 280150093) ^ 150942 = 119248929 := by
        calc
          (5 : ZMod 280150093) ^ 150942 = (5 : ZMod 280150093) ^ (75471 + 75471) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 75471 * (5 : ZMod 280150093) ^ 75471 := by rw [pow_add]
          _ = 119248929 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 280150093) ^ 301885 = 73970554 := by
        calc
          (5 : ZMod 280150093) ^ 301885 = (5 : ZMod 280150093) ^ (150942 + 150942 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 150942 * (5 : ZMod 280150093) ^ 150942) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 73970554 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 280150093) ^ 603771 = 79367500 := by
        calc
          (5 : ZMod 280150093) ^ 603771 = (5 : ZMod 280150093) ^ (301885 + 301885 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 301885 * (5 : ZMod 280150093) ^ 301885) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 79367500 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 280150093) ^ 1207543 = 8183150 := by
        calc
          (5 : ZMod 280150093) ^ 1207543 = (5 : ZMod 280150093) ^ (603771 + 603771 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 603771 * (5 : ZMod 280150093) ^ 603771) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 8183150 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 280150093) ^ 2415087 = 16864108 := by
        calc
          (5 : ZMod 280150093) ^ 2415087 = (5 : ZMod 280150093) ^ (1207543 + 1207543 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 1207543 * (5 : ZMod 280150093) ^ 1207543) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 16864108 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 280150093) ^ 4830174 = 129775505 := by
        calc
          (5 : ZMod 280150093) ^ 4830174 = (5 : ZMod 280150093) ^ (2415087 + 2415087) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 2415087 * (5 : ZMod 280150093) ^ 2415087 := by rw [pow_add]
          _ = 129775505 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 280150093) ^ 9660348 = 251607784 := by
        calc
          (5 : ZMod 280150093) ^ 9660348 = (5 : ZMod 280150093) ^ (4830174 + 4830174) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 4830174 * (5 : ZMod 280150093) ^ 4830174 := by rw [pow_add]
          _ = 251607784 := by rw [factor_2_22]; decide
      change (5 : ZMod 280150093) ^ 9660348 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (5 : ZMod 280150093) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 280150093) ^ 2 = 25 := by
        calc
          (5 : ZMod 280150093) ^ 2 = (5 : ZMod 280150093) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 1 * (5 : ZMod 280150093) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 280150093) ^ 4 = 625 := by
        calc
          (5 : ZMod 280150093) ^ 4 = (5 : ZMod 280150093) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 2 * (5 : ZMod 280150093) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 280150093) ^ 8 = 390625 := by
        calc
          (5 : ZMod 280150093) ^ 8 = (5 : ZMod 280150093) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 4 * (5 : ZMod 280150093) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 280150093) ^ 16 = 186240033 := by
        calc
          (5 : ZMod 280150093) ^ 16 = (5 : ZMod 280150093) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 8 * (5 : ZMod 280150093) ^ 8 := by rw [pow_add]
          _ = 186240033 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 280150093) ^ 32 = 215372156 := by
        calc
          (5 : ZMod 280150093) ^ 32 = (5 : ZMod 280150093) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 16 * (5 : ZMod 280150093) ^ 16 := by rw [pow_add]
          _ = 215372156 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 280150093) ^ 65 = 95955465 := by
        calc
          (5 : ZMod 280150093) ^ 65 = (5 : ZMod 280150093) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 32 * (5 : ZMod 280150093) ^ 32) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 95955465 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 280150093) ^ 130 = 206415577 := by
        calc
          (5 : ZMod 280150093) ^ 130 = (5 : ZMod 280150093) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 65 * (5 : ZMod 280150093) ^ 65 := by rw [pow_add]
          _ = 206415577 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 280150093) ^ 261 = 66372334 := by
        calc
          (5 : ZMod 280150093) ^ 261 = (5 : ZMod 280150093) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = ((5 : ZMod 280150093) ^ 130 * (5 : ZMod 280150093) ^ 130) * (5 : ZMod 280150093) := by rw [pow_succ, pow_add]
          _ = 66372334 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 280150093) ^ 522 = 187657015 := by
        calc
          (5 : ZMod 280150093) ^ 522 = (5 : ZMod 280150093) ^ (261 + 261) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 261 * (5 : ZMod 280150093) ^ 261 := by rw [pow_add]
          _ = 187657015 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 280150093) ^ 1044 = 34014435 := by
        calc
          (5 : ZMod 280150093) ^ 1044 = (5 : ZMod 280150093) ^ (522 + 522) :=
            congrArg (fun n : ℕ => (5 : ZMod 280150093) ^ n) (by norm_num)
          _ = (5 : ZMod 280150093) ^ 522 * (5 : ZMod 280150093) ^ 522 := by rw [pow_add]
          _ = 34014435 := by rw [factor_3_9]; decide
      change (5 : ZMod 280150093) ^ 1044 ≠ 1
      rw [factor_3_10]
      decide

#print axioms prime_lucas_280150093

end TotientTailPeriodKiller
end Erdos249257
