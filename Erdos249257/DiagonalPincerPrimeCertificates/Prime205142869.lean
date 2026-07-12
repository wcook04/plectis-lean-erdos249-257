import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_205142869 : Nat.Prime 205142869 := by
  apply lucas_primality 205142869 (6 : ZMod 205142869)
  ·
      have fermat_0 : (6 : ZMod 205142869) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 205142869) ^ 3 = 216 := by
        calc
          (6 : ZMod 205142869) ^ 3 = (6 : ZMod 205142869) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 1 * (6 : ZMod 205142869) ^ 1) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 205142869) ^ 6 = 46656 := by
        calc
          (6 : ZMod 205142869) ^ 6 = (6 : ZMod 205142869) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3 * (6 : ZMod 205142869) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 205142869) ^ 12 = 125353646 := by
        calc
          (6 : ZMod 205142869) ^ 12 = (6 : ZMod 205142869) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 6 * (6 : ZMod 205142869) ^ 6 := by rw [pow_add]
          _ = 125353646 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 205142869) ^ 24 = 8688281 := by
        calc
          (6 : ZMod 205142869) ^ 24 = (6 : ZMod 205142869) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 12 * (6 : ZMod 205142869) ^ 12 := by rw [pow_add]
          _ = 8688281 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 205142869) ^ 48 = 10371900 := by
        calc
          (6 : ZMod 205142869) ^ 48 = (6 : ZMod 205142869) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 24 * (6 : ZMod 205142869) ^ 24 := by rw [pow_add]
          _ = 10371900 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 205142869) ^ 97 = 27210042 := by
        calc
          (6 : ZMod 205142869) ^ 97 = (6 : ZMod 205142869) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 48 * (6 : ZMod 205142869) ^ 48) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 27210042 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 205142869) ^ 195 = 155944227 := by
        calc
          (6 : ZMod 205142869) ^ 195 = (6 : ZMod 205142869) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 97 * (6 : ZMod 205142869) ^ 97) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 155944227 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 205142869) ^ 391 = 122727234 := by
        calc
          (6 : ZMod 205142869) ^ 391 = (6 : ZMod 205142869) ^ (195 + 195 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 195 * (6 : ZMod 205142869) ^ 195) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 122727234 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 205142869) ^ 782 = 85574250 := by
        calc
          (6 : ZMod 205142869) ^ 782 = (6 : ZMod 205142869) ^ (391 + 391) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 391 * (6 : ZMod 205142869) ^ 391 := by rw [pow_add]
          _ = 85574250 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 205142869) ^ 1565 = 137085502 := by
        calc
          (6 : ZMod 205142869) ^ 1565 = (6 : ZMod 205142869) ^ (782 + 782 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 782 * (6 : ZMod 205142869) ^ 782) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 137085502 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 205142869) ^ 3130 = 64399805 := by
        calc
          (6 : ZMod 205142869) ^ 3130 = (6 : ZMod 205142869) ^ (1565 + 1565) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 1565 * (6 : ZMod 205142869) ^ 1565 := by rw [pow_add]
          _ = 64399805 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 205142869) ^ 6260 = 68324397 := by
        calc
          (6 : ZMod 205142869) ^ 6260 = (6 : ZMod 205142869) ^ (3130 + 3130) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3130 * (6 : ZMod 205142869) ^ 3130 := by rw [pow_add]
          _ = 68324397 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 205142869) ^ 12520 = 99021500 := by
        calc
          (6 : ZMod 205142869) ^ 12520 = (6 : ZMod 205142869) ^ (6260 + 6260) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 6260 * (6 : ZMod 205142869) ^ 6260 := by rw [pow_add]
          _ = 99021500 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 205142869) ^ 25041 = 138212549 := by
        calc
          (6 : ZMod 205142869) ^ 25041 = (6 : ZMod 205142869) ^ (12520 + 12520 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 12520 * (6 : ZMod 205142869) ^ 12520) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 138212549 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 205142869) ^ 50083 = 9709265 := by
        calc
          (6 : ZMod 205142869) ^ 50083 = (6 : ZMod 205142869) ^ (25041 + 25041 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 25041 * (6 : ZMod 205142869) ^ 25041) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 9709265 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 205142869) ^ 100167 = 68348895 := by
        calc
          (6 : ZMod 205142869) ^ 100167 = (6 : ZMod 205142869) ^ (50083 + 50083 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 50083 * (6 : ZMod 205142869) ^ 50083) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 68348895 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 205142869) ^ 200334 = 184563967 := by
        calc
          (6 : ZMod 205142869) ^ 200334 = (6 : ZMod 205142869) ^ (100167 + 100167) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 100167 * (6 : ZMod 205142869) ^ 100167 := by rw [pow_add]
          _ = 184563967 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 205142869) ^ 400669 = 76574016 := by
        calc
          (6 : ZMod 205142869) ^ 400669 = (6 : ZMod 205142869) ^ (200334 + 200334 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 200334 * (6 : ZMod 205142869) ^ 200334) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 76574016 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 205142869) ^ 801339 = 23596879 := by
        calc
          (6 : ZMod 205142869) ^ 801339 = (6 : ZMod 205142869) ^ (400669 + 400669 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 400669 * (6 : ZMod 205142869) ^ 400669) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 23596879 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 205142869) ^ 1602678 = 178928618 := by
        calc
          (6 : ZMod 205142869) ^ 1602678 = (6 : ZMod 205142869) ^ (801339 + 801339) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 801339 * (6 : ZMod 205142869) ^ 801339 := by rw [pow_add]
          _ = 178928618 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 205142869) ^ 3205357 = 135203317 := by
        calc
          (6 : ZMod 205142869) ^ 3205357 = (6 : ZMod 205142869) ^ (1602678 + 1602678 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 1602678 * (6 : ZMod 205142869) ^ 1602678) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 135203317 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 205142869) ^ 6410714 = 100946671 := by
        calc
          (6 : ZMod 205142869) ^ 6410714 = (6 : ZMod 205142869) ^ (3205357 + 3205357) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3205357 * (6 : ZMod 205142869) ^ 3205357 := by rw [pow_add]
          _ = 100946671 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 205142869) ^ 12821429 = 160241538 := by
        calc
          (6 : ZMod 205142869) ^ 12821429 = (6 : ZMod 205142869) ^ (6410714 + 6410714 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 6410714 * (6 : ZMod 205142869) ^ 6410714) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 160241538 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 205142869) ^ 25642858 = 179326129 := by
        calc
          (6 : ZMod 205142869) ^ 25642858 = (6 : ZMod 205142869) ^ (12821429 + 12821429) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 12821429 * (6 : ZMod 205142869) ^ 12821429 := by rw [pow_add]
          _ = 179326129 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 205142869) ^ 51285717 = 68509950 := by
        calc
          (6 : ZMod 205142869) ^ 51285717 = (6 : ZMod 205142869) ^ (25642858 + 25642858 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 25642858 * (6 : ZMod 205142869) ^ 25642858) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 68509950 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 205142869) ^ 102571434 = 205142868 := by
        calc
          (6 : ZMod 205142869) ^ 102571434 = (6 : ZMod 205142869) ^ (51285717 + 51285717) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 51285717 * (6 : ZMod 205142869) ^ 51285717 := by rw [pow_add]
          _ = 205142868 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 205142869) ^ 205142868 = 1 := by
        calc
          (6 : ZMod 205142869) ^ 205142868 = (6 : ZMod 205142869) ^ (102571434 + 102571434) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 102571434 * (6 : ZMod 205142869) ^ 102571434 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 4), (7, 1), (29, 1), (3119, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 4), (7, 1), (29, 1), (3119, 1)] : List FactorBlock).map factorBlockValue).prod = 205142869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 205142869) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 205142869) ^ 3 = 216 := by
        calc
          (6 : ZMod 205142869) ^ 3 = (6 : ZMod 205142869) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 1 * (6 : ZMod 205142869) ^ 1) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 205142869) ^ 6 = 46656 := by
        calc
          (6 : ZMod 205142869) ^ 6 = (6 : ZMod 205142869) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3 * (6 : ZMod 205142869) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 205142869) ^ 12 = 125353646 := by
        calc
          (6 : ZMod 205142869) ^ 12 = (6 : ZMod 205142869) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 6 * (6 : ZMod 205142869) ^ 6 := by rw [pow_add]
          _ = 125353646 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 205142869) ^ 24 = 8688281 := by
        calc
          (6 : ZMod 205142869) ^ 24 = (6 : ZMod 205142869) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 12 * (6 : ZMod 205142869) ^ 12 := by rw [pow_add]
          _ = 8688281 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 205142869) ^ 48 = 10371900 := by
        calc
          (6 : ZMod 205142869) ^ 48 = (6 : ZMod 205142869) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 24 * (6 : ZMod 205142869) ^ 24 := by rw [pow_add]
          _ = 10371900 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 205142869) ^ 97 = 27210042 := by
        calc
          (6 : ZMod 205142869) ^ 97 = (6 : ZMod 205142869) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 48 * (6 : ZMod 205142869) ^ 48) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 27210042 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 205142869) ^ 195 = 155944227 := by
        calc
          (6 : ZMod 205142869) ^ 195 = (6 : ZMod 205142869) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 97 * (6 : ZMod 205142869) ^ 97) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 155944227 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 205142869) ^ 391 = 122727234 := by
        calc
          (6 : ZMod 205142869) ^ 391 = (6 : ZMod 205142869) ^ (195 + 195 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 195 * (6 : ZMod 205142869) ^ 195) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 122727234 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 205142869) ^ 782 = 85574250 := by
        calc
          (6 : ZMod 205142869) ^ 782 = (6 : ZMod 205142869) ^ (391 + 391) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 391 * (6 : ZMod 205142869) ^ 391 := by rw [pow_add]
          _ = 85574250 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 205142869) ^ 1565 = 137085502 := by
        calc
          (6 : ZMod 205142869) ^ 1565 = (6 : ZMod 205142869) ^ (782 + 782 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 782 * (6 : ZMod 205142869) ^ 782) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 137085502 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 205142869) ^ 3130 = 64399805 := by
        calc
          (6 : ZMod 205142869) ^ 3130 = (6 : ZMod 205142869) ^ (1565 + 1565) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 1565 * (6 : ZMod 205142869) ^ 1565 := by rw [pow_add]
          _ = 64399805 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 205142869) ^ 6260 = 68324397 := by
        calc
          (6 : ZMod 205142869) ^ 6260 = (6 : ZMod 205142869) ^ (3130 + 3130) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3130 * (6 : ZMod 205142869) ^ 3130 := by rw [pow_add]
          _ = 68324397 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 205142869) ^ 12520 = 99021500 := by
        calc
          (6 : ZMod 205142869) ^ 12520 = (6 : ZMod 205142869) ^ (6260 + 6260) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 6260 * (6 : ZMod 205142869) ^ 6260 := by rw [pow_add]
          _ = 99021500 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 205142869) ^ 25041 = 138212549 := by
        calc
          (6 : ZMod 205142869) ^ 25041 = (6 : ZMod 205142869) ^ (12520 + 12520 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 12520 * (6 : ZMod 205142869) ^ 12520) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 138212549 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 205142869) ^ 50083 = 9709265 := by
        calc
          (6 : ZMod 205142869) ^ 50083 = (6 : ZMod 205142869) ^ (25041 + 25041 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 25041 * (6 : ZMod 205142869) ^ 25041) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 9709265 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 205142869) ^ 100167 = 68348895 := by
        calc
          (6 : ZMod 205142869) ^ 100167 = (6 : ZMod 205142869) ^ (50083 + 50083 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 50083 * (6 : ZMod 205142869) ^ 50083) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 68348895 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 205142869) ^ 200334 = 184563967 := by
        calc
          (6 : ZMod 205142869) ^ 200334 = (6 : ZMod 205142869) ^ (100167 + 100167) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 100167 * (6 : ZMod 205142869) ^ 100167 := by rw [pow_add]
          _ = 184563967 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 205142869) ^ 400669 = 76574016 := by
        calc
          (6 : ZMod 205142869) ^ 400669 = (6 : ZMod 205142869) ^ (200334 + 200334 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 200334 * (6 : ZMod 205142869) ^ 200334) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 76574016 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 205142869) ^ 801339 = 23596879 := by
        calc
          (6 : ZMod 205142869) ^ 801339 = (6 : ZMod 205142869) ^ (400669 + 400669 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 400669 * (6 : ZMod 205142869) ^ 400669) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 23596879 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 205142869) ^ 1602678 = 178928618 := by
        calc
          (6 : ZMod 205142869) ^ 1602678 = (6 : ZMod 205142869) ^ (801339 + 801339) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 801339 * (6 : ZMod 205142869) ^ 801339 := by rw [pow_add]
          _ = 178928618 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 205142869) ^ 3205357 = 135203317 := by
        calc
          (6 : ZMod 205142869) ^ 3205357 = (6 : ZMod 205142869) ^ (1602678 + 1602678 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 1602678 * (6 : ZMod 205142869) ^ 1602678) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 135203317 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 205142869) ^ 6410714 = 100946671 := by
        calc
          (6 : ZMod 205142869) ^ 6410714 = (6 : ZMod 205142869) ^ (3205357 + 3205357) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3205357 * (6 : ZMod 205142869) ^ 3205357 := by rw [pow_add]
          _ = 100946671 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 205142869) ^ 12821429 = 160241538 := by
        calc
          (6 : ZMod 205142869) ^ 12821429 = (6 : ZMod 205142869) ^ (6410714 + 6410714 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 6410714 * (6 : ZMod 205142869) ^ 6410714) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 160241538 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 205142869) ^ 25642858 = 179326129 := by
        calc
          (6 : ZMod 205142869) ^ 25642858 = (6 : ZMod 205142869) ^ (12821429 + 12821429) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 12821429 * (6 : ZMod 205142869) ^ 12821429 := by rw [pow_add]
          _ = 179326129 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 205142869) ^ 51285717 = 68509950 := by
        calc
          (6 : ZMod 205142869) ^ 51285717 = (6 : ZMod 205142869) ^ (25642858 + 25642858 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 25642858 * (6 : ZMod 205142869) ^ 25642858) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 68509950 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 205142869) ^ 102571434 = 205142868 := by
        calc
          (6 : ZMod 205142869) ^ 102571434 = (6 : ZMod 205142869) ^ (51285717 + 51285717) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 51285717 * (6 : ZMod 205142869) ^ 51285717 := by rw [pow_add]
          _ = 205142868 := by rw [factor_0_25]; decide
      change (6 : ZMod 205142869) ^ 102571434 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (6 : ZMod 205142869) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 205142869) ^ 2 = 36 := by
        calc
          (6 : ZMod 205142869) ^ 2 = (6 : ZMod 205142869) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 1 * (6 : ZMod 205142869) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 205142869) ^ 4 = 1296 := by
        calc
          (6 : ZMod 205142869) ^ 4 = (6 : ZMod 205142869) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 2 * (6 : ZMod 205142869) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 205142869) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 205142869) ^ 8 = (6 : ZMod 205142869) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 4 * (6 : ZMod 205142869) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 205142869) ^ 16 = 190315837 := by
        calc
          (6 : ZMod 205142869) ^ 16 = (6 : ZMod 205142869) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 8 * (6 : ZMod 205142869) ^ 8 := by rw [pow_add]
          _ = 190315837 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 205142869) ^ 32 = 137793781 := by
        calc
          (6 : ZMod 205142869) ^ 32 = (6 : ZMod 205142869) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 16 * (6 : ZMod 205142869) ^ 16 := by rw [pow_add]
          _ = 137793781 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 205142869) ^ 65 = 22698575 := by
        calc
          (6 : ZMod 205142869) ^ 65 = (6 : ZMod 205142869) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 32 * (6 : ZMod 205142869) ^ 32) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 22698575 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 205142869) ^ 130 = 170393758 := by
        calc
          (6 : ZMod 205142869) ^ 130 = (6 : ZMod 205142869) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 65 * (6 : ZMod 205142869) ^ 65 := by rw [pow_add]
          _ = 170393758 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 205142869) ^ 260 = 42640316 := by
        calc
          (6 : ZMod 205142869) ^ 260 = (6 : ZMod 205142869) ^ (130 + 130) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 130 * (6 : ZMod 205142869) ^ 130 := by rw [pow_add]
          _ = 42640316 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 205142869) ^ 521 = 104934693 := by
        calc
          (6 : ZMod 205142869) ^ 521 = (6 : ZMod 205142869) ^ (260 + 260 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 260 * (6 : ZMod 205142869) ^ 260) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 104934693 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 205142869) ^ 1043 = 164490087 := by
        calc
          (6 : ZMod 205142869) ^ 1043 = (6 : ZMod 205142869) ^ (521 + 521 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 521 * (6 : ZMod 205142869) ^ 521) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 164490087 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 205142869) ^ 2086 = 89388790 := by
        calc
          (6 : ZMod 205142869) ^ 2086 = (6 : ZMod 205142869) ^ (1043 + 1043) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 1043 * (6 : ZMod 205142869) ^ 1043 := by rw [pow_add]
          _ = 89388790 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 205142869) ^ 4173 = 9241800 := by
        calc
          (6 : ZMod 205142869) ^ 4173 = (6 : ZMod 205142869) ^ (2086 + 2086 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 2086 * (6 : ZMod 205142869) ^ 2086) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 9241800 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 205142869) ^ 8347 = 58962659 := by
        calc
          (6 : ZMod 205142869) ^ 8347 = (6 : ZMod 205142869) ^ (4173 + 4173 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 4173 * (6 : ZMod 205142869) ^ 4173) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 58962659 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 205142869) ^ 16694 = 183405040 := by
        calc
          (6 : ZMod 205142869) ^ 16694 = (6 : ZMod 205142869) ^ (8347 + 8347) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 8347 * (6 : ZMod 205142869) ^ 8347 := by rw [pow_add]
          _ = 183405040 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 205142869) ^ 33389 = 81355094 := by
        calc
          (6 : ZMod 205142869) ^ 33389 = (6 : ZMod 205142869) ^ (16694 + 16694 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 16694 * (6 : ZMod 205142869) ^ 16694) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 81355094 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 205142869) ^ 66778 = 158908794 := by
        calc
          (6 : ZMod 205142869) ^ 66778 = (6 : ZMod 205142869) ^ (33389 + 33389) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 33389 * (6 : ZMod 205142869) ^ 33389 := by rw [pow_add]
          _ = 158908794 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 205142869) ^ 133556 = 175554149 := by
        calc
          (6 : ZMod 205142869) ^ 133556 = (6 : ZMod 205142869) ^ (66778 + 66778) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 66778 * (6 : ZMod 205142869) ^ 66778 := by rw [pow_add]
          _ = 175554149 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 205142869) ^ 267113 = 158098320 := by
        calc
          (6 : ZMod 205142869) ^ 267113 = (6 : ZMod 205142869) ^ (133556 + 133556 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 133556 * (6 : ZMod 205142869) ^ 133556) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 158098320 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 205142869) ^ 534226 = 4406569 := by
        calc
          (6 : ZMod 205142869) ^ 534226 = (6 : ZMod 205142869) ^ (267113 + 267113) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 267113 * (6 : ZMod 205142869) ^ 267113 := by rw [pow_add]
          _ = 4406569 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 205142869) ^ 1068452 = 52086566 := by
        calc
          (6 : ZMod 205142869) ^ 1068452 = (6 : ZMod 205142869) ^ (534226 + 534226) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 534226 * (6 : ZMod 205142869) ^ 534226 := by rw [pow_add]
          _ = 52086566 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 205142869) ^ 2136904 = 18004736 := by
        calc
          (6 : ZMod 205142869) ^ 2136904 = (6 : ZMod 205142869) ^ (1068452 + 1068452) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 1068452 * (6 : ZMod 205142869) ^ 1068452 := by rw [pow_add]
          _ = 18004736 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 205142869) ^ 4273809 = 180442655 := by
        calc
          (6 : ZMod 205142869) ^ 4273809 = (6 : ZMod 205142869) ^ (2136904 + 2136904 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 2136904 * (6 : ZMod 205142869) ^ 2136904) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 180442655 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 205142869) ^ 8547619 = 21722522 := by
        calc
          (6 : ZMod 205142869) ^ 8547619 = (6 : ZMod 205142869) ^ (4273809 + 4273809 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 4273809 * (6 : ZMod 205142869) ^ 4273809) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 21722522 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 205142869) ^ 17095239 = 60600685 := by
        calc
          (6 : ZMod 205142869) ^ 17095239 = (6 : ZMod 205142869) ^ (8547619 + 8547619 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 8547619 * (6 : ZMod 205142869) ^ 8547619) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 60600685 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 205142869) ^ 34190478 = 203918374 := by
        calc
          (6 : ZMod 205142869) ^ 34190478 = (6 : ZMod 205142869) ^ (17095239 + 17095239) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 17095239 * (6 : ZMod 205142869) ^ 17095239 := by rw [pow_add]
          _ = 203918374 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 205142869) ^ 68380956 = 203918373 := by
        calc
          (6 : ZMod 205142869) ^ 68380956 = (6 : ZMod 205142869) ^ (34190478 + 34190478) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 34190478 * (6 : ZMod 205142869) ^ 34190478 := by rw [pow_add]
          _ = 203918373 := by rw [factor_1_25]; decide
      change (6 : ZMod 205142869) ^ 68380956 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (6 : ZMod 205142869) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 205142869) ^ 3 = 216 := by
        calc
          (6 : ZMod 205142869) ^ 3 = (6 : ZMod 205142869) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 1 * (6 : ZMod 205142869) ^ 1) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 205142869) ^ 6 = 46656 := by
        calc
          (6 : ZMod 205142869) ^ 6 = (6 : ZMod 205142869) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3 * (6 : ZMod 205142869) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 205142869) ^ 13 = 136693269 := by
        calc
          (6 : ZMod 205142869) ^ 13 = (6 : ZMod 205142869) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 6 * (6 : ZMod 205142869) ^ 6) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 136693269 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 205142869) ^ 27 = 30382875 := by
        calc
          (6 : ZMod 205142869) ^ 27 = (6 : ZMod 205142869) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 13 * (6 : ZMod 205142869) ^ 13) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 30382875 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 205142869) ^ 55 = 81173443 := by
        calc
          (6 : ZMod 205142869) ^ 55 = (6 : ZMod 205142869) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 27 * (6 : ZMod 205142869) ^ 27) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 81173443 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 205142869) ^ 111 = 172615266 := by
        calc
          (6 : ZMod 205142869) ^ 111 = (6 : ZMod 205142869) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 55 * (6 : ZMod 205142869) ^ 55) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 172615266 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 205142869) ^ 223 = 164341516 := by
        calc
          (6 : ZMod 205142869) ^ 223 = (6 : ZMod 205142869) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 111 * (6 : ZMod 205142869) ^ 111) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 164341516 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 205142869) ^ 447 = 141310962 := by
        calc
          (6 : ZMod 205142869) ^ 447 = (6 : ZMod 205142869) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 223 * (6 : ZMod 205142869) ^ 223) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 141310962 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 205142869) ^ 894 = 176894986 := by
        calc
          (6 : ZMod 205142869) ^ 894 = (6 : ZMod 205142869) ^ (447 + 447) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 447 * (6 : ZMod 205142869) ^ 447 := by rw [pow_add]
          _ = 176894986 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 205142869) ^ 1788 = 112432472 := by
        calc
          (6 : ZMod 205142869) ^ 1788 = (6 : ZMod 205142869) ^ (894 + 894) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 894 * (6 : ZMod 205142869) ^ 894 := by rw [pow_add]
          _ = 112432472 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 205142869) ^ 3577 = 196878780 := by
        calc
          (6 : ZMod 205142869) ^ 3577 = (6 : ZMod 205142869) ^ (1788 + 1788 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 1788 * (6 : ZMod 205142869) ^ 1788) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 196878780 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 205142869) ^ 7154 = 28766786 := by
        calc
          (6 : ZMod 205142869) ^ 7154 = (6 : ZMod 205142869) ^ (3577 + 3577) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3577 * (6 : ZMod 205142869) ^ 3577 := by rw [pow_add]
          _ = 28766786 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 205142869) ^ 14309 = 21063429 := by
        calc
          (6 : ZMod 205142869) ^ 14309 = (6 : ZMod 205142869) ^ (7154 + 7154 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 7154 * (6 : ZMod 205142869) ^ 7154) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 21063429 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 205142869) ^ 28619 = 117565668 := by
        calc
          (6 : ZMod 205142869) ^ 28619 = (6 : ZMod 205142869) ^ (14309 + 14309 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 14309 * (6 : ZMod 205142869) ^ 14309) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 117565668 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 205142869) ^ 57238 = 44257648 := by
        calc
          (6 : ZMod 205142869) ^ 57238 = (6 : ZMod 205142869) ^ (28619 + 28619) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 28619 * (6 : ZMod 205142869) ^ 28619 := by rw [pow_add]
          _ = 44257648 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 205142869) ^ 114477 = 52238616 := by
        calc
          (6 : ZMod 205142869) ^ 114477 = (6 : ZMod 205142869) ^ (57238 + 57238 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 57238 * (6 : ZMod 205142869) ^ 57238) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 52238616 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 205142869) ^ 228954 = 194725280 := by
        calc
          (6 : ZMod 205142869) ^ 228954 = (6 : ZMod 205142869) ^ (114477 + 114477) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 114477 * (6 : ZMod 205142869) ^ 114477 := by rw [pow_add]
          _ = 194725280 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 205142869) ^ 457908 = 44014458 := by
        calc
          (6 : ZMod 205142869) ^ 457908 = (6 : ZMod 205142869) ^ (228954 + 228954) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 228954 * (6 : ZMod 205142869) ^ 228954 := by rw [pow_add]
          _ = 44014458 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 205142869) ^ 915816 = 85631932 := by
        calc
          (6 : ZMod 205142869) ^ 915816 = (6 : ZMod 205142869) ^ (457908 + 457908) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 457908 * (6 : ZMod 205142869) ^ 457908 := by rw [pow_add]
          _ = 85631932 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 205142869) ^ 1831632 = 28505004 := by
        calc
          (6 : ZMod 205142869) ^ 1831632 = (6 : ZMod 205142869) ^ (915816 + 915816) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 915816 * (6 : ZMod 205142869) ^ 915816 := by rw [pow_add]
          _ = 28505004 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 205142869) ^ 3663265 = 57598463 := by
        calc
          (6 : ZMod 205142869) ^ 3663265 = (6 : ZMod 205142869) ^ (1831632 + 1831632 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 1831632 * (6 : ZMod 205142869) ^ 1831632) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 57598463 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 205142869) ^ 7326531 = 102961898 := by
        calc
          (6 : ZMod 205142869) ^ 7326531 = (6 : ZMod 205142869) ^ (3663265 + 3663265 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 3663265 * (6 : ZMod 205142869) ^ 3663265) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 102961898 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 205142869) ^ 14653062 = 194450317 := by
        calc
          (6 : ZMod 205142869) ^ 14653062 = (6 : ZMod 205142869) ^ (7326531 + 7326531) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 7326531 * (6 : ZMod 205142869) ^ 7326531 := by rw [pow_add]
          _ = 194450317 := by rw [factor_2_22]; decide
      have factor_2_24 : (6 : ZMod 205142869) ^ 29306124 = 34235886 := by
        calc
          (6 : ZMod 205142869) ^ 29306124 = (6 : ZMod 205142869) ^ (14653062 + 14653062) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 14653062 * (6 : ZMod 205142869) ^ 14653062 := by rw [pow_add]
          _ = 34235886 := by rw [factor_2_23]; decide
      change (6 : ZMod 205142869) ^ 29306124 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (6 : ZMod 205142869) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 205142869) ^ 3 = 216 := by
        calc
          (6 : ZMod 205142869) ^ 3 = (6 : ZMod 205142869) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 1 * (6 : ZMod 205142869) ^ 1) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 205142869) ^ 6 = 46656 := by
        calc
          (6 : ZMod 205142869) ^ 6 = (6 : ZMod 205142869) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3 * (6 : ZMod 205142869) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 205142869) ^ 13 = 136693269 := by
        calc
          (6 : ZMod 205142869) ^ 13 = (6 : ZMod 205142869) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 6 * (6 : ZMod 205142869) ^ 6) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 136693269 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 205142869) ^ 26 = 107635247 := by
        calc
          (6 : ZMod 205142869) ^ 26 = (6 : ZMod 205142869) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 13 * (6 : ZMod 205142869) ^ 13 := by rw [pow_add]
          _ = 107635247 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 205142869) ^ 53 = 30746883 := by
        calc
          (6 : ZMod 205142869) ^ 53 = (6 : ZMod 205142869) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 26 * (6 : ZMod 205142869) ^ 26) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 30746883 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 205142869) ^ 107 = 145442723 := by
        calc
          (6 : ZMod 205142869) ^ 107 = (6 : ZMod 205142869) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 53 * (6 : ZMod 205142869) ^ 53) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 145442723 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 205142869) ^ 215 = 95650286 := by
        calc
          (6 : ZMod 205142869) ^ 215 = (6 : ZMod 205142869) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 107 * (6 : ZMod 205142869) ^ 107) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 95650286 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 205142869) ^ 431 = 106456250 := by
        calc
          (6 : ZMod 205142869) ^ 431 = (6 : ZMod 205142869) ^ (215 + 215 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 215 * (6 : ZMod 205142869) ^ 215) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 106456250 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 205142869) ^ 863 = 173580469 := by
        calc
          (6 : ZMod 205142869) ^ 863 = (6 : ZMod 205142869) ^ (431 + 431 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 431 * (6 : ZMod 205142869) ^ 431) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 173580469 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 205142869) ^ 1727 = 29086361 := by
        calc
          (6 : ZMod 205142869) ^ 1727 = (6 : ZMod 205142869) ^ (863 + 863 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 863 * (6 : ZMod 205142869) ^ 863) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 29086361 := by rw [factor_3_9]; decide
      have factor_3_11 : (6 : ZMod 205142869) ^ 3454 = 24465906 := by
        calc
          (6 : ZMod 205142869) ^ 3454 = (6 : ZMod 205142869) ^ (1727 + 1727) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 1727 * (6 : ZMod 205142869) ^ 1727 := by rw [pow_add]
          _ = 24465906 := by rw [factor_3_10]; decide
      have factor_3_12 : (6 : ZMod 205142869) ^ 6908 = 128088937 := by
        calc
          (6 : ZMod 205142869) ^ 6908 = (6 : ZMod 205142869) ^ (3454 + 3454) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3454 * (6 : ZMod 205142869) ^ 3454 := by rw [pow_add]
          _ = 128088937 := by rw [factor_3_11]; decide
      have factor_3_13 : (6 : ZMod 205142869) ^ 13816 = 132916103 := by
        calc
          (6 : ZMod 205142869) ^ 13816 = (6 : ZMod 205142869) ^ (6908 + 6908) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 6908 * (6 : ZMod 205142869) ^ 6908 := by rw [pow_add]
          _ = 132916103 := by rw [factor_3_12]; decide
      have factor_3_14 : (6 : ZMod 205142869) ^ 27632 = 112153238 := by
        calc
          (6 : ZMod 205142869) ^ 27632 = (6 : ZMod 205142869) ^ (13816 + 13816) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 13816 * (6 : ZMod 205142869) ^ 13816 := by rw [pow_add]
          _ = 112153238 := by rw [factor_3_13]; decide
      have factor_3_15 : (6 : ZMod 205142869) ^ 55264 = 36577421 := by
        calc
          (6 : ZMod 205142869) ^ 55264 = (6 : ZMod 205142869) ^ (27632 + 27632) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 27632 * (6 : ZMod 205142869) ^ 27632 := by rw [pow_add]
          _ = 36577421 := by rw [factor_3_14]; decide
      have factor_3_16 : (6 : ZMod 205142869) ^ 110529 = 139799839 := by
        calc
          (6 : ZMod 205142869) ^ 110529 = (6 : ZMod 205142869) ^ (55264 + 55264 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 55264 * (6 : ZMod 205142869) ^ 55264) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 139799839 := by rw [factor_3_15]; decide
      have factor_3_17 : (6 : ZMod 205142869) ^ 221059 = 37335216 := by
        calc
          (6 : ZMod 205142869) ^ 221059 = (6 : ZMod 205142869) ^ (110529 + 110529 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 110529 * (6 : ZMod 205142869) ^ 110529) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 37335216 := by rw [factor_3_16]; decide
      have factor_3_18 : (6 : ZMod 205142869) ^ 442118 = 48056102 := by
        calc
          (6 : ZMod 205142869) ^ 442118 = (6 : ZMod 205142869) ^ (221059 + 221059) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 221059 * (6 : ZMod 205142869) ^ 221059 := by rw [pow_add]
          _ = 48056102 := by rw [factor_3_17]; decide
      have factor_3_19 : (6 : ZMod 205142869) ^ 884236 = 66524450 := by
        calc
          (6 : ZMod 205142869) ^ 884236 = (6 : ZMod 205142869) ^ (442118 + 442118) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 442118 * (6 : ZMod 205142869) ^ 442118 := by rw [pow_add]
          _ = 66524450 := by rw [factor_3_18]; decide
      have factor_3_20 : (6 : ZMod 205142869) ^ 1768473 = 130922783 := by
        calc
          (6 : ZMod 205142869) ^ 1768473 = (6 : ZMod 205142869) ^ (884236 + 884236 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 884236 * (6 : ZMod 205142869) ^ 884236) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 130922783 := by rw [factor_3_19]; decide
      have factor_3_21 : (6 : ZMod 205142869) ^ 3536946 = 120595044 := by
        calc
          (6 : ZMod 205142869) ^ 3536946 = (6 : ZMod 205142869) ^ (1768473 + 1768473) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 1768473 * (6 : ZMod 205142869) ^ 1768473 := by rw [pow_add]
          _ = 120595044 := by rw [factor_3_20]; decide
      have factor_3_22 : (6 : ZMod 205142869) ^ 7073892 = 150489465 := by
        calc
          (6 : ZMod 205142869) ^ 7073892 = (6 : ZMod 205142869) ^ (3536946 + 3536946) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 3536946 * (6 : ZMod 205142869) ^ 3536946 := by rw [pow_add]
          _ = 150489465 := by rw [factor_3_21]; decide
      change (6 : ZMod 205142869) ^ 7073892 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (6 : ZMod 205142869) ^ 1 = 6 := by norm_num
      have factor_4_1 : (6 : ZMod 205142869) ^ 2 = 36 := by
        calc
          (6 : ZMod 205142869) ^ 2 = (6 : ZMod 205142869) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 1 * (6 : ZMod 205142869) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_4_0]; decide
      have factor_4_2 : (6 : ZMod 205142869) ^ 4 = 1296 := by
        calc
          (6 : ZMod 205142869) ^ 4 = (6 : ZMod 205142869) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 2 * (6 : ZMod 205142869) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_4_1]; decide
      have factor_4_3 : (6 : ZMod 205142869) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 205142869) ^ 8 = (6 : ZMod 205142869) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 4 * (6 : ZMod 205142869) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_4_2]; decide
      have factor_4_4 : (6 : ZMod 205142869) ^ 16 = 190315837 := by
        calc
          (6 : ZMod 205142869) ^ 16 = (6 : ZMod 205142869) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 8 * (6 : ZMod 205142869) ^ 8 := by rw [pow_add]
          _ = 190315837 := by rw [factor_4_3]; decide
      have factor_4_5 : (6 : ZMod 205142869) ^ 32 = 137793781 := by
        calc
          (6 : ZMod 205142869) ^ 32 = (6 : ZMod 205142869) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 16 * (6 : ZMod 205142869) ^ 16 := by rw [pow_add]
          _ = 137793781 := by rw [factor_4_4]; decide
      have factor_4_6 : (6 : ZMod 205142869) ^ 64 = 37973574 := by
        calc
          (6 : ZMod 205142869) ^ 64 = (6 : ZMod 205142869) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 32 * (6 : ZMod 205142869) ^ 32 := by rw [pow_add]
          _ = 37973574 := by rw [factor_4_5]; decide
      have factor_4_7 : (6 : ZMod 205142869) ^ 128 = 16129986 := by
        calc
          (6 : ZMod 205142869) ^ 128 = (6 : ZMod 205142869) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 64 * (6 : ZMod 205142869) ^ 64 := by rw [pow_add]
          _ = 16129986 := by rw [factor_4_6]; decide
      have factor_4_8 : (6 : ZMod 205142869) ^ 256 = 107036435 := by
        calc
          (6 : ZMod 205142869) ^ 256 = (6 : ZMod 205142869) ^ (128 + 128) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 128 * (6 : ZMod 205142869) ^ 128 := by rw [pow_add]
          _ = 107036435 := by rw [factor_4_7]; decide
      have factor_4_9 : (6 : ZMod 205142869) ^ 513 = 108447619 := by
        calc
          (6 : ZMod 205142869) ^ 513 = (6 : ZMod 205142869) ^ (256 + 256 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 256 * (6 : ZMod 205142869) ^ 256) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 108447619 := by rw [factor_4_8]; decide
      have factor_4_10 : (6 : ZMod 205142869) ^ 1027 = 97407803 := by
        calc
          (6 : ZMod 205142869) ^ 1027 = (6 : ZMod 205142869) ^ (513 + 513 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 513 * (6 : ZMod 205142869) ^ 513) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 97407803 := by rw [factor_4_9]; decide
      have factor_4_11 : (6 : ZMod 205142869) ^ 2055 = 29217228 := by
        calc
          (6 : ZMod 205142869) ^ 2055 = (6 : ZMod 205142869) ^ (1027 + 1027 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 1027 * (6 : ZMod 205142869) ^ 1027) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 29217228 := by rw [factor_4_10]; decide
      have factor_4_12 : (6 : ZMod 205142869) ^ 4110 = 161520852 := by
        calc
          (6 : ZMod 205142869) ^ 4110 = (6 : ZMod 205142869) ^ (2055 + 2055) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 2055 * (6 : ZMod 205142869) ^ 2055 := by rw [pow_add]
          _ = 161520852 := by rw [factor_4_11]; decide
      have factor_4_13 : (6 : ZMod 205142869) ^ 8221 = 29834366 := by
        calc
          (6 : ZMod 205142869) ^ 8221 = (6 : ZMod 205142869) ^ (4110 + 4110 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 4110 * (6 : ZMod 205142869) ^ 4110) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 29834366 := by rw [factor_4_12]; decide
      have factor_4_14 : (6 : ZMod 205142869) ^ 16443 = 157908879 := by
        calc
          (6 : ZMod 205142869) ^ 16443 = (6 : ZMod 205142869) ^ (8221 + 8221 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = ((6 : ZMod 205142869) ^ 8221 * (6 : ZMod 205142869) ^ 8221) * (6 : ZMod 205142869) := by rw [pow_succ, pow_add]
          _ = 157908879 := by rw [factor_4_13]; decide
      have factor_4_15 : (6 : ZMod 205142869) ^ 32886 = 76652390 := by
        calc
          (6 : ZMod 205142869) ^ 32886 = (6 : ZMod 205142869) ^ (16443 + 16443) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 16443 * (6 : ZMod 205142869) ^ 16443 := by rw [pow_add]
          _ = 76652390 := by rw [factor_4_14]; decide
      have factor_4_16 : (6 : ZMod 205142869) ^ 65772 = 77677788 := by
        calc
          (6 : ZMod 205142869) ^ 65772 = (6 : ZMod 205142869) ^ (32886 + 32886) :=
            congrArg (fun n : ℕ => (6 : ZMod 205142869) ^ n) (by norm_num)
          _ = (6 : ZMod 205142869) ^ 32886 * (6 : ZMod 205142869) ^ 32886 := by rw [pow_add]
          _ = 77677788 := by rw [factor_4_15]; decide
      change (6 : ZMod 205142869) ^ 65772 ≠ 1
      rw [factor_4_16]
      decide

#print axioms prime_lucas_205142869

end TotientTailPeriodKiller
end Erdos249257
