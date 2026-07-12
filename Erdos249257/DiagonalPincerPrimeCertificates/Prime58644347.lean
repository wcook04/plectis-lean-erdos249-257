import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_58644347 : Nat.Prime 58644347 := by
  apply lucas_primality 58644347 (2 : ZMod 58644347)
  ·
      have fermat_0 : (2 : ZMod 58644347) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 58644347) ^ 3 = 8 := by
        calc
          (2 : ZMod 58644347) ^ 3 = (2 : ZMod 58644347) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 1 * (2 : ZMod 58644347) ^ 1) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 58644347) ^ 6 = 64 := by
        calc
          (2 : ZMod 58644347) ^ 6 = (2 : ZMod 58644347) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 3 * (2 : ZMod 58644347) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 58644347) ^ 13 = 8192 := by
        calc
          (2 : ZMod 58644347) ^ 13 = (2 : ZMod 58644347) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 6 * (2 : ZMod 58644347) ^ 6) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 58644347) ^ 27 = 16929034 := by
        calc
          (2 : ZMod 58644347) ^ 27 = (2 : ZMod 58644347) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 13 * (2 : ZMod 58644347) ^ 13) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 16929034 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 58644347) ^ 55 = 49336930 := by
        calc
          (2 : ZMod 58644347) ^ 55 = (2 : ZMod 58644347) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 27 * (2 : ZMod 58644347) ^ 27) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 49336930 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 58644347) ^ 111 = 37219981 := by
        calc
          (2 : ZMod 58644347) ^ 111 = (2 : ZMod 58644347) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 55 * (2 : ZMod 58644347) ^ 55) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 37219981 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 58644347) ^ 223 = 37935312 := by
        calc
          (2 : ZMod 58644347) ^ 223 = (2 : ZMod 58644347) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 111 * (2 : ZMod 58644347) ^ 111) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 37935312 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 58644347) ^ 447 = 29856046 := by
        calc
          (2 : ZMod 58644347) ^ 447 = (2 : ZMod 58644347) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 223 * (2 : ZMod 58644347) ^ 223) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 29856046 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 58644347) ^ 894 = 22980923 := by
        calc
          (2 : ZMod 58644347) ^ 894 = (2 : ZMod 58644347) ^ (447 + 447) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 447 * (2 : ZMod 58644347) ^ 447 := by rw [pow_add]
          _ = 22980923 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 58644347) ^ 1789 = 22917325 := by
        calc
          (2 : ZMod 58644347) ^ 1789 = (2 : ZMod 58644347) ^ (894 + 894 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 894 * (2 : ZMod 58644347) ^ 894) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 22917325 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 58644347) ^ 3579 = 52752914 := by
        calc
          (2 : ZMod 58644347) ^ 3579 = (2 : ZMod 58644347) ^ (1789 + 1789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 1789 * (2 : ZMod 58644347) ^ 1789) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 52752914 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 58644347) ^ 7158 = 32799804 := by
        calc
          (2 : ZMod 58644347) ^ 7158 = (2 : ZMod 58644347) ^ (3579 + 3579) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 3579 * (2 : ZMod 58644347) ^ 3579 := by rw [pow_add]
          _ = 32799804 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 58644347) ^ 14317 = 54835431 := by
        calc
          (2 : ZMod 58644347) ^ 14317 = (2 : ZMod 58644347) ^ (7158 + 7158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 7158 * (2 : ZMod 58644347) ^ 7158) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 54835431 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 58644347) ^ 28634 = 50668114 := by
        calc
          (2 : ZMod 58644347) ^ 28634 = (2 : ZMod 58644347) ^ (14317 + 14317) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 14317 * (2 : ZMod 58644347) ^ 14317 := by rw [pow_add]
          _ = 50668114 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 58644347) ^ 57269 = 4699025 := by
        calc
          (2 : ZMod 58644347) ^ 57269 = (2 : ZMod 58644347) ^ (28634 + 28634 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 28634 * (2 : ZMod 58644347) ^ 28634) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 4699025 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 58644347) ^ 114539 = 15547676 := by
        calc
          (2 : ZMod 58644347) ^ 114539 = (2 : ZMod 58644347) ^ (57269 + 57269 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 57269 * (2 : ZMod 58644347) ^ 57269) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 15547676 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 58644347) ^ 229079 = 38639119 := by
        calc
          (2 : ZMod 58644347) ^ 229079 = (2 : ZMod 58644347) ^ (114539 + 114539 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 114539 * (2 : ZMod 58644347) ^ 114539) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 38639119 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 58644347) ^ 458158 = 8392963 := by
        calc
          (2 : ZMod 58644347) ^ 458158 = (2 : ZMod 58644347) ^ (229079 + 229079) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 229079 * (2 : ZMod 58644347) ^ 229079 := by rw [pow_add]
          _ = 8392963 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 58644347) ^ 916317 = 53911105 := by
        calc
          (2 : ZMod 58644347) ^ 916317 = (2 : ZMod 58644347) ^ (458158 + 458158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 458158 * (2 : ZMod 58644347) ^ 458158) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 53911105 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 58644347) ^ 1832635 = 4980125 := by
        calc
          (2 : ZMod 58644347) ^ 1832635 = (2 : ZMod 58644347) ^ (916317 + 916317 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 916317 * (2 : ZMod 58644347) ^ 916317) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 4980125 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 58644347) ^ 3665271 = 24719546 := by
        calc
          (2 : ZMod 58644347) ^ 3665271 = (2 : ZMod 58644347) ^ (1832635 + 1832635 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 1832635 * (2 : ZMod 58644347) ^ 1832635) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 24719546 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 58644347) ^ 7330543 = 18263025 := by
        calc
          (2 : ZMod 58644347) ^ 7330543 = (2 : ZMod 58644347) ^ (3665271 + 3665271 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 3665271 * (2 : ZMod 58644347) ^ 3665271) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 18263025 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 58644347) ^ 14661086 = 629841 := by
        calc
          (2 : ZMod 58644347) ^ 14661086 = (2 : ZMod 58644347) ^ (7330543 + 7330543) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 7330543 * (2 : ZMod 58644347) ^ 7330543 := by rw [pow_add]
          _ = 629841 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 58644347) ^ 29322173 = 58644346 := by
        calc
          (2 : ZMod 58644347) ^ 29322173 = (2 : ZMod 58644347) ^ (14661086 + 14661086 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 14661086 * (2 : ZMod 58644347) ^ 14661086) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 58644346 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 58644347) ^ 58644346 = 1 := by
        calc
          (2 : ZMod 58644347) ^ 58644346 = (2 : ZMod 58644347) ^ (29322173 + 29322173) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 29322173 * (2 : ZMod 58644347) ^ 29322173 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (43, 1), (107, 1), (6373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (43, 1), (107, 1), (6373, 1)] : List FactorBlock).map factorBlockValue).prod = 58644347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 58644347) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 58644347) ^ 3 = 8 := by
        calc
          (2 : ZMod 58644347) ^ 3 = (2 : ZMod 58644347) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 1 * (2 : ZMod 58644347) ^ 1) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 58644347) ^ 6 = 64 := by
        calc
          (2 : ZMod 58644347) ^ 6 = (2 : ZMod 58644347) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 3 * (2 : ZMod 58644347) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 58644347) ^ 13 = 8192 := by
        calc
          (2 : ZMod 58644347) ^ 13 = (2 : ZMod 58644347) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 6 * (2 : ZMod 58644347) ^ 6) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 58644347) ^ 27 = 16929034 := by
        calc
          (2 : ZMod 58644347) ^ 27 = (2 : ZMod 58644347) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 13 * (2 : ZMod 58644347) ^ 13) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 16929034 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 58644347) ^ 55 = 49336930 := by
        calc
          (2 : ZMod 58644347) ^ 55 = (2 : ZMod 58644347) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 27 * (2 : ZMod 58644347) ^ 27) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 49336930 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 58644347) ^ 111 = 37219981 := by
        calc
          (2 : ZMod 58644347) ^ 111 = (2 : ZMod 58644347) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 55 * (2 : ZMod 58644347) ^ 55) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 37219981 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 58644347) ^ 223 = 37935312 := by
        calc
          (2 : ZMod 58644347) ^ 223 = (2 : ZMod 58644347) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 111 * (2 : ZMod 58644347) ^ 111) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 37935312 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 58644347) ^ 447 = 29856046 := by
        calc
          (2 : ZMod 58644347) ^ 447 = (2 : ZMod 58644347) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 223 * (2 : ZMod 58644347) ^ 223) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 29856046 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 58644347) ^ 894 = 22980923 := by
        calc
          (2 : ZMod 58644347) ^ 894 = (2 : ZMod 58644347) ^ (447 + 447) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 447 * (2 : ZMod 58644347) ^ 447 := by rw [pow_add]
          _ = 22980923 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 58644347) ^ 1789 = 22917325 := by
        calc
          (2 : ZMod 58644347) ^ 1789 = (2 : ZMod 58644347) ^ (894 + 894 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 894 * (2 : ZMod 58644347) ^ 894) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 22917325 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 58644347) ^ 3579 = 52752914 := by
        calc
          (2 : ZMod 58644347) ^ 3579 = (2 : ZMod 58644347) ^ (1789 + 1789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 1789 * (2 : ZMod 58644347) ^ 1789) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 52752914 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 58644347) ^ 7158 = 32799804 := by
        calc
          (2 : ZMod 58644347) ^ 7158 = (2 : ZMod 58644347) ^ (3579 + 3579) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 3579 * (2 : ZMod 58644347) ^ 3579 := by rw [pow_add]
          _ = 32799804 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 58644347) ^ 14317 = 54835431 := by
        calc
          (2 : ZMod 58644347) ^ 14317 = (2 : ZMod 58644347) ^ (7158 + 7158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 7158 * (2 : ZMod 58644347) ^ 7158) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 54835431 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 58644347) ^ 28634 = 50668114 := by
        calc
          (2 : ZMod 58644347) ^ 28634 = (2 : ZMod 58644347) ^ (14317 + 14317) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 14317 * (2 : ZMod 58644347) ^ 14317 := by rw [pow_add]
          _ = 50668114 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 58644347) ^ 57269 = 4699025 := by
        calc
          (2 : ZMod 58644347) ^ 57269 = (2 : ZMod 58644347) ^ (28634 + 28634 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 28634 * (2 : ZMod 58644347) ^ 28634) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 4699025 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 58644347) ^ 114539 = 15547676 := by
        calc
          (2 : ZMod 58644347) ^ 114539 = (2 : ZMod 58644347) ^ (57269 + 57269 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 57269 * (2 : ZMod 58644347) ^ 57269) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 15547676 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 58644347) ^ 229079 = 38639119 := by
        calc
          (2 : ZMod 58644347) ^ 229079 = (2 : ZMod 58644347) ^ (114539 + 114539 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 114539 * (2 : ZMod 58644347) ^ 114539) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 38639119 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 58644347) ^ 458158 = 8392963 := by
        calc
          (2 : ZMod 58644347) ^ 458158 = (2 : ZMod 58644347) ^ (229079 + 229079) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 229079 * (2 : ZMod 58644347) ^ 229079 := by rw [pow_add]
          _ = 8392963 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 58644347) ^ 916317 = 53911105 := by
        calc
          (2 : ZMod 58644347) ^ 916317 = (2 : ZMod 58644347) ^ (458158 + 458158 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 458158 * (2 : ZMod 58644347) ^ 458158) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 53911105 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 58644347) ^ 1832635 = 4980125 := by
        calc
          (2 : ZMod 58644347) ^ 1832635 = (2 : ZMod 58644347) ^ (916317 + 916317 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 916317 * (2 : ZMod 58644347) ^ 916317) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 4980125 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 58644347) ^ 3665271 = 24719546 := by
        calc
          (2 : ZMod 58644347) ^ 3665271 = (2 : ZMod 58644347) ^ (1832635 + 1832635 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 1832635 * (2 : ZMod 58644347) ^ 1832635) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 24719546 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 58644347) ^ 7330543 = 18263025 := by
        calc
          (2 : ZMod 58644347) ^ 7330543 = (2 : ZMod 58644347) ^ (3665271 + 3665271 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 3665271 * (2 : ZMod 58644347) ^ 3665271) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 18263025 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 58644347) ^ 14661086 = 629841 := by
        calc
          (2 : ZMod 58644347) ^ 14661086 = (2 : ZMod 58644347) ^ (7330543 + 7330543) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 7330543 * (2 : ZMod 58644347) ^ 7330543 := by rw [pow_add]
          _ = 629841 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 58644347) ^ 29322173 = 58644346 := by
        calc
          (2 : ZMod 58644347) ^ 29322173 = (2 : ZMod 58644347) ^ (14661086 + 14661086 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 14661086 * (2 : ZMod 58644347) ^ 14661086) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 58644346 := by rw [factor_0_23]; decide
      change (2 : ZMod 58644347) ^ 29322173 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 58644347) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 58644347) ^ 2 = 4 := by
        calc
          (2 : ZMod 58644347) ^ 2 = (2 : ZMod 58644347) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 1 * (2 : ZMod 58644347) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 58644347) ^ 5 = 32 := by
        calc
          (2 : ZMod 58644347) ^ 5 = (2 : ZMod 58644347) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 2 * (2 : ZMod 58644347) ^ 2) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 58644347) ^ 10 = 1024 := by
        calc
          (2 : ZMod 58644347) ^ 10 = (2 : ZMod 58644347) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 5 * (2 : ZMod 58644347) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 58644347) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 58644347) ^ 20 = (2 : ZMod 58644347) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 10 * (2 : ZMod 58644347) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 58644347) ^ 41 = 36176093 := by
        calc
          (2 : ZMod 58644347) ^ 41 = (2 : ZMod 58644347) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 20 * (2 : ZMod 58644347) ^ 20) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 36176093 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 58644347) ^ 83 = 46704497 := by
        calc
          (2 : ZMod 58644347) ^ 83 = (2 : ZMod 58644347) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 41 * (2 : ZMod 58644347) ^ 41) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 46704497 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 58644347) ^ 166 = 8791525 := by
        calc
          (2 : ZMod 58644347) ^ 166 = (2 : ZMod 58644347) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 83 * (2 : ZMod 58644347) ^ 83 := by rw [pow_add]
          _ = 8791525 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 58644347) ^ 332 = 8253505 := by
        calc
          (2 : ZMod 58644347) ^ 332 = (2 : ZMod 58644347) ^ (166 + 166) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 166 * (2 : ZMod 58644347) ^ 166 := by rw [pow_add]
          _ = 8253505 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 58644347) ^ 665 = 19238754 := by
        calc
          (2 : ZMod 58644347) ^ 665 = (2 : ZMod 58644347) ^ (332 + 332 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 332 * (2 : ZMod 58644347) ^ 332) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 19238754 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 58644347) ^ 1331 = 46261306 := by
        calc
          (2 : ZMod 58644347) ^ 1331 = (2 : ZMod 58644347) ^ (665 + 665 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 665 * (2 : ZMod 58644347) ^ 665) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 46261306 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 58644347) ^ 2663 = 27710149 := by
        calc
          (2 : ZMod 58644347) ^ 2663 = (2 : ZMod 58644347) ^ (1331 + 1331 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 1331 * (2 : ZMod 58644347) ^ 1331) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 27710149 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 58644347) ^ 5327 = 37335193 := by
        calc
          (2 : ZMod 58644347) ^ 5327 = (2 : ZMod 58644347) ^ (2663 + 2663 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 2663 * (2 : ZMod 58644347) ^ 2663) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 37335193 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 58644347) ^ 10654 = 32169454 := by
        calc
          (2 : ZMod 58644347) ^ 10654 = (2 : ZMod 58644347) ^ (5327 + 5327) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 5327 * (2 : ZMod 58644347) ^ 5327 := by rw [pow_add]
          _ = 32169454 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 58644347) ^ 21309 = 52754974 := by
        calc
          (2 : ZMod 58644347) ^ 21309 = (2 : ZMod 58644347) ^ (10654 + 10654 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 10654 * (2 : ZMod 58644347) ^ 10654) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 52754974 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 58644347) ^ 42619 = 27553857 := by
        calc
          (2 : ZMod 58644347) ^ 42619 = (2 : ZMod 58644347) ^ (21309 + 21309 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 21309 * (2 : ZMod 58644347) ^ 21309) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 27553857 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 58644347) ^ 85238 = 41323219 := by
        calc
          (2 : ZMod 58644347) ^ 85238 = (2 : ZMod 58644347) ^ (42619 + 42619) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 42619 * (2 : ZMod 58644347) ^ 42619 := by rw [pow_add]
          _ = 41323219 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 58644347) ^ 170477 = 32248509 := by
        calc
          (2 : ZMod 58644347) ^ 170477 = (2 : ZMod 58644347) ^ (85238 + 85238 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 85238 * (2 : ZMod 58644347) ^ 85238) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 32248509 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 58644347) ^ 340955 = 2630985 := by
        calc
          (2 : ZMod 58644347) ^ 340955 = (2 : ZMod 58644347) ^ (170477 + 170477 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 170477 * (2 : ZMod 58644347) ^ 170477) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 2630985 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 58644347) ^ 681911 = 51788507 := by
        calc
          (2 : ZMod 58644347) ^ 681911 = (2 : ZMod 58644347) ^ (340955 + 340955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 340955 * (2 : ZMod 58644347) ^ 340955) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 51788507 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 58644347) ^ 1363822 = 36294652 := by
        calc
          (2 : ZMod 58644347) ^ 1363822 = (2 : ZMod 58644347) ^ (681911 + 681911) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 681911 * (2 : ZMod 58644347) ^ 681911 := by rw [pow_add]
          _ = 36294652 := by rw [factor_1_19]; decide
      change (2 : ZMod 58644347) ^ 1363822 ≠ 1
      rw [factor_1_20]
      decide
    ·
      have factor_2_0 : (2 : ZMod 58644347) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 58644347) ^ 2 = 4 := by
        calc
          (2 : ZMod 58644347) ^ 2 = (2 : ZMod 58644347) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 1 * (2 : ZMod 58644347) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 58644347) ^ 4 = 16 := by
        calc
          (2 : ZMod 58644347) ^ 4 = (2 : ZMod 58644347) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 2 * (2 : ZMod 58644347) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 58644347) ^ 8 = 256 := by
        calc
          (2 : ZMod 58644347) ^ 8 = (2 : ZMod 58644347) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 4 * (2 : ZMod 58644347) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 58644347) ^ 16 = 65536 := by
        calc
          (2 : ZMod 58644347) ^ 16 = (2 : ZMod 58644347) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 8 * (2 : ZMod 58644347) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 58644347) ^ 33 = 27859930 := by
        calc
          (2 : ZMod 58644347) ^ 33 = (2 : ZMod 58644347) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 16 * (2 : ZMod 58644347) ^ 16) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 27859930 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 58644347) ^ 66 = 56467106 := by
        calc
          (2 : ZMod 58644347) ^ 66 = (2 : ZMod 58644347) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 33 * (2 : ZMod 58644347) ^ 33 := by rw [pow_add]
          _ = 56467106 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 58644347) ^ 133 = 18386407 := by
        calc
          (2 : ZMod 58644347) ^ 133 = (2 : ZMod 58644347) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 66 * (2 : ZMod 58644347) ^ 66) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 18386407 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 58644347) ^ 267 = 41013819 := by
        calc
          (2 : ZMod 58644347) ^ 267 = (2 : ZMod 58644347) ^ (133 + 133 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 133 * (2 : ZMod 58644347) ^ 133) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 41013819 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 58644347) ^ 535 = 23163362 := by
        calc
          (2 : ZMod 58644347) ^ 535 = (2 : ZMod 58644347) ^ (267 + 267 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 267 * (2 : ZMod 58644347) ^ 267) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 23163362 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 58644347) ^ 1070 = 44691407 := by
        calc
          (2 : ZMod 58644347) ^ 1070 = (2 : ZMod 58644347) ^ (535 + 535) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 535 * (2 : ZMod 58644347) ^ 535 := by rw [pow_add]
          _ = 44691407 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 58644347) ^ 2140 = 22334697 := by
        calc
          (2 : ZMod 58644347) ^ 2140 = (2 : ZMod 58644347) ^ (1070 + 1070) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 1070 * (2 : ZMod 58644347) ^ 1070 := by rw [pow_add]
          _ = 22334697 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 58644347) ^ 4281 = 44499026 := by
        calc
          (2 : ZMod 58644347) ^ 4281 = (2 : ZMod 58644347) ^ (2140 + 2140 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 2140 * (2 : ZMod 58644347) ^ 2140) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 44499026 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 58644347) ^ 8563 = 43754479 := by
        calc
          (2 : ZMod 58644347) ^ 8563 = (2 : ZMod 58644347) ^ (4281 + 4281 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 4281 * (2 : ZMod 58644347) ^ 4281) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 43754479 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 58644347) ^ 17127 = 38214025 := by
        calc
          (2 : ZMod 58644347) ^ 17127 = (2 : ZMod 58644347) ^ (8563 + 8563 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 8563 * (2 : ZMod 58644347) ^ 8563) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 38214025 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 58644347) ^ 34254 = 25401575 := by
        calc
          (2 : ZMod 58644347) ^ 34254 = (2 : ZMod 58644347) ^ (17127 + 17127) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 17127 * (2 : ZMod 58644347) ^ 17127 := by rw [pow_add]
          _ = 25401575 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 58644347) ^ 68509 = 26800320 := by
        calc
          (2 : ZMod 58644347) ^ 68509 = (2 : ZMod 58644347) ^ (34254 + 34254 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 34254 * (2 : ZMod 58644347) ^ 34254) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 26800320 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 58644347) ^ 137019 = 29763574 := by
        calc
          (2 : ZMod 58644347) ^ 137019 = (2 : ZMod 58644347) ^ (68509 + 68509 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 68509 * (2 : ZMod 58644347) ^ 68509) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 29763574 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 58644347) ^ 274039 = 6439159 := by
        calc
          (2 : ZMod 58644347) ^ 274039 = (2 : ZMod 58644347) ^ (137019 + 137019 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 137019 * (2 : ZMod 58644347) ^ 137019) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 6439159 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 58644347) ^ 548078 = 42411341 := by
        calc
          (2 : ZMod 58644347) ^ 548078 = (2 : ZMod 58644347) ^ (274039 + 274039) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 274039 * (2 : ZMod 58644347) ^ 274039 := by rw [pow_add]
          _ = 42411341 := by rw [factor_2_18]; decide
      change (2 : ZMod 58644347) ^ 548078 ≠ 1
      rw [factor_2_19]
      decide
    ·
      have factor_3_0 : (2 : ZMod 58644347) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 58644347) ^ 2 = 4 := by
        calc
          (2 : ZMod 58644347) ^ 2 = (2 : ZMod 58644347) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 1 * (2 : ZMod 58644347) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 58644347) ^ 4 = 16 := by
        calc
          (2 : ZMod 58644347) ^ 4 = (2 : ZMod 58644347) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 2 * (2 : ZMod 58644347) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 58644347) ^ 8 = 256 := by
        calc
          (2 : ZMod 58644347) ^ 8 = (2 : ZMod 58644347) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 4 * (2 : ZMod 58644347) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 58644347) ^ 17 = 131072 := by
        calc
          (2 : ZMod 58644347) ^ 17 = (2 : ZMod 58644347) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 8 * (2 : ZMod 58644347) ^ 8) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 58644347) ^ 35 = 52795373 := by
        calc
          (2 : ZMod 58644347) ^ 35 = (2 : ZMod 58644347) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 17 * (2 : ZMod 58644347) ^ 17) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 52795373 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 58644347) ^ 71 = 47616982 := by
        calc
          (2 : ZMod 58644347) ^ 71 = (2 : ZMod 58644347) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 35 * (2 : ZMod 58644347) ^ 35) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 47616982 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 58644347) ^ 143 = 2845381 := by
        calc
          (2 : ZMod 58644347) ^ 143 = (2 : ZMod 58644347) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 71 * (2 : ZMod 58644347) ^ 71) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 2845381 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 58644347) ^ 287 = 36775805 := by
        calc
          (2 : ZMod 58644347) ^ 287 = (2 : ZMod 58644347) ^ (143 + 143 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 143 * (2 : ZMod 58644347) ^ 143) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 36775805 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 58644347) ^ 575 = 6069899 := by
        calc
          (2 : ZMod 58644347) ^ 575 = (2 : ZMod 58644347) ^ (287 + 287 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 287 * (2 : ZMod 58644347) ^ 287) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 6069899 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 58644347) ^ 1150 = 11001369 := by
        calc
          (2 : ZMod 58644347) ^ 1150 = (2 : ZMod 58644347) ^ (575 + 575) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 575 * (2 : ZMod 58644347) ^ 575 := by rw [pow_add]
          _ = 11001369 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 58644347) ^ 2300 = 33824255 := by
        calc
          (2 : ZMod 58644347) ^ 2300 = (2 : ZMod 58644347) ^ (1150 + 1150) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 1150 * (2 : ZMod 58644347) ^ 1150 := by rw [pow_add]
          _ = 33824255 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 58644347) ^ 4601 = 10634137 := by
        calc
          (2 : ZMod 58644347) ^ 4601 = (2 : ZMod 58644347) ^ (2300 + 2300 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = ((2 : ZMod 58644347) ^ 2300 * (2 : ZMod 58644347) ^ 2300) * (2 : ZMod 58644347) := by rw [pow_succ, pow_add]
          _ = 10634137 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 58644347) ^ 9202 = 37105117 := by
        calc
          (2 : ZMod 58644347) ^ 9202 = (2 : ZMod 58644347) ^ (4601 + 4601) :=
            congrArg (fun n : ℕ => (2 : ZMod 58644347) ^ n) (by norm_num)
          _ = (2 : ZMod 58644347) ^ 4601 * (2 : ZMod 58644347) ^ 4601 := by rw [pow_add]
          _ = 37105117 := by rw [factor_3_12]; decide
      change (2 : ZMod 58644347) ^ 9202 ≠ 1
      rw [factor_3_13]
      decide

#print axioms prime_lucas_58644347

end TotientTailPeriodKiller
end Erdos249257
