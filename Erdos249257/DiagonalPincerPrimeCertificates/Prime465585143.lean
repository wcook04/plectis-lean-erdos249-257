import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=19 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000

theorem prime_lucas_465585143 : Nat.Prime 465585143 := by
  apply lucas_primality 465585143 (5 : ZMod 465585143)
  ·
      have fermat_0 : (5 : ZMod 465585143) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 465585143) ^ 3 = 125 := by
        calc
          (5 : ZMod 465585143) ^ 3 = (5 : ZMod 465585143) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 1 * (5 : ZMod 465585143) ^ 1) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 465585143) ^ 6 = 15625 := by
        calc
          (5 : ZMod 465585143) ^ 6 = (5 : ZMod 465585143) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 3 * (5 : ZMod 465585143) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 465585143) ^ 13 = 289532839 := by
        calc
          (5 : ZMod 465585143) ^ 13 = (5 : ZMod 465585143) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 6 * (5 : ZMod 465585143) ^ 6) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 289532839 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 465585143) ^ 27 = 174926307 := by
        calc
          (5 : ZMod 465585143) ^ 27 = (5 : ZMod 465585143) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 13 * (5 : ZMod 465585143) ^ 13) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 174926307 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 465585143) ^ 55 = 198221205 := by
        calc
          (5 : ZMod 465585143) ^ 55 = (5 : ZMod 465585143) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 27 * (5 : ZMod 465585143) ^ 27) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 198221205 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 465585143) ^ 111 = 439528720 := by
        calc
          (5 : ZMod 465585143) ^ 111 = (5 : ZMod 465585143) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 55 * (5 : ZMod 465585143) ^ 55) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 439528720 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 465585143) ^ 222 = 438286037 := by
        calc
          (5 : ZMod 465585143) ^ 222 = (5 : ZMod 465585143) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 111 * (5 : ZMod 465585143) ^ 111 := by rw [pow_add]
          _ = 438286037 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 465585143) ^ 444 = 1330571 := by
        calc
          (5 : ZMod 465585143) ^ 444 = (5 : ZMod 465585143) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 222 * (5 : ZMod 465585143) ^ 222 := by rw [pow_add]
          _ = 1330571 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 465585143) ^ 888 = 264472355 := by
        calc
          (5 : ZMod 465585143) ^ 888 = (5 : ZMod 465585143) ^ (444 + 444) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 444 * (5 : ZMod 465585143) ^ 444 := by rw [pow_add]
          _ = 264472355 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 465585143) ^ 1776 = 448529503 := by
        calc
          (5 : ZMod 465585143) ^ 1776 = (5 : ZMod 465585143) ^ (888 + 888) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 888 * (5 : ZMod 465585143) ^ 888 := by rw [pow_add]
          _ = 448529503 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 465585143) ^ 3552 = 51974058 := by
        calc
          (5 : ZMod 465585143) ^ 3552 = (5 : ZMod 465585143) ^ (1776 + 1776) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 1776 * (5 : ZMod 465585143) ^ 1776 := by rw [pow_add]
          _ = 51974058 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 465585143) ^ 7104 = 53388228 := by
        calc
          (5 : ZMod 465585143) ^ 7104 = (5 : ZMod 465585143) ^ (3552 + 3552) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 3552 * (5 : ZMod 465585143) ^ 3552 := by rw [pow_add]
          _ = 53388228 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 465585143) ^ 14208 = 420821987 := by
        calc
          (5 : ZMod 465585143) ^ 14208 = (5 : ZMod 465585143) ^ (7104 + 7104) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 7104 * (5 : ZMod 465585143) ^ 7104 := by rw [pow_add]
          _ = 420821987 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 465585143) ^ 28417 = 257564178 := by
        calc
          (5 : ZMod 465585143) ^ 28417 = (5 : ZMod 465585143) ^ (14208 + 14208 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 14208 * (5 : ZMod 465585143) ^ 14208) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 257564178 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 465585143) ^ 56834 = 232630845 := by
        calc
          (5 : ZMod 465585143) ^ 56834 = (5 : ZMod 465585143) ^ (28417 + 28417) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 28417 * (5 : ZMod 465585143) ^ 28417 := by rw [pow_add]
          _ = 232630845 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 465585143) ^ 113668 = 199089080 := by
        calc
          (5 : ZMod 465585143) ^ 113668 = (5 : ZMod 465585143) ^ (56834 + 56834) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 56834 * (5 : ZMod 465585143) ^ 56834 := by rw [pow_add]
          _ = 199089080 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 465585143) ^ 227336 = 135498318 := by
        calc
          (5 : ZMod 465585143) ^ 227336 = (5 : ZMod 465585143) ^ (113668 + 113668) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 113668 * (5 : ZMod 465585143) ^ 113668 := by rw [pow_add]
          _ = 135498318 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 465585143) ^ 454672 = 440870009 := by
        calc
          (5 : ZMod 465585143) ^ 454672 = (5 : ZMod 465585143) ^ (227336 + 227336) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 227336 * (5 : ZMod 465585143) ^ 227336 := by rw [pow_add]
          _ = 440870009 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 465585143) ^ 909345 = 57134938 := by
        calc
          (5 : ZMod 465585143) ^ 909345 = (5 : ZMod 465585143) ^ (454672 + 454672 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 454672 * (5 : ZMod 465585143) ^ 454672) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 57134938 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 465585143) ^ 1818691 = 379552224 := by
        calc
          (5 : ZMod 465585143) ^ 1818691 = (5 : ZMod 465585143) ^ (909345 + 909345 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 909345 * (5 : ZMod 465585143) ^ 909345) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 379552224 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 465585143) ^ 3637383 = 307804555 := by
        calc
          (5 : ZMod 465585143) ^ 3637383 = (5 : ZMod 465585143) ^ (1818691 + 1818691 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 1818691 * (5 : ZMod 465585143) ^ 1818691) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 307804555 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 465585143) ^ 7274767 = 64148624 := by
        calc
          (5 : ZMod 465585143) ^ 7274767 = (5 : ZMod 465585143) ^ (3637383 + 3637383 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 3637383 * (5 : ZMod 465585143) ^ 3637383) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 64148624 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 465585143) ^ 14549535 = 376907995 := by
        calc
          (5 : ZMod 465585143) ^ 14549535 = (5 : ZMod 465585143) ^ (7274767 + 7274767 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 7274767 * (5 : ZMod 465585143) ^ 7274767) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 376907995 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 465585143) ^ 29099071 = 372512811 := by
        calc
          (5 : ZMod 465585143) ^ 29099071 = (5 : ZMod 465585143) ^ (14549535 + 14549535 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 14549535 * (5 : ZMod 465585143) ^ 14549535) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 372512811 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 465585143) ^ 58198142 = 172692291 := by
        calc
          (5 : ZMod 465585143) ^ 58198142 = (5 : ZMod 465585143) ^ (29099071 + 29099071) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 29099071 * (5 : ZMod 465585143) ^ 29099071 := by rw [pow_add]
          _ = 172692291 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 465585143) ^ 116396285 = 130572206 := by
        calc
          (5 : ZMod 465585143) ^ 116396285 = (5 : ZMod 465585143) ^ (58198142 + 58198142 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 58198142 * (5 : ZMod 465585143) ^ 58198142) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 130572206 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 465585143) ^ 232792571 = 465585142 := by
        calc
          (5 : ZMod 465585143) ^ 232792571 = (5 : ZMod 465585143) ^ (116396285 + 116396285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 116396285 * (5 : ZMod 465585143) ^ 116396285) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 465585142 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 465585143) ^ 465585142 = 1 := by
        calc
          (5 : ZMod 465585143) ^ 465585142 = (5 : ZMod 465585143) ^ (232792571 + 232792571) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 232792571 * (5 : ZMod 465585143) ^ 232792571 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (2131, 1), (9931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (2131, 1), (9931, 1)] : List FactorBlock).map factorBlockValue).prod = 465585143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 465585143) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 465585143) ^ 3 = 125 := by
        calc
          (5 : ZMod 465585143) ^ 3 = (5 : ZMod 465585143) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 1 * (5 : ZMod 465585143) ^ 1) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 465585143) ^ 6 = 15625 := by
        calc
          (5 : ZMod 465585143) ^ 6 = (5 : ZMod 465585143) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 3 * (5 : ZMod 465585143) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 465585143) ^ 13 = 289532839 := by
        calc
          (5 : ZMod 465585143) ^ 13 = (5 : ZMod 465585143) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 6 * (5 : ZMod 465585143) ^ 6) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 289532839 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 465585143) ^ 27 = 174926307 := by
        calc
          (5 : ZMod 465585143) ^ 27 = (5 : ZMod 465585143) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 13 * (5 : ZMod 465585143) ^ 13) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 174926307 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 465585143) ^ 55 = 198221205 := by
        calc
          (5 : ZMod 465585143) ^ 55 = (5 : ZMod 465585143) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 27 * (5 : ZMod 465585143) ^ 27) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 198221205 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 465585143) ^ 111 = 439528720 := by
        calc
          (5 : ZMod 465585143) ^ 111 = (5 : ZMod 465585143) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 55 * (5 : ZMod 465585143) ^ 55) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 439528720 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 465585143) ^ 222 = 438286037 := by
        calc
          (5 : ZMod 465585143) ^ 222 = (5 : ZMod 465585143) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 111 * (5 : ZMod 465585143) ^ 111 := by rw [pow_add]
          _ = 438286037 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 465585143) ^ 444 = 1330571 := by
        calc
          (5 : ZMod 465585143) ^ 444 = (5 : ZMod 465585143) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 222 * (5 : ZMod 465585143) ^ 222 := by rw [pow_add]
          _ = 1330571 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 465585143) ^ 888 = 264472355 := by
        calc
          (5 : ZMod 465585143) ^ 888 = (5 : ZMod 465585143) ^ (444 + 444) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 444 * (5 : ZMod 465585143) ^ 444 := by rw [pow_add]
          _ = 264472355 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 465585143) ^ 1776 = 448529503 := by
        calc
          (5 : ZMod 465585143) ^ 1776 = (5 : ZMod 465585143) ^ (888 + 888) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 888 * (5 : ZMod 465585143) ^ 888 := by rw [pow_add]
          _ = 448529503 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 465585143) ^ 3552 = 51974058 := by
        calc
          (5 : ZMod 465585143) ^ 3552 = (5 : ZMod 465585143) ^ (1776 + 1776) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 1776 * (5 : ZMod 465585143) ^ 1776 := by rw [pow_add]
          _ = 51974058 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 465585143) ^ 7104 = 53388228 := by
        calc
          (5 : ZMod 465585143) ^ 7104 = (5 : ZMod 465585143) ^ (3552 + 3552) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 3552 * (5 : ZMod 465585143) ^ 3552 := by rw [pow_add]
          _ = 53388228 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 465585143) ^ 14208 = 420821987 := by
        calc
          (5 : ZMod 465585143) ^ 14208 = (5 : ZMod 465585143) ^ (7104 + 7104) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 7104 * (5 : ZMod 465585143) ^ 7104 := by rw [pow_add]
          _ = 420821987 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 465585143) ^ 28417 = 257564178 := by
        calc
          (5 : ZMod 465585143) ^ 28417 = (5 : ZMod 465585143) ^ (14208 + 14208 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 14208 * (5 : ZMod 465585143) ^ 14208) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 257564178 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 465585143) ^ 56834 = 232630845 := by
        calc
          (5 : ZMod 465585143) ^ 56834 = (5 : ZMod 465585143) ^ (28417 + 28417) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 28417 * (5 : ZMod 465585143) ^ 28417 := by rw [pow_add]
          _ = 232630845 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 465585143) ^ 113668 = 199089080 := by
        calc
          (5 : ZMod 465585143) ^ 113668 = (5 : ZMod 465585143) ^ (56834 + 56834) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 56834 * (5 : ZMod 465585143) ^ 56834 := by rw [pow_add]
          _ = 199089080 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 465585143) ^ 227336 = 135498318 := by
        calc
          (5 : ZMod 465585143) ^ 227336 = (5 : ZMod 465585143) ^ (113668 + 113668) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 113668 * (5 : ZMod 465585143) ^ 113668 := by rw [pow_add]
          _ = 135498318 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 465585143) ^ 454672 = 440870009 := by
        calc
          (5 : ZMod 465585143) ^ 454672 = (5 : ZMod 465585143) ^ (227336 + 227336) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 227336 * (5 : ZMod 465585143) ^ 227336 := by rw [pow_add]
          _ = 440870009 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 465585143) ^ 909345 = 57134938 := by
        calc
          (5 : ZMod 465585143) ^ 909345 = (5 : ZMod 465585143) ^ (454672 + 454672 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 454672 * (5 : ZMod 465585143) ^ 454672) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 57134938 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 465585143) ^ 1818691 = 379552224 := by
        calc
          (5 : ZMod 465585143) ^ 1818691 = (5 : ZMod 465585143) ^ (909345 + 909345 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 909345 * (5 : ZMod 465585143) ^ 909345) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 379552224 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 465585143) ^ 3637383 = 307804555 := by
        calc
          (5 : ZMod 465585143) ^ 3637383 = (5 : ZMod 465585143) ^ (1818691 + 1818691 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 1818691 * (5 : ZMod 465585143) ^ 1818691) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 307804555 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 465585143) ^ 7274767 = 64148624 := by
        calc
          (5 : ZMod 465585143) ^ 7274767 = (5 : ZMod 465585143) ^ (3637383 + 3637383 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 3637383 * (5 : ZMod 465585143) ^ 3637383) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 64148624 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 465585143) ^ 14549535 = 376907995 := by
        calc
          (5 : ZMod 465585143) ^ 14549535 = (5 : ZMod 465585143) ^ (7274767 + 7274767 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 7274767 * (5 : ZMod 465585143) ^ 7274767) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 376907995 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 465585143) ^ 29099071 = 372512811 := by
        calc
          (5 : ZMod 465585143) ^ 29099071 = (5 : ZMod 465585143) ^ (14549535 + 14549535 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 14549535 * (5 : ZMod 465585143) ^ 14549535) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 372512811 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 465585143) ^ 58198142 = 172692291 := by
        calc
          (5 : ZMod 465585143) ^ 58198142 = (5 : ZMod 465585143) ^ (29099071 + 29099071) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 29099071 * (5 : ZMod 465585143) ^ 29099071 := by rw [pow_add]
          _ = 172692291 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 465585143) ^ 116396285 = 130572206 := by
        calc
          (5 : ZMod 465585143) ^ 116396285 = (5 : ZMod 465585143) ^ (58198142 + 58198142 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 58198142 * (5 : ZMod 465585143) ^ 58198142) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 130572206 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 465585143) ^ 232792571 = 465585142 := by
        calc
          (5 : ZMod 465585143) ^ 232792571 = (5 : ZMod 465585143) ^ (116396285 + 116396285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 116396285 * (5 : ZMod 465585143) ^ 116396285) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 465585142 := by rw [factor_0_26]; decide
      change (5 : ZMod 465585143) ^ 232792571 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (5 : ZMod 465585143) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 465585143) ^ 2 = 25 := by
        calc
          (5 : ZMod 465585143) ^ 2 = (5 : ZMod 465585143) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 1 * (5 : ZMod 465585143) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 465585143) ^ 5 = 3125 := by
        calc
          (5 : ZMod 465585143) ^ 5 = (5 : ZMod 465585143) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 2 * (5 : ZMod 465585143) ^ 2) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 465585143) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 465585143) ^ 10 = (5 : ZMod 465585143) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 5 * (5 : ZMod 465585143) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 465585143) ^ 20 = 230044506 := by
        calc
          (5 : ZMod 465585143) ^ 20 = (5 : ZMod 465585143) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 10 * (5 : ZMod 465585143) ^ 10 := by rw [pow_add]
          _ = 230044506 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 465585143) ^ 40 = 189369116 := by
        calc
          (5 : ZMod 465585143) ^ 40 = (5 : ZMod 465585143) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 20 * (5 : ZMod 465585143) ^ 20 := by rw [pow_add]
          _ = 189369116 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 465585143) ^ 80 = 54063916 := by
        calc
          (5 : ZMod 465585143) ^ 80 = (5 : ZMod 465585143) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 40 * (5 : ZMod 465585143) ^ 40 := by rw [pow_add]
          _ = 54063916 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 465585143) ^ 161 = 402466479 := by
        calc
          (5 : ZMod 465585143) ^ 161 = (5 : ZMod 465585143) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 80 * (5 : ZMod 465585143) ^ 80) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 402466479 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 465585143) ^ 322 = 235008196 := by
        calc
          (5 : ZMod 465585143) ^ 322 = (5 : ZMod 465585143) ^ (161 + 161) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 161 * (5 : ZMod 465585143) ^ 161 := by rw [pow_add]
          _ = 235008196 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 465585143) ^ 645 = 358452613 := by
        calc
          (5 : ZMod 465585143) ^ 645 = (5 : ZMod 465585143) ^ (322 + 322 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 322 * (5 : ZMod 465585143) ^ 322) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 358452613 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 465585143) ^ 1291 = 169966561 := by
        calc
          (5 : ZMod 465585143) ^ 1291 = (5 : ZMod 465585143) ^ (645 + 645 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 645 * (5 : ZMod 465585143) ^ 645) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 169966561 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 465585143) ^ 2583 = 316086169 := by
        calc
          (5 : ZMod 465585143) ^ 2583 = (5 : ZMod 465585143) ^ (1291 + 1291 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 1291 * (5 : ZMod 465585143) ^ 1291) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 316086169 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 465585143) ^ 5166 = 75087535 := by
        calc
          (5 : ZMod 465585143) ^ 5166 = (5 : ZMod 465585143) ^ (2583 + 2583) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 2583 * (5 : ZMod 465585143) ^ 2583 := by rw [pow_add]
          _ = 75087535 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 465585143) ^ 10333 = 345556990 := by
        calc
          (5 : ZMod 465585143) ^ 10333 = (5 : ZMod 465585143) ^ (5166 + 5166 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 5166 * (5 : ZMod 465585143) ^ 5166) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 345556990 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 465585143) ^ 20666 = 461719504 := by
        calc
          (5 : ZMod 465585143) ^ 20666 = (5 : ZMod 465585143) ^ (10333 + 10333) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 10333 * (5 : ZMod 465585143) ^ 10333 := by rw [pow_add]
          _ = 461719504 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 465585143) ^ 41333 = 117398394 := by
        calc
          (5 : ZMod 465585143) ^ 41333 = (5 : ZMod 465585143) ^ (20666 + 20666 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 20666 * (5 : ZMod 465585143) ^ 20666) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 117398394 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 465585143) ^ 82667 = 147244264 := by
        calc
          (5 : ZMod 465585143) ^ 82667 = (5 : ZMod 465585143) ^ (41333 + 41333 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 41333 * (5 : ZMod 465585143) ^ 41333) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 147244264 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 465585143) ^ 165335 = 18104669 := by
        calc
          (5 : ZMod 465585143) ^ 165335 = (5 : ZMod 465585143) ^ (82667 + 82667 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 82667 * (5 : ZMod 465585143) ^ 82667) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 18104669 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 465585143) ^ 330671 = 110166937 := by
        calc
          (5 : ZMod 465585143) ^ 330671 = (5 : ZMod 465585143) ^ (165335 + 165335 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 165335 * (5 : ZMod 465585143) ^ 165335) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 110166937 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 465585143) ^ 661342 = 155619720 := by
        calc
          (5 : ZMod 465585143) ^ 661342 = (5 : ZMod 465585143) ^ (330671 + 330671) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 330671 * (5 : ZMod 465585143) ^ 330671 := by rw [pow_add]
          _ = 155619720 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 465585143) ^ 1322685 = 463580011 := by
        calc
          (5 : ZMod 465585143) ^ 1322685 = (5 : ZMod 465585143) ^ (661342 + 661342 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 661342 * (5 : ZMod 465585143) ^ 661342) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 463580011 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 465585143) ^ 2645370 = 226627619 := by
        calc
          (5 : ZMod 465585143) ^ 2645370 = (5 : ZMod 465585143) ^ (1322685 + 1322685) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 1322685 * (5 : ZMod 465585143) ^ 1322685 := by rw [pow_add]
          _ = 226627619 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 465585143) ^ 5290740 = 109330166 := by
        calc
          (5 : ZMod 465585143) ^ 5290740 = (5 : ZMod 465585143) ^ (2645370 + 2645370) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 2645370 * (5 : ZMod 465585143) ^ 2645370 := by rw [pow_add]
          _ = 109330166 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 465585143) ^ 10581480 = 28307377 := by
        calc
          (5 : ZMod 465585143) ^ 10581480 = (5 : ZMod 465585143) ^ (5290740 + 5290740) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 5290740 * (5 : ZMod 465585143) ^ 5290740 := by rw [pow_add]
          _ = 28307377 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 465585143) ^ 21162961 = 419646162 := by
        calc
          (5 : ZMod 465585143) ^ 21162961 = (5 : ZMod 465585143) ^ (10581480 + 10581480 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 10581480 * (5 : ZMod 465585143) ^ 10581480) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 419646162 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 465585143) ^ 42325922 = 72267394 := by
        calc
          (5 : ZMod 465585143) ^ 42325922 = (5 : ZMod 465585143) ^ (21162961 + 21162961) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 21162961 * (5 : ZMod 465585143) ^ 21162961 := by rw [pow_add]
          _ = 72267394 := by rw [factor_1_24]; decide
      change (5 : ZMod 465585143) ^ 42325922 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (5 : ZMod 465585143) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 465585143) ^ 3 = 125 := by
        calc
          (5 : ZMod 465585143) ^ 3 = (5 : ZMod 465585143) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 1 * (5 : ZMod 465585143) ^ 1) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 465585143) ^ 6 = 15625 := by
        calc
          (5 : ZMod 465585143) ^ 6 = (5 : ZMod 465585143) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 3 * (5 : ZMod 465585143) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 465585143) ^ 13 = 289532839 := by
        calc
          (5 : ZMod 465585143) ^ 13 = (5 : ZMod 465585143) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 6 * (5 : ZMod 465585143) ^ 6) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 289532839 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 465585143) ^ 26 = 128102290 := by
        calc
          (5 : ZMod 465585143) ^ 26 = (5 : ZMod 465585143) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 13 * (5 : ZMod 465585143) ^ 13 := by rw [pow_add]
          _ = 128102290 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 465585143) ^ 53 = 287279934 := by
        calc
          (5 : ZMod 465585143) ^ 53 = (5 : ZMod 465585143) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 26 * (5 : ZMod 465585143) ^ 26) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 287279934 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 465585143) ^ 106 = 217662028 := by
        calc
          (5 : ZMod 465585143) ^ 106 = (5 : ZMod 465585143) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 53 * (5 : ZMod 465585143) ^ 53 := by rw [pow_add]
          _ = 217662028 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 465585143) ^ 213 = 168174882 := by
        calc
          (5 : ZMod 465585143) ^ 213 = (5 : ZMod 465585143) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 106 * (5 : ZMod 465585143) ^ 106) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 168174882 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 465585143) ^ 426 = 131986672 := by
        calc
          (5 : ZMod 465585143) ^ 426 = (5 : ZMod 465585143) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 213 * (5 : ZMod 465585143) ^ 213 := by rw [pow_add]
          _ = 131986672 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 465585143) ^ 853 = 26530836 := by
        calc
          (5 : ZMod 465585143) ^ 853 = (5 : ZMod 465585143) ^ (426 + 426 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 426 * (5 : ZMod 465585143) ^ 426) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 26530836 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 465585143) ^ 1706 = 137702349 := by
        calc
          (5 : ZMod 465585143) ^ 1706 = (5 : ZMod 465585143) ^ (853 + 853) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 853 * (5 : ZMod 465585143) ^ 853 := by rw [pow_add]
          _ = 137702349 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 465585143) ^ 3413 = 261881070 := by
        calc
          (5 : ZMod 465585143) ^ 3413 = (5 : ZMod 465585143) ^ (1706 + 1706 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 1706 * (5 : ZMod 465585143) ^ 1706) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 261881070 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 465585143) ^ 6827 = 87893818 := by
        calc
          (5 : ZMod 465585143) ^ 6827 = (5 : ZMod 465585143) ^ (3413 + 3413 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 3413 * (5 : ZMod 465585143) ^ 3413) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 87893818 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 465585143) ^ 13655 = 367971964 := by
        calc
          (5 : ZMod 465585143) ^ 13655 = (5 : ZMod 465585143) ^ (6827 + 6827 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 6827 * (5 : ZMod 465585143) ^ 6827) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 367971964 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 465585143) ^ 27310 = 71225286 := by
        calc
          (5 : ZMod 465585143) ^ 27310 = (5 : ZMod 465585143) ^ (13655 + 13655) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 13655 * (5 : ZMod 465585143) ^ 13655 := by rw [pow_add]
          _ = 71225286 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 465585143) ^ 54620 = 40470931 := by
        calc
          (5 : ZMod 465585143) ^ 54620 = (5 : ZMod 465585143) ^ (27310 + 27310) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 27310 * (5 : ZMod 465585143) ^ 27310 := by rw [pow_add]
          _ = 40470931 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 465585143) ^ 109241 = 172708426 := by
        calc
          (5 : ZMod 465585143) ^ 109241 = (5 : ZMod 465585143) ^ (54620 + 54620 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 54620 * (5 : ZMod 465585143) ^ 54620) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 172708426 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 465585143) ^ 218482 = 291872612 := by
        calc
          (5 : ZMod 465585143) ^ 218482 = (5 : ZMod 465585143) ^ (109241 + 109241) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 109241 * (5 : ZMod 465585143) ^ 109241 := by rw [pow_add]
          _ = 291872612 := by rw [factor_2_16]; decide
      change (5 : ZMod 465585143) ^ 218482 ≠ 1
      rw [factor_2_17]
      decide
    ·
      have factor_3_0 : (5 : ZMod 465585143) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 465585143) ^ 2 = 25 := by
        calc
          (5 : ZMod 465585143) ^ 2 = (5 : ZMod 465585143) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 1 * (5 : ZMod 465585143) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 465585143) ^ 5 = 3125 := by
        calc
          (5 : ZMod 465585143) ^ 5 = (5 : ZMod 465585143) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 2 * (5 : ZMod 465585143) ^ 2) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 465585143) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 465585143) ^ 11 = (5 : ZMod 465585143) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 5 * (5 : ZMod 465585143) ^ 5) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 465585143) ^ 22 = 164090934 := by
        calc
          (5 : ZMod 465585143) ^ 22 = (5 : ZMod 465585143) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 11 * (5 : ZMod 465585143) ^ 11 := by rw [pow_add]
          _ = 164090934 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 465585143) ^ 45 = 19770747 := by
        calc
          (5 : ZMod 465585143) ^ 45 = (5 : ZMod 465585143) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 22 * (5 : ZMod 465585143) ^ 22) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 19770747 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 465585143) ^ 91 = 288321223 := by
        calc
          (5 : ZMod 465585143) ^ 91 = (5 : ZMod 465585143) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 45 * (5 : ZMod 465585143) ^ 45) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 288321223 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 465585143) ^ 183 = 308367475 := by
        calc
          (5 : ZMod 465585143) ^ 183 = (5 : ZMod 465585143) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 91 * (5 : ZMod 465585143) ^ 91) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 308367475 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 465585143) ^ 366 = 413678098 := by
        calc
          (5 : ZMod 465585143) ^ 366 = (5 : ZMod 465585143) ^ (183 + 183) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 183 * (5 : ZMod 465585143) ^ 183 := by rw [pow_add]
          _ = 413678098 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 465585143) ^ 732 = 98091025 := by
        calc
          (5 : ZMod 465585143) ^ 732 = (5 : ZMod 465585143) ^ (366 + 366) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 366 * (5 : ZMod 465585143) ^ 366 := by rw [pow_add]
          _ = 98091025 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 465585143) ^ 1465 = 208185880 := by
        calc
          (5 : ZMod 465585143) ^ 1465 = (5 : ZMod 465585143) ^ (732 + 732 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 732 * (5 : ZMod 465585143) ^ 732) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 208185880 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 465585143) ^ 2930 = 94767245 := by
        calc
          (5 : ZMod 465585143) ^ 2930 = (5 : ZMod 465585143) ^ (1465 + 1465) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 1465 * (5 : ZMod 465585143) ^ 1465 := by rw [pow_add]
          _ = 94767245 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 465585143) ^ 5860 = 137029262 := by
        calc
          (5 : ZMod 465585143) ^ 5860 = (5 : ZMod 465585143) ^ (2930 + 2930) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 2930 * (5 : ZMod 465585143) ^ 2930 := by rw [pow_add]
          _ = 137029262 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 465585143) ^ 11720 = 90108939 := by
        calc
          (5 : ZMod 465585143) ^ 11720 = (5 : ZMod 465585143) ^ (5860 + 5860) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 5860 * (5 : ZMod 465585143) ^ 5860 := by rw [pow_add]
          _ = 90108939 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 465585143) ^ 23441 = 430756316 := by
        calc
          (5 : ZMod 465585143) ^ 23441 = (5 : ZMod 465585143) ^ (11720 + 11720 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = ((5 : ZMod 465585143) ^ 11720 * (5 : ZMod 465585143) ^ 11720) * (5 : ZMod 465585143) := by rw [pow_succ, pow_add]
          _ = 430756316 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 465585143) ^ 46882 = 18995154 := by
        calc
          (5 : ZMod 465585143) ^ 46882 = (5 : ZMod 465585143) ^ (23441 + 23441) :=
            congrArg (fun n : ℕ => (5 : ZMod 465585143) ^ n) (by norm_num)
          _ = (5 : ZMod 465585143) ^ 23441 * (5 : ZMod 465585143) ^ 23441 := by rw [pow_add]
          _ = 18995154 := by rw [factor_3_14]; decide
      change (5 : ZMod 465585143) ^ 46882 ≠ 1
      rw [factor_3_15]
      decide

#print axioms prime_lucas_465585143

end TotientTailPeriodKiller
end Erdos249257
