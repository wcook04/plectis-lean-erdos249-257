import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=19 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000

theorem prime_lucas_232792561 : Nat.Prime 232792561 := by
  apply lucas_primality 232792561 (71 : ZMod 232792561)
  ·
      have fermat_0 : (71 : ZMod 232792561) ^ 1 = 71 := by norm_num
      have fermat_1 : (71 : ZMod 232792561) ^ 3 = 357911 := by
        calc
          (71 : ZMod 232792561) ^ 3 = (71 : ZMod 232792561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1 * (71 : ZMod 232792561) ^ 1) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 357911 := by rw [fermat_0]; decide
      have fermat_2 : (71 : ZMod 232792561) ^ 6 = 64375371 := by
        calc
          (71 : ZMod 232792561) ^ 6 = (71 : ZMod 232792561) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 3 * (71 : ZMod 232792561) ^ 3 := by rw [pow_add]
          _ = 64375371 := by rw [fermat_1]; decide
      have fermat_3 : (71 : ZMod 232792561) ^ 13 = 29992349 := by
        calc
          (71 : ZMod 232792561) ^ 13 = (71 : ZMod 232792561) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 6 * (71 : ZMod 232792561) ^ 6) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 29992349 := by rw [fermat_2]; decide
      have fermat_4 : (71 : ZMod 232792561) ^ 27 = 78494156 := by
        calc
          (71 : ZMod 232792561) ^ 27 = (71 : ZMod 232792561) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 13 * (71 : ZMod 232792561) ^ 13) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 78494156 := by rw [fermat_3]; decide
      have fermat_5 : (71 : ZMod 232792561) ^ 55 = 54141573 := by
        calc
          (71 : ZMod 232792561) ^ 55 = (71 : ZMod 232792561) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 27 * (71 : ZMod 232792561) ^ 27) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 54141573 := by rw [fermat_4]; decide
      have fermat_6 : (71 : ZMod 232792561) ^ 111 = 171993390 := by
        calc
          (71 : ZMod 232792561) ^ 111 = (71 : ZMod 232792561) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 55 * (71 : ZMod 232792561) ^ 55) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 171993390 := by rw [fermat_5]; decide
      have fermat_7 : (71 : ZMod 232792561) ^ 222 = 45401409 := by
        calc
          (71 : ZMod 232792561) ^ 222 = (71 : ZMod 232792561) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 111 * (71 : ZMod 232792561) ^ 111 := by rw [pow_add]
          _ = 45401409 := by rw [fermat_6]; decide
      have fermat_8 : (71 : ZMod 232792561) ^ 444 = 135043949 := by
        calc
          (71 : ZMod 232792561) ^ 444 = (71 : ZMod 232792561) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 222 * (71 : ZMod 232792561) ^ 222 := by rw [pow_add]
          _ = 135043949 := by rw [fermat_7]; decide
      have fermat_9 : (71 : ZMod 232792561) ^ 888 = 197538636 := by
        calc
          (71 : ZMod 232792561) ^ 888 = (71 : ZMod 232792561) ^ (444 + 444) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 444 * (71 : ZMod 232792561) ^ 444 := by rw [pow_add]
          _ = 197538636 := by rw [fermat_8]; decide
      have fermat_10 : (71 : ZMod 232792561) ^ 1776 = 17839678 := by
        calc
          (71 : ZMod 232792561) ^ 1776 = (71 : ZMod 232792561) ^ (888 + 888) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 888 * (71 : ZMod 232792561) ^ 888 := by rw [pow_add]
          _ = 17839678 := by rw [fermat_9]; decide
      have fermat_11 : (71 : ZMod 232792561) ^ 3552 = 141904730 := by
        calc
          (71 : ZMod 232792561) ^ 3552 = (71 : ZMod 232792561) ^ (1776 + 1776) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1776 * (71 : ZMod 232792561) ^ 1776 := by rw [pow_add]
          _ = 141904730 := by rw [fermat_10]; decide
      have fermat_12 : (71 : ZMod 232792561) ^ 7104 = 122519200 := by
        calc
          (71 : ZMod 232792561) ^ 7104 = (71 : ZMod 232792561) ^ (3552 + 3552) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 3552 * (71 : ZMod 232792561) ^ 3552 := by rw [pow_add]
          _ = 122519200 := by rw [fermat_11]; decide
      have fermat_13 : (71 : ZMod 232792561) ^ 14208 = 7019095 := by
        calc
          (71 : ZMod 232792561) ^ 14208 = (71 : ZMod 232792561) ^ (7104 + 7104) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 7104 * (71 : ZMod 232792561) ^ 7104 := by rw [pow_add]
          _ = 7019095 := by rw [fermat_12]; decide
      have fermat_14 : (71 : ZMod 232792561) ^ 28417 = 114447695 := by
        calc
          (71 : ZMod 232792561) ^ 28417 = (71 : ZMod 232792561) ^ (14208 + 14208 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 14208 * (71 : ZMod 232792561) ^ 14208) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 114447695 := by rw [fermat_13]; decide
      have fermat_15 : (71 : ZMod 232792561) ^ 56834 = 80582760 := by
        calc
          (71 : ZMod 232792561) ^ 56834 = (71 : ZMod 232792561) ^ (28417 + 28417) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 28417 * (71 : ZMod 232792561) ^ 28417 := by rw [pow_add]
          _ = 80582760 := by rw [fermat_14]; decide
      have fermat_16 : (71 : ZMod 232792561) ^ 113668 = 97973959 := by
        calc
          (71 : ZMod 232792561) ^ 113668 = (71 : ZMod 232792561) ^ (56834 + 56834) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 56834 * (71 : ZMod 232792561) ^ 56834 := by rw [pow_add]
          _ = 97973959 := by rw [fermat_15]; decide
      have fermat_17 : (71 : ZMod 232792561) ^ 227336 = 114761030 := by
        calc
          (71 : ZMod 232792561) ^ 227336 = (71 : ZMod 232792561) ^ (113668 + 113668) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 113668 * (71 : ZMod 232792561) ^ 113668 := by rw [pow_add]
          _ = 114761030 := by rw [fermat_16]; decide
      have fermat_18 : (71 : ZMod 232792561) ^ 454672 = 130643964 := by
        calc
          (71 : ZMod 232792561) ^ 454672 = (71 : ZMod 232792561) ^ (227336 + 227336) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 227336 * (71 : ZMod 232792561) ^ 227336 := by rw [pow_add]
          _ = 130643964 := by rw [fermat_17]; decide
      have fermat_19 : (71 : ZMod 232792561) ^ 909345 = 157523872 := by
        calc
          (71 : ZMod 232792561) ^ 909345 = (71 : ZMod 232792561) ^ (454672 + 454672 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 454672 * (71 : ZMod 232792561) ^ 454672) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 157523872 := by rw [fermat_18]; decide
      have fermat_20 : (71 : ZMod 232792561) ^ 1818691 = 156329620 := by
        calc
          (71 : ZMod 232792561) ^ 1818691 = (71 : ZMod 232792561) ^ (909345 + 909345 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 909345 * (71 : ZMod 232792561) ^ 909345) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 156329620 := by rw [fermat_19]; decide
      have fermat_21 : (71 : ZMod 232792561) ^ 3637383 = 225586838 := by
        calc
          (71 : ZMod 232792561) ^ 3637383 = (71 : ZMod 232792561) ^ (1818691 + 1818691 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1818691 * (71 : ZMod 232792561) ^ 1818691) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 225586838 := by rw [fermat_20]; decide
      have fermat_22 : (71 : ZMod 232792561) ^ 7274767 = 69142760 := by
        calc
          (71 : ZMod 232792561) ^ 7274767 = (71 : ZMod 232792561) ^ (3637383 + 3637383 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 3637383 * (71 : ZMod 232792561) ^ 3637383) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 69142760 := by rw [fermat_21]; decide
      have fermat_23 : (71 : ZMod 232792561) ^ 14549535 = 177346687 := by
        calc
          (71 : ZMod 232792561) ^ 14549535 = (71 : ZMod 232792561) ^ (7274767 + 7274767 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 7274767 * (71 : ZMod 232792561) ^ 7274767) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 177346687 := by rw [fermat_22]; decide
      have fermat_24 : (71 : ZMod 232792561) ^ 29099070 = 117818975 := by
        calc
          (71 : ZMod 232792561) ^ 29099070 = (71 : ZMod 232792561) ^ (14549535 + 14549535) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 14549535 * (71 : ZMod 232792561) ^ 14549535 := by rw [pow_add]
          _ = 117818975 := by rw [fermat_23]; decide
      have fermat_25 : (71 : ZMod 232792561) ^ 58198140 = 102916856 := by
        calc
          (71 : ZMod 232792561) ^ 58198140 = (71 : ZMod 232792561) ^ (29099070 + 29099070) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 29099070 * (71 : ZMod 232792561) ^ 29099070 := by rw [pow_add]
          _ = 102916856 := by rw [fermat_24]; decide
      have fermat_26 : (71 : ZMod 232792561) ^ 116396280 = 232792560 := by
        calc
          (71 : ZMod 232792561) ^ 116396280 = (71 : ZMod 232792561) ^ (58198140 + 58198140) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 58198140 * (71 : ZMod 232792561) ^ 58198140 := by rw [pow_add]
          _ = 232792560 := by rw [fermat_25]; decide
      have fermat_27 : (71 : ZMod 232792561) ^ 232792560 = 1 := by
        calc
          (71 : ZMod 232792561) ^ 232792560 = (71 : ZMod 232792561) ^ (116396280 + 116396280) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 116396280 * (71 : ZMod 232792561) ^ 116396280 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1)] : List FactorBlock).map factorBlockValue).prod = 232792561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (71 : ZMod 232792561) ^ 1 = 71 := by norm_num
      have factor_0_1 : (71 : ZMod 232792561) ^ 3 = 357911 := by
        calc
          (71 : ZMod 232792561) ^ 3 = (71 : ZMod 232792561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1 * (71 : ZMod 232792561) ^ 1) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 357911 := by rw [factor_0_0]; decide
      have factor_0_2 : (71 : ZMod 232792561) ^ 6 = 64375371 := by
        calc
          (71 : ZMod 232792561) ^ 6 = (71 : ZMod 232792561) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 3 * (71 : ZMod 232792561) ^ 3 := by rw [pow_add]
          _ = 64375371 := by rw [factor_0_1]; decide
      have factor_0_3 : (71 : ZMod 232792561) ^ 13 = 29992349 := by
        calc
          (71 : ZMod 232792561) ^ 13 = (71 : ZMod 232792561) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 6 * (71 : ZMod 232792561) ^ 6) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 29992349 := by rw [factor_0_2]; decide
      have factor_0_4 : (71 : ZMod 232792561) ^ 27 = 78494156 := by
        calc
          (71 : ZMod 232792561) ^ 27 = (71 : ZMod 232792561) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 13 * (71 : ZMod 232792561) ^ 13) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 78494156 := by rw [factor_0_3]; decide
      have factor_0_5 : (71 : ZMod 232792561) ^ 55 = 54141573 := by
        calc
          (71 : ZMod 232792561) ^ 55 = (71 : ZMod 232792561) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 27 * (71 : ZMod 232792561) ^ 27) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 54141573 := by rw [factor_0_4]; decide
      have factor_0_6 : (71 : ZMod 232792561) ^ 111 = 171993390 := by
        calc
          (71 : ZMod 232792561) ^ 111 = (71 : ZMod 232792561) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 55 * (71 : ZMod 232792561) ^ 55) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 171993390 := by rw [factor_0_5]; decide
      have factor_0_7 : (71 : ZMod 232792561) ^ 222 = 45401409 := by
        calc
          (71 : ZMod 232792561) ^ 222 = (71 : ZMod 232792561) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 111 * (71 : ZMod 232792561) ^ 111 := by rw [pow_add]
          _ = 45401409 := by rw [factor_0_6]; decide
      have factor_0_8 : (71 : ZMod 232792561) ^ 444 = 135043949 := by
        calc
          (71 : ZMod 232792561) ^ 444 = (71 : ZMod 232792561) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 222 * (71 : ZMod 232792561) ^ 222 := by rw [pow_add]
          _ = 135043949 := by rw [factor_0_7]; decide
      have factor_0_9 : (71 : ZMod 232792561) ^ 888 = 197538636 := by
        calc
          (71 : ZMod 232792561) ^ 888 = (71 : ZMod 232792561) ^ (444 + 444) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 444 * (71 : ZMod 232792561) ^ 444 := by rw [pow_add]
          _ = 197538636 := by rw [factor_0_8]; decide
      have factor_0_10 : (71 : ZMod 232792561) ^ 1776 = 17839678 := by
        calc
          (71 : ZMod 232792561) ^ 1776 = (71 : ZMod 232792561) ^ (888 + 888) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 888 * (71 : ZMod 232792561) ^ 888 := by rw [pow_add]
          _ = 17839678 := by rw [factor_0_9]; decide
      have factor_0_11 : (71 : ZMod 232792561) ^ 3552 = 141904730 := by
        calc
          (71 : ZMod 232792561) ^ 3552 = (71 : ZMod 232792561) ^ (1776 + 1776) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1776 * (71 : ZMod 232792561) ^ 1776 := by rw [pow_add]
          _ = 141904730 := by rw [factor_0_10]; decide
      have factor_0_12 : (71 : ZMod 232792561) ^ 7104 = 122519200 := by
        calc
          (71 : ZMod 232792561) ^ 7104 = (71 : ZMod 232792561) ^ (3552 + 3552) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 3552 * (71 : ZMod 232792561) ^ 3552 := by rw [pow_add]
          _ = 122519200 := by rw [factor_0_11]; decide
      have factor_0_13 : (71 : ZMod 232792561) ^ 14208 = 7019095 := by
        calc
          (71 : ZMod 232792561) ^ 14208 = (71 : ZMod 232792561) ^ (7104 + 7104) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 7104 * (71 : ZMod 232792561) ^ 7104 := by rw [pow_add]
          _ = 7019095 := by rw [factor_0_12]; decide
      have factor_0_14 : (71 : ZMod 232792561) ^ 28417 = 114447695 := by
        calc
          (71 : ZMod 232792561) ^ 28417 = (71 : ZMod 232792561) ^ (14208 + 14208 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 14208 * (71 : ZMod 232792561) ^ 14208) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 114447695 := by rw [factor_0_13]; decide
      have factor_0_15 : (71 : ZMod 232792561) ^ 56834 = 80582760 := by
        calc
          (71 : ZMod 232792561) ^ 56834 = (71 : ZMod 232792561) ^ (28417 + 28417) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 28417 * (71 : ZMod 232792561) ^ 28417 := by rw [pow_add]
          _ = 80582760 := by rw [factor_0_14]; decide
      have factor_0_16 : (71 : ZMod 232792561) ^ 113668 = 97973959 := by
        calc
          (71 : ZMod 232792561) ^ 113668 = (71 : ZMod 232792561) ^ (56834 + 56834) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 56834 * (71 : ZMod 232792561) ^ 56834 := by rw [pow_add]
          _ = 97973959 := by rw [factor_0_15]; decide
      have factor_0_17 : (71 : ZMod 232792561) ^ 227336 = 114761030 := by
        calc
          (71 : ZMod 232792561) ^ 227336 = (71 : ZMod 232792561) ^ (113668 + 113668) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 113668 * (71 : ZMod 232792561) ^ 113668 := by rw [pow_add]
          _ = 114761030 := by rw [factor_0_16]; decide
      have factor_0_18 : (71 : ZMod 232792561) ^ 454672 = 130643964 := by
        calc
          (71 : ZMod 232792561) ^ 454672 = (71 : ZMod 232792561) ^ (227336 + 227336) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 227336 * (71 : ZMod 232792561) ^ 227336 := by rw [pow_add]
          _ = 130643964 := by rw [factor_0_17]; decide
      have factor_0_19 : (71 : ZMod 232792561) ^ 909345 = 157523872 := by
        calc
          (71 : ZMod 232792561) ^ 909345 = (71 : ZMod 232792561) ^ (454672 + 454672 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 454672 * (71 : ZMod 232792561) ^ 454672) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 157523872 := by rw [factor_0_18]; decide
      have factor_0_20 : (71 : ZMod 232792561) ^ 1818691 = 156329620 := by
        calc
          (71 : ZMod 232792561) ^ 1818691 = (71 : ZMod 232792561) ^ (909345 + 909345 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 909345 * (71 : ZMod 232792561) ^ 909345) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 156329620 := by rw [factor_0_19]; decide
      have factor_0_21 : (71 : ZMod 232792561) ^ 3637383 = 225586838 := by
        calc
          (71 : ZMod 232792561) ^ 3637383 = (71 : ZMod 232792561) ^ (1818691 + 1818691 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1818691 * (71 : ZMod 232792561) ^ 1818691) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 225586838 := by rw [factor_0_20]; decide
      have factor_0_22 : (71 : ZMod 232792561) ^ 7274767 = 69142760 := by
        calc
          (71 : ZMod 232792561) ^ 7274767 = (71 : ZMod 232792561) ^ (3637383 + 3637383 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 3637383 * (71 : ZMod 232792561) ^ 3637383) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 69142760 := by rw [factor_0_21]; decide
      have factor_0_23 : (71 : ZMod 232792561) ^ 14549535 = 177346687 := by
        calc
          (71 : ZMod 232792561) ^ 14549535 = (71 : ZMod 232792561) ^ (7274767 + 7274767 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 7274767 * (71 : ZMod 232792561) ^ 7274767) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 177346687 := by rw [factor_0_22]; decide
      have factor_0_24 : (71 : ZMod 232792561) ^ 29099070 = 117818975 := by
        calc
          (71 : ZMod 232792561) ^ 29099070 = (71 : ZMod 232792561) ^ (14549535 + 14549535) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 14549535 * (71 : ZMod 232792561) ^ 14549535 := by rw [pow_add]
          _ = 117818975 := by rw [factor_0_23]; decide
      have factor_0_25 : (71 : ZMod 232792561) ^ 58198140 = 102916856 := by
        calc
          (71 : ZMod 232792561) ^ 58198140 = (71 : ZMod 232792561) ^ (29099070 + 29099070) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 29099070 * (71 : ZMod 232792561) ^ 29099070 := by rw [pow_add]
          _ = 102916856 := by rw [factor_0_24]; decide
      have factor_0_26 : (71 : ZMod 232792561) ^ 116396280 = 232792560 := by
        calc
          (71 : ZMod 232792561) ^ 116396280 = (71 : ZMod 232792561) ^ (58198140 + 58198140) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 58198140 * (71 : ZMod 232792561) ^ 58198140 := by rw [pow_add]
          _ = 232792560 := by rw [factor_0_25]; decide
      change (71 : ZMod 232792561) ^ 116396280 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (71 : ZMod 232792561) ^ 1 = 71 := by norm_num
      have factor_1_1 : (71 : ZMod 232792561) ^ 2 = 5041 := by
        calc
          (71 : ZMod 232792561) ^ 2 = (71 : ZMod 232792561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1 * (71 : ZMod 232792561) ^ 1 := by rw [pow_add]
          _ = 5041 := by rw [factor_1_0]; decide
      have factor_1_2 : (71 : ZMod 232792561) ^ 4 = 25411681 := by
        calc
          (71 : ZMod 232792561) ^ 4 = (71 : ZMod 232792561) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 2 * (71 : ZMod 232792561) ^ 2 := by rw [pow_add]
          _ = 25411681 := by rw [factor_1_1]; decide
      have factor_1_3 : (71 : ZMod 232792561) ^ 9 = 9685006 := by
        calc
          (71 : ZMod 232792561) ^ 9 = (71 : ZMod 232792561) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 4 * (71 : ZMod 232792561) ^ 4) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 9685006 := by rw [factor_1_2]; decide
      have factor_1_4 : (71 : ZMod 232792561) ^ 18 = 1823745 := by
        calc
          (71 : ZMod 232792561) ^ 18 = (71 : ZMod 232792561) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 9 * (71 : ZMod 232792561) ^ 9 := by rw [pow_add]
          _ = 1823745 := by rw [factor_1_3]; decide
      have factor_1_5 : (71 : ZMod 232792561) ^ 37 = 56639716 := by
        calc
          (71 : ZMod 232792561) ^ 37 = (71 : ZMod 232792561) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 18 * (71 : ZMod 232792561) ^ 18) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 56639716 := by rw [factor_1_4]; decide
      have factor_1_6 : (71 : ZMod 232792561) ^ 74 = 179597101 := by
        calc
          (71 : ZMod 232792561) ^ 74 = (71 : ZMod 232792561) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 37 * (71 : ZMod 232792561) ^ 37 := by rw [pow_add]
          _ = 179597101 := by rw [factor_1_5]; decide
      have factor_1_7 : (71 : ZMod 232792561) ^ 148 = 198071339 := by
        calc
          (71 : ZMod 232792561) ^ 148 = (71 : ZMod 232792561) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 74 * (71 : ZMod 232792561) ^ 74 := by rw [pow_add]
          _ = 198071339 := by rw [factor_1_6]; decide
      have factor_1_8 : (71 : ZMod 232792561) ^ 296 = 188730023 := by
        calc
          (71 : ZMod 232792561) ^ 296 = (71 : ZMod 232792561) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 148 * (71 : ZMod 232792561) ^ 148 := by rw [pow_add]
          _ = 188730023 := by rw [factor_1_7]; decide
      have factor_1_9 : (71 : ZMod 232792561) ^ 592 = 69611930 := by
        calc
          (71 : ZMod 232792561) ^ 592 = (71 : ZMod 232792561) ^ (296 + 296) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 296 * (71 : ZMod 232792561) ^ 296 := by rw [pow_add]
          _ = 69611930 := by rw [factor_1_8]; decide
      have factor_1_10 : (71 : ZMod 232792561) ^ 1184 = 140091094 := by
        calc
          (71 : ZMod 232792561) ^ 1184 = (71 : ZMod 232792561) ^ (592 + 592) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 592 * (71 : ZMod 232792561) ^ 592 := by rw [pow_add]
          _ = 140091094 := by rw [factor_1_9]; decide
      have factor_1_11 : (71 : ZMod 232792561) ^ 2368 = 151418184 := by
        calc
          (71 : ZMod 232792561) ^ 2368 = (71 : ZMod 232792561) ^ (1184 + 1184) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1184 * (71 : ZMod 232792561) ^ 1184 := by rw [pow_add]
          _ = 151418184 := by rw [factor_1_10]; decide
      have factor_1_12 : (71 : ZMod 232792561) ^ 4736 = 178641909 := by
        calc
          (71 : ZMod 232792561) ^ 4736 = (71 : ZMod 232792561) ^ (2368 + 2368) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 2368 * (71 : ZMod 232792561) ^ 2368 := by rw [pow_add]
          _ = 178641909 := by rw [factor_1_11]; decide
      have factor_1_13 : (71 : ZMod 232792561) ^ 9472 = 68481661 := by
        calc
          (71 : ZMod 232792561) ^ 9472 = (71 : ZMod 232792561) ^ (4736 + 4736) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 4736 * (71 : ZMod 232792561) ^ 4736 := by rw [pow_add]
          _ = 68481661 := by rw [factor_1_12]; decide
      have factor_1_14 : (71 : ZMod 232792561) ^ 18944 = 224176956 := by
        calc
          (71 : ZMod 232792561) ^ 18944 = (71 : ZMod 232792561) ^ (9472 + 9472) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 9472 * (71 : ZMod 232792561) ^ 9472 := by rw [pow_add]
          _ = 224176956 := by rw [factor_1_13]; decide
      have factor_1_15 : (71 : ZMod 232792561) ^ 37889 = 27742429 := by
        calc
          (71 : ZMod 232792561) ^ 37889 = (71 : ZMod 232792561) ^ (18944 + 18944 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 18944 * (71 : ZMod 232792561) ^ 18944) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 27742429 := by rw [factor_1_14]; decide
      have factor_1_16 : (71 : ZMod 232792561) ^ 75778 = 129913672 := by
        calc
          (71 : ZMod 232792561) ^ 75778 = (71 : ZMod 232792561) ^ (37889 + 37889) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 37889 * (71 : ZMod 232792561) ^ 37889 := by rw [pow_add]
          _ = 129913672 := by rw [factor_1_15]; decide
      have factor_1_17 : (71 : ZMod 232792561) ^ 151557 = 175156148 := by
        calc
          (71 : ZMod 232792561) ^ 151557 = (71 : ZMod 232792561) ^ (75778 + 75778 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 75778 * (71 : ZMod 232792561) ^ 75778) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 175156148 := by rw [factor_1_16]; decide
      have factor_1_18 : (71 : ZMod 232792561) ^ 303115 = 152390011 := by
        calc
          (71 : ZMod 232792561) ^ 303115 = (71 : ZMod 232792561) ^ (151557 + 151557 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 151557 * (71 : ZMod 232792561) ^ 151557) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 152390011 := by rw [factor_1_17]; decide
      have factor_1_19 : (71 : ZMod 232792561) ^ 606230 = 9795801 := by
        calc
          (71 : ZMod 232792561) ^ 606230 = (71 : ZMod 232792561) ^ (303115 + 303115) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 303115 * (71 : ZMod 232792561) ^ 303115 := by rw [pow_add]
          _ = 9795801 := by rw [factor_1_18]; decide
      have factor_1_20 : (71 : ZMod 232792561) ^ 1212461 = 44118881 := by
        calc
          (71 : ZMod 232792561) ^ 1212461 = (71 : ZMod 232792561) ^ (606230 + 606230 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 606230 * (71 : ZMod 232792561) ^ 606230) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 44118881 := by rw [factor_1_19]; decide
      have factor_1_21 : (71 : ZMod 232792561) ^ 2424922 = 216465785 := by
        calc
          (71 : ZMod 232792561) ^ 2424922 = (71 : ZMod 232792561) ^ (1212461 + 1212461) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1212461 * (71 : ZMod 232792561) ^ 1212461 := by rw [pow_add]
          _ = 216465785 := by rw [factor_1_20]; decide
      have factor_1_22 : (71 : ZMod 232792561) ^ 4849845 = 47451376 := by
        calc
          (71 : ZMod 232792561) ^ 4849845 = (71 : ZMod 232792561) ^ (2424922 + 2424922 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 2424922 * (71 : ZMod 232792561) ^ 2424922) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 47451376 := by rw [factor_1_21]; decide
      have factor_1_23 : (71 : ZMod 232792561) ^ 9699690 = 114724784 := by
        calc
          (71 : ZMod 232792561) ^ 9699690 = (71 : ZMod 232792561) ^ (4849845 + 4849845) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 4849845 * (71 : ZMod 232792561) ^ 4849845 := by rw [pow_add]
          _ = 114724784 := by rw [factor_1_22]; decide
      have factor_1_24 : (71 : ZMod 232792561) ^ 19399380 = 98826811 := by
        calc
          (71 : ZMod 232792561) ^ 19399380 = (71 : ZMod 232792561) ^ (9699690 + 9699690) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 9699690 * (71 : ZMod 232792561) ^ 9699690 := by rw [pow_add]
          _ = 98826811 := by rw [factor_1_23]; decide
      have factor_1_25 : (71 : ZMod 232792561) ^ 38798760 = 5331436 := by
        calc
          (71 : ZMod 232792561) ^ 38798760 = (71 : ZMod 232792561) ^ (19399380 + 19399380) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 19399380 * (71 : ZMod 232792561) ^ 19399380 := by rw [pow_add]
          _ = 5331436 := by rw [factor_1_24]; decide
      have factor_1_26 : (71 : ZMod 232792561) ^ 77597520 = 5331435 := by
        calc
          (71 : ZMod 232792561) ^ 77597520 = (71 : ZMod 232792561) ^ (38798760 + 38798760) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 38798760 * (71 : ZMod 232792561) ^ 38798760 := by rw [pow_add]
          _ = 5331435 := by rw [factor_1_25]; decide
      change (71 : ZMod 232792561) ^ 77597520 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (71 : ZMod 232792561) ^ 1 = 71 := by norm_num
      have factor_2_1 : (71 : ZMod 232792561) ^ 2 = 5041 := by
        calc
          (71 : ZMod 232792561) ^ 2 = (71 : ZMod 232792561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1 * (71 : ZMod 232792561) ^ 1 := by rw [pow_add]
          _ = 5041 := by rw [factor_2_0]; decide
      have factor_2_2 : (71 : ZMod 232792561) ^ 5 = 174681424 := by
        calc
          (71 : ZMod 232792561) ^ 5 = (71 : ZMod 232792561) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 2 * (71 : ZMod 232792561) ^ 2) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 174681424 := by rw [factor_2_1]; decide
      have factor_2_3 : (71 : ZMod 232792561) ^ 11 = 168469997 := by
        calc
          (71 : ZMod 232792561) ^ 11 = (71 : ZMod 232792561) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 5 * (71 : ZMod 232792561) ^ 5) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 168469997 := by rw [factor_2_2]; decide
      have factor_2_4 : (71 : ZMod 232792561) ^ 22 = 83121465 := by
        calc
          (71 : ZMod 232792561) ^ 22 = (71 : ZMod 232792561) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 11 * (71 : ZMod 232792561) ^ 11 := by rw [pow_add]
          _ = 83121465 := by rw [factor_2_3]; decide
      have factor_2_5 : (71 : ZMod 232792561) ^ 44 = 188296358 := by
        calc
          (71 : ZMod 232792561) ^ 44 = (71 : ZMod 232792561) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 22 * (71 : ZMod 232792561) ^ 22 := by rw [pow_add]
          _ = 188296358 := by rw [factor_2_4]; decide
      have factor_2_6 : (71 : ZMod 232792561) ^ 88 = 176069281 := by
        calc
          (71 : ZMod 232792561) ^ 88 = (71 : ZMod 232792561) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 44 * (71 : ZMod 232792561) ^ 44 := by rw [pow_add]
          _ = 176069281 := by rw [factor_2_5]; decide
      have factor_2_7 : (71 : ZMod 232792561) ^ 177 = 64706086 := by
        calc
          (71 : ZMod 232792561) ^ 177 = (71 : ZMod 232792561) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 88 * (71 : ZMod 232792561) ^ 88) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 64706086 := by rw [factor_2_6]; decide
      have factor_2_8 : (71 : ZMod 232792561) ^ 355 = 178554274 := by
        calc
          (71 : ZMod 232792561) ^ 355 = (71 : ZMod 232792561) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 177 * (71 : ZMod 232792561) ^ 177) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 178554274 := by rw [factor_2_7]; decide
      have factor_2_9 : (71 : ZMod 232792561) ^ 710 = 98284443 := by
        calc
          (71 : ZMod 232792561) ^ 710 = (71 : ZMod 232792561) ^ (355 + 355) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 355 * (71 : ZMod 232792561) ^ 355 := by rw [pow_add]
          _ = 98284443 := by rw [factor_2_8]; decide
      have factor_2_10 : (71 : ZMod 232792561) ^ 1420 = 126057921 := by
        calc
          (71 : ZMod 232792561) ^ 1420 = (71 : ZMod 232792561) ^ (710 + 710) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 710 * (71 : ZMod 232792561) ^ 710 := by rw [pow_add]
          _ = 126057921 := by rw [factor_2_9]; decide
      have factor_2_11 : (71 : ZMod 232792561) ^ 2841 = 169184607 := by
        calc
          (71 : ZMod 232792561) ^ 2841 = (71 : ZMod 232792561) ^ (1420 + 1420 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1420 * (71 : ZMod 232792561) ^ 1420) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 169184607 := by rw [factor_2_10]; decide
      have factor_2_12 : (71 : ZMod 232792561) ^ 5683 = 186086521 := by
        calc
          (71 : ZMod 232792561) ^ 5683 = (71 : ZMod 232792561) ^ (2841 + 2841 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 2841 * (71 : ZMod 232792561) ^ 2841) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 186086521 := by rw [factor_2_11]; decide
      have factor_2_13 : (71 : ZMod 232792561) ^ 11366 = 12314873 := by
        calc
          (71 : ZMod 232792561) ^ 11366 = (71 : ZMod 232792561) ^ (5683 + 5683) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 5683 * (71 : ZMod 232792561) ^ 5683 := by rw [pow_add]
          _ = 12314873 := by rw [factor_2_12]; decide
      have factor_2_14 : (71 : ZMod 232792561) ^ 22733 = 193999818 := by
        calc
          (71 : ZMod 232792561) ^ 22733 = (71 : ZMod 232792561) ^ (11366 + 11366 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 11366 * (71 : ZMod 232792561) ^ 11366) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 193999818 := by rw [factor_2_13]; decide
      have factor_2_15 : (71 : ZMod 232792561) ^ 45467 = 171590253 := by
        calc
          (71 : ZMod 232792561) ^ 45467 = (71 : ZMod 232792561) ^ (22733 + 22733 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 22733 * (71 : ZMod 232792561) ^ 22733) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 171590253 := by rw [factor_2_14]; decide
      have factor_2_16 : (71 : ZMod 232792561) ^ 90934 = 107315757 := by
        calc
          (71 : ZMod 232792561) ^ 90934 = (71 : ZMod 232792561) ^ (45467 + 45467) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 45467 * (71 : ZMod 232792561) ^ 45467 := by rw [pow_add]
          _ = 107315757 := by rw [factor_2_15]; decide
      have factor_2_17 : (71 : ZMod 232792561) ^ 181869 = 170446132 := by
        calc
          (71 : ZMod 232792561) ^ 181869 = (71 : ZMod 232792561) ^ (90934 + 90934 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 90934 * (71 : ZMod 232792561) ^ 90934) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 170446132 := by rw [factor_2_16]; decide
      have factor_2_18 : (71 : ZMod 232792561) ^ 363738 = 142498441 := by
        calc
          (71 : ZMod 232792561) ^ 363738 = (71 : ZMod 232792561) ^ (181869 + 181869) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 181869 * (71 : ZMod 232792561) ^ 181869 := by rw [pow_add]
          _ = 142498441 := by rw [factor_2_17]; decide
      have factor_2_19 : (71 : ZMod 232792561) ^ 727476 = 122966163 := by
        calc
          (71 : ZMod 232792561) ^ 727476 = (71 : ZMod 232792561) ^ (363738 + 363738) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 363738 * (71 : ZMod 232792561) ^ 363738 := by rw [pow_add]
          _ = 122966163 := by rw [factor_2_18]; decide
      have factor_2_20 : (71 : ZMod 232792561) ^ 1454953 = 203858762 := by
        calc
          (71 : ZMod 232792561) ^ 1454953 = (71 : ZMod 232792561) ^ (727476 + 727476 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 727476 * (71 : ZMod 232792561) ^ 727476) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 203858762 := by rw [factor_2_19]; decide
      have factor_2_21 : (71 : ZMod 232792561) ^ 2909907 = 145183056 := by
        calc
          (71 : ZMod 232792561) ^ 2909907 = (71 : ZMod 232792561) ^ (1454953 + 1454953 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1454953 * (71 : ZMod 232792561) ^ 1454953) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 145183056 := by rw [factor_2_20]; decide
      have factor_2_22 : (71 : ZMod 232792561) ^ 5819814 = 187905852 := by
        calc
          (71 : ZMod 232792561) ^ 5819814 = (71 : ZMod 232792561) ^ (2909907 + 2909907) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 2909907 * (71 : ZMod 232792561) ^ 2909907 := by rw [pow_add]
          _ = 187905852 := by rw [factor_2_21]; decide
      have factor_2_23 : (71 : ZMod 232792561) ^ 11639628 = 55698974 := by
        calc
          (71 : ZMod 232792561) ^ 11639628 = (71 : ZMod 232792561) ^ (5819814 + 5819814) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 5819814 * (71 : ZMod 232792561) ^ 5819814 := by rw [pow_add]
          _ = 55698974 := by rw [factor_2_22]; decide
      have factor_2_24 : (71 : ZMod 232792561) ^ 23279256 = 225776535 := by
        calc
          (71 : ZMod 232792561) ^ 23279256 = (71 : ZMod 232792561) ^ (11639628 + 11639628) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 11639628 * (71 : ZMod 232792561) ^ 11639628 := by rw [pow_add]
          _ = 225776535 := by rw [factor_2_23]; decide
      have factor_2_25 : (71 : ZMod 232792561) ^ 46558512 = 168224104 := by
        calc
          (71 : ZMod 232792561) ^ 46558512 = (71 : ZMod 232792561) ^ (23279256 + 23279256) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 23279256 * (71 : ZMod 232792561) ^ 23279256 := by rw [pow_add]
          _ = 168224104 := by rw [factor_2_24]; decide
      change (71 : ZMod 232792561) ^ 46558512 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (71 : ZMod 232792561) ^ 1 = 71 := by norm_num
      have factor_3_1 : (71 : ZMod 232792561) ^ 3 = 357911 := by
        calc
          (71 : ZMod 232792561) ^ 3 = (71 : ZMod 232792561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1 * (71 : ZMod 232792561) ^ 1) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 357911 := by rw [factor_3_0]; decide
      have factor_3_2 : (71 : ZMod 232792561) ^ 7 = 147592682 := by
        calc
          (71 : ZMod 232792561) ^ 7 = (71 : ZMod 232792561) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 3 * (71 : ZMod 232792561) ^ 3) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 147592682 := by rw [factor_3_1]; decide
      have factor_3_3 : (71 : ZMod 232792561) ^ 15 = 109059220 := by
        calc
          (71 : ZMod 232792561) ^ 15 = (71 : ZMod 232792561) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 7 * (71 : ZMod 232792561) ^ 7) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 109059220 := by rw [factor_3_2]; decide
      have factor_3_4 : (71 : ZMod 232792561) ^ 31 = 59639079 := by
        calc
          (71 : ZMod 232792561) ^ 31 = (71 : ZMod 232792561) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 15 * (71 : ZMod 232792561) ^ 15) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 59639079 := by rw [factor_3_3]; decide
      have factor_3_5 : (71 : ZMod 232792561) ^ 63 = 113917219 := by
        calc
          (71 : ZMod 232792561) ^ 63 = (71 : ZMod 232792561) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 31 * (71 : ZMod 232792561) ^ 31) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 113917219 := by rw [factor_3_4]; decide
      have factor_3_6 : (71 : ZMod 232792561) ^ 126 = 196904803 := by
        calc
          (71 : ZMod 232792561) ^ 126 = (71 : ZMod 232792561) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 63 * (71 : ZMod 232792561) ^ 63 := by rw [pow_add]
          _ = 196904803 := by rw [factor_3_5]; decide
      have factor_3_7 : (71 : ZMod 232792561) ^ 253 = 178275814 := by
        calc
          (71 : ZMod 232792561) ^ 253 = (71 : ZMod 232792561) ^ (126 + 126 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 126 * (71 : ZMod 232792561) ^ 126) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 178275814 := by rw [factor_3_6]; decide
      have factor_3_8 : (71 : ZMod 232792561) ^ 507 = 102692371 := by
        calc
          (71 : ZMod 232792561) ^ 507 = (71 : ZMod 232792561) ^ (253 + 253 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 253 * (71 : ZMod 232792561) ^ 253) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 102692371 := by rw [factor_3_7]; decide
      have factor_3_9 : (71 : ZMod 232792561) ^ 1014 = 59331496 := by
        calc
          (71 : ZMod 232792561) ^ 1014 = (71 : ZMod 232792561) ^ (507 + 507) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 507 * (71 : ZMod 232792561) ^ 507 := by rw [pow_add]
          _ = 59331496 := by rw [factor_3_8]; decide
      have factor_3_10 : (71 : ZMod 232792561) ^ 2029 = 14843456 := by
        calc
          (71 : ZMod 232792561) ^ 2029 = (71 : ZMod 232792561) ^ (1014 + 1014 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1014 * (71 : ZMod 232792561) ^ 1014) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 14843456 := by rw [factor_3_9]; decide
      have factor_3_11 : (71 : ZMod 232792561) ^ 4059 = 74628518 := by
        calc
          (71 : ZMod 232792561) ^ 4059 = (71 : ZMod 232792561) ^ (2029 + 2029 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 2029 * (71 : ZMod 232792561) ^ 2029) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 74628518 := by rw [factor_3_10]; decide
      have factor_3_12 : (71 : ZMod 232792561) ^ 8119 = 129956312 := by
        calc
          (71 : ZMod 232792561) ^ 8119 = (71 : ZMod 232792561) ^ (4059 + 4059 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 4059 * (71 : ZMod 232792561) ^ 4059) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 129956312 := by rw [factor_3_11]; decide
      have factor_3_13 : (71 : ZMod 232792561) ^ 16238 = 165473709 := by
        calc
          (71 : ZMod 232792561) ^ 16238 = (71 : ZMod 232792561) ^ (8119 + 8119) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 8119 * (71 : ZMod 232792561) ^ 8119 := by rw [pow_add]
          _ = 165473709 := by rw [factor_3_12]; decide
      have factor_3_14 : (71 : ZMod 232792561) ^ 32476 = 110566508 := by
        calc
          (71 : ZMod 232792561) ^ 32476 = (71 : ZMod 232792561) ^ (16238 + 16238) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 16238 * (71 : ZMod 232792561) ^ 16238 := by rw [pow_add]
          _ = 110566508 := by rw [factor_3_13]; decide
      have factor_3_15 : (71 : ZMod 232792561) ^ 64953 = 227464162 := by
        calc
          (71 : ZMod 232792561) ^ 64953 = (71 : ZMod 232792561) ^ (32476 + 32476 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 32476 * (71 : ZMod 232792561) ^ 32476) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 227464162 := by rw [factor_3_14]; decide
      have factor_3_16 : (71 : ZMod 232792561) ^ 129906 = 222371080 := by
        calc
          (71 : ZMod 232792561) ^ 129906 = (71 : ZMod 232792561) ^ (64953 + 64953) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 64953 * (71 : ZMod 232792561) ^ 64953 := by rw [pow_add]
          _ = 222371080 := by rw [factor_3_15]; decide
      have factor_3_17 : (71 : ZMod 232792561) ^ 259813 = 132639743 := by
        calc
          (71 : ZMod 232792561) ^ 259813 = (71 : ZMod 232792561) ^ (129906 + 129906 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 129906 * (71 : ZMod 232792561) ^ 129906) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 132639743 := by rw [factor_3_16]; decide
      have factor_3_18 : (71 : ZMod 232792561) ^ 519626 = 133642634 := by
        calc
          (71 : ZMod 232792561) ^ 519626 = (71 : ZMod 232792561) ^ (259813 + 259813) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 259813 * (71 : ZMod 232792561) ^ 259813 := by rw [pow_add]
          _ = 133642634 := by rw [factor_3_17]; decide
      have factor_3_19 : (71 : ZMod 232792561) ^ 1039252 = 156377293 := by
        calc
          (71 : ZMod 232792561) ^ 1039252 = (71 : ZMod 232792561) ^ (519626 + 519626) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 519626 * (71 : ZMod 232792561) ^ 519626 := by rw [pow_add]
          _ = 156377293 := by rw [factor_3_18]; decide
      have factor_3_20 : (71 : ZMod 232792561) ^ 2078505 = 115023626 := by
        calc
          (71 : ZMod 232792561) ^ 2078505 = (71 : ZMod 232792561) ^ (1039252 + 1039252 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1039252 * (71 : ZMod 232792561) ^ 1039252) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 115023626 := by rw [factor_3_19]; decide
      have factor_3_21 : (71 : ZMod 232792561) ^ 4157010 = 131982057 := by
        calc
          (71 : ZMod 232792561) ^ 4157010 = (71 : ZMod 232792561) ^ (2078505 + 2078505) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 2078505 * (71 : ZMod 232792561) ^ 2078505 := by rw [pow_add]
          _ = 131982057 := by rw [factor_3_20]; decide
      have factor_3_22 : (71 : ZMod 232792561) ^ 8314020 = 127017044 := by
        calc
          (71 : ZMod 232792561) ^ 8314020 = (71 : ZMod 232792561) ^ (4157010 + 4157010) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 4157010 * (71 : ZMod 232792561) ^ 4157010 := by rw [pow_add]
          _ = 127017044 := by rw [factor_3_21]; decide
      have factor_3_23 : (71 : ZMod 232792561) ^ 16628040 = 225314559 := by
        calc
          (71 : ZMod 232792561) ^ 16628040 = (71 : ZMod 232792561) ^ (8314020 + 8314020) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 8314020 * (71 : ZMod 232792561) ^ 8314020 := by rw [pow_add]
          _ = 225314559 := by rw [factor_3_22]; decide
      have factor_3_24 : (71 : ZMod 232792561) ^ 33256080 = 16078828 := by
        calc
          (71 : ZMod 232792561) ^ 33256080 = (71 : ZMod 232792561) ^ (16628040 + 16628040) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 16628040 * (71 : ZMod 232792561) ^ 16628040 := by rw [pow_add]
          _ = 16078828 := by rw [factor_3_23]; decide
      change (71 : ZMod 232792561) ^ 33256080 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (71 : ZMod 232792561) ^ 1 = 71 := by norm_num
      have factor_4_1 : (71 : ZMod 232792561) ^ 2 = 5041 := by
        calc
          (71 : ZMod 232792561) ^ 2 = (71 : ZMod 232792561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1 * (71 : ZMod 232792561) ^ 1 := by rw [pow_add]
          _ = 5041 := by rw [factor_4_0]; decide
      have factor_4_2 : (71 : ZMod 232792561) ^ 5 = 174681424 := by
        calc
          (71 : ZMod 232792561) ^ 5 = (71 : ZMod 232792561) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 2 * (71 : ZMod 232792561) ^ 2) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 174681424 := by rw [factor_4_1]; decide
      have factor_4_3 : (71 : ZMod 232792561) ^ 10 = 222050304 := by
        calc
          (71 : ZMod 232792561) ^ 10 = (71 : ZMod 232792561) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 5 * (71 : ZMod 232792561) ^ 5 := by rw [pow_add]
          _ = 222050304 := by rw [factor_4_2]; decide
      have factor_4_4 : (71 : ZMod 232792561) ^ 20 = 114588666 := by
        calc
          (71 : ZMod 232792561) ^ 20 = (71 : ZMod 232792561) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 10 * (71 : ZMod 232792561) ^ 10 := by rw [pow_add]
          _ = 114588666 := by rw [factor_4_3]; decide
      have factor_4_5 : (71 : ZMod 232792561) ^ 40 = 168388835 := by
        calc
          (71 : ZMod 232792561) ^ 40 = (71 : ZMod 232792561) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 20 * (71 : ZMod 232792561) ^ 20 := by rw [pow_add]
          _ = 168388835 := by rw [factor_4_4]; decide
      have factor_4_6 : (71 : ZMod 232792561) ^ 80 = 36132765 := by
        calc
          (71 : ZMod 232792561) ^ 80 = (71 : ZMod 232792561) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 40 * (71 : ZMod 232792561) ^ 40 := by rw [pow_add]
          _ = 36132765 := by rw [factor_4_5]; decide
      have factor_4_7 : (71 : ZMod 232792561) ^ 161 = 208143629 := by
        calc
          (71 : ZMod 232792561) ^ 161 = (71 : ZMod 232792561) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 80 * (71 : ZMod 232792561) ^ 80) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 208143629 := by rw [factor_4_6]; decide
      have factor_4_8 : (71 : ZMod 232792561) ^ 322 = 120728065 := by
        calc
          (71 : ZMod 232792561) ^ 322 = (71 : ZMod 232792561) ^ (161 + 161) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 161 * (71 : ZMod 232792561) ^ 161 := by rw [pow_add]
          _ = 120728065 := by rw [factor_4_7]; decide
      have factor_4_9 : (71 : ZMod 232792561) ^ 645 = 136078569 := by
        calc
          (71 : ZMod 232792561) ^ 645 = (71 : ZMod 232792561) ^ (322 + 322 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 322 * (71 : ZMod 232792561) ^ 322) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 136078569 := by rw [factor_4_8]; decide
      have factor_4_10 : (71 : ZMod 232792561) ^ 1291 = 19235244 := by
        calc
          (71 : ZMod 232792561) ^ 1291 = (71 : ZMod 232792561) ^ (645 + 645 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 645 * (71 : ZMod 232792561) ^ 645) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 19235244 := by rw [factor_4_9]; decide
      have factor_4_11 : (71 : ZMod 232792561) ^ 2583 = 47962651 := by
        calc
          (71 : ZMod 232792561) ^ 2583 = (71 : ZMod 232792561) ^ (1291 + 1291 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1291 * (71 : ZMod 232792561) ^ 1291) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 47962651 := by rw [factor_4_10]; decide
      have factor_4_12 : (71 : ZMod 232792561) ^ 5166 = 76258854 := by
        calc
          (71 : ZMod 232792561) ^ 5166 = (71 : ZMod 232792561) ^ (2583 + 2583) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 2583 * (71 : ZMod 232792561) ^ 2583 := by rw [pow_add]
          _ = 76258854 := by rw [factor_4_11]; decide
      have factor_4_13 : (71 : ZMod 232792561) ^ 10333 = 43880493 := by
        calc
          (71 : ZMod 232792561) ^ 10333 = (71 : ZMod 232792561) ^ (5166 + 5166 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 5166 * (71 : ZMod 232792561) ^ 5166) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 43880493 := by rw [factor_4_12]; decide
      have factor_4_14 : (71 : ZMod 232792561) ^ 20666 = 90538627 := by
        calc
          (71 : ZMod 232792561) ^ 20666 = (71 : ZMod 232792561) ^ (10333 + 10333) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 10333 * (71 : ZMod 232792561) ^ 10333 := by rw [pow_add]
          _ = 90538627 := by rw [factor_4_13]; decide
      have factor_4_15 : (71 : ZMod 232792561) ^ 41333 = 189549448 := by
        calc
          (71 : ZMod 232792561) ^ 41333 = (71 : ZMod 232792561) ^ (20666 + 20666 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 20666 * (71 : ZMod 232792561) ^ 20666) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 189549448 := by rw [factor_4_14]; decide
      have factor_4_16 : (71 : ZMod 232792561) ^ 82667 = 32012624 := by
        calc
          (71 : ZMod 232792561) ^ 82667 = (71 : ZMod 232792561) ^ (41333 + 41333 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 41333 * (71 : ZMod 232792561) ^ 41333) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 32012624 := by rw [factor_4_15]; decide
      have factor_4_17 : (71 : ZMod 232792561) ^ 165335 = 81811968 := by
        calc
          (71 : ZMod 232792561) ^ 165335 = (71 : ZMod 232792561) ^ (82667 + 82667 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 82667 * (71 : ZMod 232792561) ^ 82667) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 81811968 := by rw [factor_4_16]; decide
      have factor_4_18 : (71 : ZMod 232792561) ^ 330671 = 143805054 := by
        calc
          (71 : ZMod 232792561) ^ 330671 = (71 : ZMod 232792561) ^ (165335 + 165335 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 165335 * (71 : ZMod 232792561) ^ 165335) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 143805054 := by rw [factor_4_17]; decide
      have factor_4_19 : (71 : ZMod 232792561) ^ 661342 = 123239160 := by
        calc
          (71 : ZMod 232792561) ^ 661342 = (71 : ZMod 232792561) ^ (330671 + 330671) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 330671 * (71 : ZMod 232792561) ^ 330671 := by rw [pow_add]
          _ = 123239160 := by rw [factor_4_18]; decide
      have factor_4_20 : (71 : ZMod 232792561) ^ 1322685 = 475681 := by
        calc
          (71 : ZMod 232792561) ^ 1322685 = (71 : ZMod 232792561) ^ (661342 + 661342 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 661342 * (71 : ZMod 232792561) ^ 661342) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 475681 := by rw [factor_4_19]; decide
      have factor_4_21 : (71 : ZMod 232792561) ^ 2645370 = 230837030 := by
        calc
          (71 : ZMod 232792561) ^ 2645370 = (71 : ZMod 232792561) ^ (1322685 + 1322685) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1322685 * (71 : ZMod 232792561) ^ 1322685 := by rw [pow_add]
          _ = 230837030 := by rw [factor_4_20]; decide
      have factor_4_22 : (71 : ZMod 232792561) ^ 5290740 = 18092414 := by
        calc
          (71 : ZMod 232792561) ^ 5290740 = (71 : ZMod 232792561) ^ (2645370 + 2645370) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 2645370 * (71 : ZMod 232792561) ^ 2645370 := by rw [pow_add]
          _ = 18092414 := by rw [factor_4_21]; decide
      have factor_4_23 : (71 : ZMod 232792561) ^ 10581480 = 4511271 := by
        calc
          (71 : ZMod 232792561) ^ 10581480 = (71 : ZMod 232792561) ^ (5290740 + 5290740) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 5290740 * (71 : ZMod 232792561) ^ 5290740 := by rw [pow_add]
          _ = 4511271 := by rw [factor_4_22]; decide
      have factor_4_24 : (71 : ZMod 232792561) ^ 21162960 = 141975138 := by
        calc
          (71 : ZMod 232792561) ^ 21162960 = (71 : ZMod 232792561) ^ (10581480 + 10581480) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 10581480 * (71 : ZMod 232792561) ^ 10581480 := by rw [pow_add]
          _ = 141975138 := by rw [factor_4_23]; decide
      change (71 : ZMod 232792561) ^ 21162960 ≠ 1
      rw [factor_4_24]
      decide
    ·
      have factor_5_0 : (71 : ZMod 232792561) ^ 1 = 71 := by norm_num
      have factor_5_1 : (71 : ZMod 232792561) ^ 2 = 5041 := by
        calc
          (71 : ZMod 232792561) ^ 2 = (71 : ZMod 232792561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1 * (71 : ZMod 232792561) ^ 1 := by rw [pow_add]
          _ = 5041 := by rw [factor_5_0]; decide
      have factor_5_2 : (71 : ZMod 232792561) ^ 4 = 25411681 := by
        calc
          (71 : ZMod 232792561) ^ 4 = (71 : ZMod 232792561) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 2 * (71 : ZMod 232792561) ^ 2 := by rw [pow_add]
          _ = 25411681 := by rw [factor_5_1]; decide
      have factor_5_3 : (71 : ZMod 232792561) ^ 8 = 3415177 := by
        calc
          (71 : ZMod 232792561) ^ 8 = (71 : ZMod 232792561) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 4 * (71 : ZMod 232792561) ^ 4 := by rw [pow_add]
          _ = 3415177 := by rw [factor_5_2]; decide
      have factor_5_4 : (71 : ZMod 232792561) ^ 17 = 144291499 := by
        calc
          (71 : ZMod 232792561) ^ 17 = (71 : ZMod 232792561) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 8 * (71 : ZMod 232792561) ^ 8) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 144291499 := by rw [factor_5_3]; decide
      have factor_5_5 : (71 : ZMod 232792561) ^ 34 = 34108196 := by
        calc
          (71 : ZMod 232792561) ^ 34 = (71 : ZMod 232792561) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 17 * (71 : ZMod 232792561) ^ 17 := by rw [pow_add]
          _ = 34108196 := by rw [factor_5_4]; decide
      have factor_5_6 : (71 : ZMod 232792561) ^ 68 = 83197527 := by
        calc
          (71 : ZMod 232792561) ^ 68 = (71 : ZMod 232792561) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 34 * (71 : ZMod 232792561) ^ 34 := by rw [pow_add]
          _ = 83197527 := by rw [factor_5_5]; decide
      have factor_5_7 : (71 : ZMod 232792561) ^ 136 = 97323439 := by
        calc
          (71 : ZMod 232792561) ^ 136 = (71 : ZMod 232792561) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 68 * (71 : ZMod 232792561) ^ 68 := by rw [pow_add]
          _ = 97323439 := by rw [factor_5_6]; decide
      have factor_5_8 : (71 : ZMod 232792561) ^ 273 = 97428914 := by
        calc
          (71 : ZMod 232792561) ^ 273 = (71 : ZMod 232792561) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 136 * (71 : ZMod 232792561) ^ 136) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 97428914 := by rw [factor_5_7]; decide
      have factor_5_9 : (71 : ZMod 232792561) ^ 546 = 50881928 := by
        calc
          (71 : ZMod 232792561) ^ 546 = (71 : ZMod 232792561) ^ (273 + 273) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 273 * (71 : ZMod 232792561) ^ 273 := by rw [pow_add]
          _ = 50881928 := by rw [factor_5_8]; decide
      have factor_5_10 : (71 : ZMod 232792561) ^ 1092 = 22416541 := by
        calc
          (71 : ZMod 232792561) ^ 1092 = (71 : ZMod 232792561) ^ (546 + 546) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 546 * (71 : ZMod 232792561) ^ 546 := by rw [pow_add]
          _ = 22416541 := by rw [factor_5_9]; decide
      have factor_5_11 : (71 : ZMod 232792561) ^ 2185 = 220038469 := by
        calc
          (71 : ZMod 232792561) ^ 2185 = (71 : ZMod 232792561) ^ (1092 + 1092 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1092 * (71 : ZMod 232792561) ^ 1092) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 220038469 := by rw [factor_5_10]; decide
      have factor_5_12 : (71 : ZMod 232792561) ^ 4371 = 117486281 := by
        calc
          (71 : ZMod 232792561) ^ 4371 = (71 : ZMod 232792561) ^ (2185 + 2185 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 2185 * (71 : ZMod 232792561) ^ 2185) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 117486281 := by rw [factor_5_11]; decide
      have factor_5_13 : (71 : ZMod 232792561) ^ 8743 = 57599076 := by
        calc
          (71 : ZMod 232792561) ^ 8743 = (71 : ZMod 232792561) ^ (4371 + 4371 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 4371 * (71 : ZMod 232792561) ^ 4371) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 57599076 := by rw [factor_5_12]; decide
      have factor_5_14 : (71 : ZMod 232792561) ^ 17487 = 157451153 := by
        calc
          (71 : ZMod 232792561) ^ 17487 = (71 : ZMod 232792561) ^ (8743 + 8743 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 8743 * (71 : ZMod 232792561) ^ 8743) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 157451153 := by rw [factor_5_13]; decide
      have factor_5_15 : (71 : ZMod 232792561) ^ 34974 = 85246034 := by
        calc
          (71 : ZMod 232792561) ^ 34974 = (71 : ZMod 232792561) ^ (17487 + 17487) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 17487 * (71 : ZMod 232792561) ^ 17487 := by rw [pow_add]
          _ = 85246034 := by rw [factor_5_14]; decide
      have factor_5_16 : (71 : ZMod 232792561) ^ 69949 = 222991630 := by
        calc
          (71 : ZMod 232792561) ^ 69949 = (71 : ZMod 232792561) ^ (34974 + 34974 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 34974 * (71 : ZMod 232792561) ^ 34974) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 222991630 := by rw [factor_5_15]; decide
      have factor_5_17 : (71 : ZMod 232792561) ^ 139899 = 109102420 := by
        calc
          (71 : ZMod 232792561) ^ 139899 = (71 : ZMod 232792561) ^ (69949 + 69949 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 69949 * (71 : ZMod 232792561) ^ 69949) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 109102420 := by rw [factor_5_16]; decide
      have factor_5_18 : (71 : ZMod 232792561) ^ 279798 = 26037429 := by
        calc
          (71 : ZMod 232792561) ^ 279798 = (71 : ZMod 232792561) ^ (139899 + 139899) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 139899 * (71 : ZMod 232792561) ^ 139899 := by rw [pow_add]
          _ = 26037429 := by rw [factor_5_17]; decide
      have factor_5_19 : (71 : ZMod 232792561) ^ 559597 = 193490862 := by
        calc
          (71 : ZMod 232792561) ^ 559597 = (71 : ZMod 232792561) ^ (279798 + 279798 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 279798 * (71 : ZMod 232792561) ^ 279798) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 193490862 := by rw [factor_5_18]; decide
      have factor_5_20 : (71 : ZMod 232792561) ^ 1119195 = 184333337 := by
        calc
          (71 : ZMod 232792561) ^ 1119195 = (71 : ZMod 232792561) ^ (559597 + 559597 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 559597 * (71 : ZMod 232792561) ^ 559597) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 184333337 := by rw [factor_5_19]; decide
      have factor_5_21 : (71 : ZMod 232792561) ^ 2238390 = 34839310 := by
        calc
          (71 : ZMod 232792561) ^ 2238390 = (71 : ZMod 232792561) ^ (1119195 + 1119195) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1119195 * (71 : ZMod 232792561) ^ 1119195 := by rw [pow_add]
          _ = 34839310 := by rw [factor_5_20]; decide
      have factor_5_22 : (71 : ZMod 232792561) ^ 4476780 = 134525393 := by
        calc
          (71 : ZMod 232792561) ^ 4476780 = (71 : ZMod 232792561) ^ (2238390 + 2238390) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 2238390 * (71 : ZMod 232792561) ^ 2238390 := by rw [pow_add]
          _ = 134525393 := by rw [factor_5_21]; decide
      have factor_5_23 : (71 : ZMod 232792561) ^ 8953560 = 209272642 := by
        calc
          (71 : ZMod 232792561) ^ 8953560 = (71 : ZMod 232792561) ^ (4476780 + 4476780) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 4476780 * (71 : ZMod 232792561) ^ 4476780 := by rw [pow_add]
          _ = 209272642 := by rw [factor_5_22]; decide
      have factor_5_24 : (71 : ZMod 232792561) ^ 17907120 = 230306895 := by
        calc
          (71 : ZMod 232792561) ^ 17907120 = (71 : ZMod 232792561) ^ (8953560 + 8953560) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 8953560 * (71 : ZMod 232792561) ^ 8953560 := by rw [pow_add]
          _ = 230306895 := by rw [factor_5_23]; decide
      change (71 : ZMod 232792561) ^ 17907120 ≠ 1
      rw [factor_5_24]
      decide
    ·
      have factor_6_0 : (71 : ZMod 232792561) ^ 1 = 71 := by norm_num
      have factor_6_1 : (71 : ZMod 232792561) ^ 3 = 357911 := by
        calc
          (71 : ZMod 232792561) ^ 3 = (71 : ZMod 232792561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1 * (71 : ZMod 232792561) ^ 1) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 357911 := by rw [factor_6_0]; decide
      have factor_6_2 : (71 : ZMod 232792561) ^ 6 = 64375371 := by
        calc
          (71 : ZMod 232792561) ^ 6 = (71 : ZMod 232792561) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 3 * (71 : ZMod 232792561) ^ 3 := by rw [pow_add]
          _ = 64375371 := by rw [factor_6_1]; decide
      have factor_6_3 : (71 : ZMod 232792561) ^ 13 = 29992349 := by
        calc
          (71 : ZMod 232792561) ^ 13 = (71 : ZMod 232792561) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 6 * (71 : ZMod 232792561) ^ 6) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 29992349 := by rw [factor_6_2]; decide
      have factor_6_4 : (71 : ZMod 232792561) ^ 26 = 47008310 := by
        calc
          (71 : ZMod 232792561) ^ 26 = (71 : ZMod 232792561) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 13 * (71 : ZMod 232792561) ^ 13 := by rw [pow_add]
          _ = 47008310 := by rw [factor_6_3]; decide
      have factor_6_5 : (71 : ZMod 232792561) ^ 52 = 151689210 := by
        calc
          (71 : ZMod 232792561) ^ 52 = (71 : ZMod 232792561) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 26 * (71 : ZMod 232792561) ^ 26 := by rw [pow_add]
          _ = 151689210 := by rw [factor_6_4]; decide
      have factor_6_6 : (71 : ZMod 232792561) ^ 104 = 229149424 := by
        calc
          (71 : ZMod 232792561) ^ 104 = (71 : ZMod 232792561) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 52 * (71 : ZMod 232792561) ^ 52 := by rw [pow_add]
          _ = 229149424 := by rw [factor_6_5]; decide
      have factor_6_7 : (71 : ZMod 232792561) ^ 208 = 12127915 := by
        calc
          (71 : ZMod 232792561) ^ 208 = (71 : ZMod 232792561) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 104 * (71 : ZMod 232792561) ^ 104 := by rw [pow_add]
          _ = 12127915 := by rw [factor_6_6]; decide
      have factor_6_8 : (71 : ZMod 232792561) ^ 417 = 119633701 := by
        calc
          (71 : ZMod 232792561) ^ 417 = (71 : ZMod 232792561) ^ (208 + 208 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 208 * (71 : ZMod 232792561) ^ 208) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 119633701 := by rw [factor_6_7]; decide
      have factor_6_9 : (71 : ZMod 232792561) ^ 835 = 50522144 := by
        calc
          (71 : ZMod 232792561) ^ 835 = (71 : ZMod 232792561) ^ (417 + 417 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 417 * (71 : ZMod 232792561) ^ 417) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 50522144 := by rw [factor_6_8]; decide
      have factor_6_10 : (71 : ZMod 232792561) ^ 1671 = 123994852 := by
        calc
          (71 : ZMod 232792561) ^ 1671 = (71 : ZMod 232792561) ^ (835 + 835 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 835 * (71 : ZMod 232792561) ^ 835) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 123994852 := by rw [factor_6_9]; decide
      have factor_6_11 : (71 : ZMod 232792561) ^ 3343 = 230396982 := by
        calc
          (71 : ZMod 232792561) ^ 3343 = (71 : ZMod 232792561) ^ (1671 + 1671 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1671 * (71 : ZMod 232792561) ^ 1671) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 230396982 := by rw [factor_6_10]; decide
      have factor_6_12 : (71 : ZMod 232792561) ^ 6686 = 229324030 := by
        calc
          (71 : ZMod 232792561) ^ 6686 = (71 : ZMod 232792561) ^ (3343 + 3343) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 3343 * (71 : ZMod 232792561) ^ 3343 := by rw [pow_add]
          _ = 229324030 := by rw [factor_6_11]; decide
      have factor_6_13 : (71 : ZMod 232792561) ^ 13372 = 220538042 := by
        calc
          (71 : ZMod 232792561) ^ 13372 = (71 : ZMod 232792561) ^ (6686 + 6686) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 6686 * (71 : ZMod 232792561) ^ 6686 := by rw [pow_add]
          _ = 220538042 := by rw [factor_6_12]; decide
      have factor_6_14 : (71 : ZMod 232792561) ^ 26745 = 53411711 := by
        calc
          (71 : ZMod 232792561) ^ 26745 = (71 : ZMod 232792561) ^ (13372 + 13372 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 13372 * (71 : ZMod 232792561) ^ 13372) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 53411711 := by rw [factor_6_13]; decide
      have factor_6_15 : (71 : ZMod 232792561) ^ 53490 = 192506308 := by
        calc
          (71 : ZMod 232792561) ^ 53490 = (71 : ZMod 232792561) ^ (26745 + 26745) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 26745 * (71 : ZMod 232792561) ^ 26745 := by rw [pow_add]
          _ = 192506308 := by rw [factor_6_14]; decide
      have factor_6_16 : (71 : ZMod 232792561) ^ 106981 = 52953383 := by
        calc
          (71 : ZMod 232792561) ^ 106981 = (71 : ZMod 232792561) ^ (53490 + 53490 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 53490 * (71 : ZMod 232792561) ^ 53490) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 52953383 := by rw [factor_6_15]; decide
      have factor_6_17 : (71 : ZMod 232792561) ^ 213963 = 113216756 := by
        calc
          (71 : ZMod 232792561) ^ 213963 = (71 : ZMod 232792561) ^ (106981 + 106981 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 106981 * (71 : ZMod 232792561) ^ 106981) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 113216756 := by rw [factor_6_16]; decide
      have factor_6_18 : (71 : ZMod 232792561) ^ 427927 = 178820934 := by
        calc
          (71 : ZMod 232792561) ^ 427927 = (71 : ZMod 232792561) ^ (213963 + 213963 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 213963 * (71 : ZMod 232792561) ^ 213963) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 178820934 := by rw [factor_6_17]; decide
      have factor_6_19 : (71 : ZMod 232792561) ^ 855855 = 133291062 := by
        calc
          (71 : ZMod 232792561) ^ 855855 = (71 : ZMod 232792561) ^ (427927 + 427927 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 427927 * (71 : ZMod 232792561) ^ 427927) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 133291062 := by rw [factor_6_18]; decide
      have factor_6_20 : (71 : ZMod 232792561) ^ 1711710 = 106500794 := by
        calc
          (71 : ZMod 232792561) ^ 1711710 = (71 : ZMod 232792561) ^ (855855 + 855855) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 855855 * (71 : ZMod 232792561) ^ 855855 := by rw [pow_add]
          _ = 106500794 := by rw [factor_6_19]; decide
      have factor_6_21 : (71 : ZMod 232792561) ^ 3423420 = 128769868 := by
        calc
          (71 : ZMod 232792561) ^ 3423420 = (71 : ZMod 232792561) ^ (1711710 + 1711710) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1711710 * (71 : ZMod 232792561) ^ 1711710 := by rw [pow_add]
          _ = 128769868 := by rw [factor_6_20]; decide
      have factor_6_22 : (71 : ZMod 232792561) ^ 6846840 = 37185365 := by
        calc
          (71 : ZMod 232792561) ^ 6846840 = (71 : ZMod 232792561) ^ (3423420 + 3423420) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 3423420 * (71 : ZMod 232792561) ^ 3423420 := by rw [pow_add]
          _ = 37185365 := by rw [factor_6_21]; decide
      have factor_6_23 : (71 : ZMod 232792561) ^ 13693680 = 106275302 := by
        calc
          (71 : ZMod 232792561) ^ 13693680 = (71 : ZMod 232792561) ^ (6846840 + 6846840) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 6846840 * (71 : ZMod 232792561) ^ 6846840 := by rw [pow_add]
          _ = 106275302 := by rw [factor_6_22]; decide
      change (71 : ZMod 232792561) ^ 13693680 ≠ 1
      rw [factor_6_23]
      decide
    ·
      have factor_7_0 : (71 : ZMod 232792561) ^ 1 = 71 := by norm_num
      have factor_7_1 : (71 : ZMod 232792561) ^ 2 = 5041 := by
        calc
          (71 : ZMod 232792561) ^ 2 = (71 : ZMod 232792561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1 * (71 : ZMod 232792561) ^ 1 := by rw [pow_add]
          _ = 5041 := by rw [factor_7_0]; decide
      have factor_7_2 : (71 : ZMod 232792561) ^ 5 = 174681424 := by
        calc
          (71 : ZMod 232792561) ^ 5 = (71 : ZMod 232792561) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 2 * (71 : ZMod 232792561) ^ 2) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 174681424 := by rw [factor_7_1]; decide
      have factor_7_3 : (71 : ZMod 232792561) ^ 11 = 168469997 := by
        calc
          (71 : ZMod 232792561) ^ 11 = (71 : ZMod 232792561) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 5 * (71 : ZMod 232792561) ^ 5) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 168469997 := by rw [factor_7_2]; decide
      have factor_7_4 : (71 : ZMod 232792561) ^ 23 = 81809990 := by
        calc
          (71 : ZMod 232792561) ^ 23 = (71 : ZMod 232792561) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 11 * (71 : ZMod 232792561) ^ 11) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 81809990 := by rw [factor_7_3]; decide
      have factor_7_5 : (71 : ZMod 232792561) ^ 46 = 106669481 := by
        calc
          (71 : ZMod 232792561) ^ 46 = (71 : ZMod 232792561) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 23 * (71 : ZMod 232792561) ^ 23 := by rw [pow_add]
          _ = 106669481 := by rw [factor_7_4]; decide
      have factor_7_6 : (71 : ZMod 232792561) ^ 93 = 92582540 := by
        calc
          (71 : ZMod 232792561) ^ 93 = (71 : ZMod 232792561) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 46 * (71 : ZMod 232792561) ^ 46) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 92582540 := by rw [factor_7_5]; decide
      have factor_7_7 : (71 : ZMod 232792561) ^ 186 = 92971711 := by
        calc
          (71 : ZMod 232792561) ^ 186 = (71 : ZMod 232792561) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 93 * (71 : ZMod 232792561) ^ 93 := by rw [pow_add]
          _ = 92971711 := by rw [factor_7_6]; decide
      have factor_7_8 : (71 : ZMod 232792561) ^ 373 = 13539939 := by
        calc
          (71 : ZMod 232792561) ^ 373 = (71 : ZMod 232792561) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 186 * (71 : ZMod 232792561) ^ 186) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 13539939 := by rw [factor_7_7]; decide
      have factor_7_9 : (71 : ZMod 232792561) ^ 747 = 207038721 := by
        calc
          (71 : ZMod 232792561) ^ 747 = (71 : ZMod 232792561) ^ (373 + 373 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 373 * (71 : ZMod 232792561) ^ 373) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 207038721 := by rw [factor_7_8]; decide
      have factor_7_10 : (71 : ZMod 232792561) ^ 1495 = 145363589 := by
        calc
          (71 : ZMod 232792561) ^ 1495 = (71 : ZMod 232792561) ^ (747 + 747 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 747 * (71 : ZMod 232792561) ^ 747) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 145363589 := by rw [factor_7_9]; decide
      have factor_7_11 : (71 : ZMod 232792561) ^ 2991 = 181554717 := by
        calc
          (71 : ZMod 232792561) ^ 2991 = (71 : ZMod 232792561) ^ (1495 + 1495 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 1495 * (71 : ZMod 232792561) ^ 1495) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 181554717 := by rw [factor_7_10]; decide
      have factor_7_12 : (71 : ZMod 232792561) ^ 5982 = 180638763 := by
        calc
          (71 : ZMod 232792561) ^ 5982 = (71 : ZMod 232792561) ^ (2991 + 2991) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 2991 * (71 : ZMod 232792561) ^ 2991 := by rw [pow_add]
          _ = 180638763 := by rw [factor_7_11]; decide
      have factor_7_13 : (71 : ZMod 232792561) ^ 11965 = 51798024 := by
        calc
          (71 : ZMod 232792561) ^ 11965 = (71 : ZMod 232792561) ^ (5982 + 5982 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 5982 * (71 : ZMod 232792561) ^ 5982) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 51798024 := by rw [factor_7_12]; decide
      have factor_7_14 : (71 : ZMod 232792561) ^ 23930 = 225600663 := by
        calc
          (71 : ZMod 232792561) ^ 23930 = (71 : ZMod 232792561) ^ (11965 + 11965) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 11965 * (71 : ZMod 232792561) ^ 11965 := by rw [pow_add]
          _ = 225600663 := by rw [factor_7_13]; decide
      have factor_7_15 : (71 : ZMod 232792561) ^ 47860 = 148884058 := by
        calc
          (71 : ZMod 232792561) ^ 47860 = (71 : ZMod 232792561) ^ (23930 + 23930) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 23930 * (71 : ZMod 232792561) ^ 23930 := by rw [pow_add]
          _ = 148884058 := by rw [factor_7_14]; decide
      have factor_7_16 : (71 : ZMod 232792561) ^ 95720 = 229884198 := by
        calc
          (71 : ZMod 232792561) ^ 95720 = (71 : ZMod 232792561) ^ (47860 + 47860) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 47860 * (71 : ZMod 232792561) ^ 47860 := by rw [pow_add]
          _ = 229884198 := by rw [factor_7_15]; decide
      have factor_7_17 : (71 : ZMod 232792561) ^ 191441 = 134670677 := by
        calc
          (71 : ZMod 232792561) ^ 191441 = (71 : ZMod 232792561) ^ (95720 + 95720 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 95720 * (71 : ZMod 232792561) ^ 95720) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 134670677 := by rw [factor_7_16]; decide
      have factor_7_18 : (71 : ZMod 232792561) ^ 382882 = 9688278 := by
        calc
          (71 : ZMod 232792561) ^ 382882 = (71 : ZMod 232792561) ^ (191441 + 191441) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 191441 * (71 : ZMod 232792561) ^ 191441 := by rw [pow_add]
          _ = 9688278 := by rw [factor_7_17]; decide
      have factor_7_19 : (71 : ZMod 232792561) ^ 765765 = 197256690 := by
        calc
          (71 : ZMod 232792561) ^ 765765 = (71 : ZMod 232792561) ^ (382882 + 382882 + 1) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = ((71 : ZMod 232792561) ^ 382882 * (71 : ZMod 232792561) ^ 382882) * (71 : ZMod 232792561) := by rw [pow_succ, pow_add]
          _ = 197256690 := by rw [factor_7_18]; decide
      have factor_7_20 : (71 : ZMod 232792561) ^ 1531530 = 214652798 := by
        calc
          (71 : ZMod 232792561) ^ 1531530 = (71 : ZMod 232792561) ^ (765765 + 765765) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 765765 * (71 : ZMod 232792561) ^ 765765 := by rw [pow_add]
          _ = 214652798 := by rw [factor_7_19]; decide
      have factor_7_21 : (71 : ZMod 232792561) ^ 3063060 = 113478035 := by
        calc
          (71 : ZMod 232792561) ^ 3063060 = (71 : ZMod 232792561) ^ (1531530 + 1531530) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 1531530 * (71 : ZMod 232792561) ^ 1531530 := by rw [pow_add]
          _ = 113478035 := by rw [factor_7_20]; decide
      have factor_7_22 : (71 : ZMod 232792561) ^ 6126120 = 81133628 := by
        calc
          (71 : ZMod 232792561) ^ 6126120 = (71 : ZMod 232792561) ^ (3063060 + 3063060) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 3063060 * (71 : ZMod 232792561) ^ 3063060 := by rw [pow_add]
          _ = 81133628 := by rw [factor_7_21]; decide
      have factor_7_23 : (71 : ZMod 232792561) ^ 12252240 = 122332946 := by
        calc
          (71 : ZMod 232792561) ^ 12252240 = (71 : ZMod 232792561) ^ (6126120 + 6126120) :=
            congrArg (fun n : ℕ => (71 : ZMod 232792561) ^ n) (by norm_num)
          _ = (71 : ZMod 232792561) ^ 6126120 * (71 : ZMod 232792561) ^ 6126120 := by rw [pow_add]
          _ = 122332946 := by rw [factor_7_22]; decide
      change (71 : ZMod 232792561) ^ 12252240 ≠ 1
      rw [factor_7_23]
      decide

#print axioms prime_lucas_232792561

end TotientTailPeriodKiller
end Erdos249257
