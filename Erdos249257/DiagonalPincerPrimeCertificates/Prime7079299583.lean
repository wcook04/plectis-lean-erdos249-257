import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_7079299583 : Nat.Prime 7079299583 := by
  apply lucas_primality 7079299583 (5 : ZMod 7079299583)
  ·
      have fermat_0 : (5 : ZMod 7079299583) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 7079299583) ^ 3 = 125 := by
        calc
          (5 : ZMod 7079299583) ^ 3 = (5 : ZMod 7079299583) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1 * (5 : ZMod 7079299583) ^ 1) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 7079299583) ^ 6 = 15625 := by
        calc
          (5 : ZMod 7079299583) ^ 6 = (5 : ZMod 7079299583) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 3 * (5 : ZMod 7079299583) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 7079299583) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 7079299583) ^ 13 = (5 : ZMod 7079299583) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 6 * (5 : ZMod 7079299583) ^ 6) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 7079299583) ^ 26 = 6519462442 := by
        calc
          (5 : ZMod 7079299583) ^ 26 = (5 : ZMod 7079299583) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 13 * (5 : ZMod 7079299583) ^ 13 := by rw [pow_add]
          _ = 6519462442 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 7079299583) ^ 52 = 6188146766 := by
        calc
          (5 : ZMod 7079299583) ^ 52 = (5 : ZMod 7079299583) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 26 * (5 : ZMod 7079299583) ^ 26 := by rw [pow_add]
          _ = 6188146766 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 7079299583) ^ 105 = 4301245610 := by
        calc
          (5 : ZMod 7079299583) ^ 105 = (5 : ZMod 7079299583) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 52 * (5 : ZMod 7079299583) ^ 52) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4301245610 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 7079299583) ^ 210 = 3506267085 := by
        calc
          (5 : ZMod 7079299583) ^ 210 = (5 : ZMod 7079299583) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 105 * (5 : ZMod 7079299583) ^ 105 := by rw [pow_add]
          _ = 3506267085 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 7079299583) ^ 421 = 2565265886 := by
        calc
          (5 : ZMod 7079299583) ^ 421 = (5 : ZMod 7079299583) ^ (210 + 210 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 210 * (5 : ZMod 7079299583) ^ 210) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2565265886 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 7079299583) ^ 843 = 1538973217 := by
        calc
          (5 : ZMod 7079299583) ^ 843 = (5 : ZMod 7079299583) ^ (421 + 421 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 421 * (5 : ZMod 7079299583) ^ 421) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1538973217 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 7079299583) ^ 1687 = 604438892 := by
        calc
          (5 : ZMod 7079299583) ^ 1687 = (5 : ZMod 7079299583) ^ (843 + 843 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 843 * (5 : ZMod 7079299583) ^ 843) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 604438892 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 7079299583) ^ 3375 = 4125094071 := by
        calc
          (5 : ZMod 7079299583) ^ 3375 = (5 : ZMod 7079299583) ^ (1687 + 1687 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1687 * (5 : ZMod 7079299583) ^ 1687) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4125094071 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 7079299583) ^ 6751 = 2165181082 := by
        calc
          (5 : ZMod 7079299583) ^ 6751 = (5 : ZMod 7079299583) ^ (3375 + 3375 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 3375 * (5 : ZMod 7079299583) ^ 3375) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2165181082 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 7079299583) ^ 13502 = 4218200288 := by
        calc
          (5 : ZMod 7079299583) ^ 13502 = (5 : ZMod 7079299583) ^ (6751 + 6751) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 6751 * (5 : ZMod 7079299583) ^ 6751 := by rw [pow_add]
          _ = 4218200288 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 7079299583) ^ 27005 = 562484590 := by
        calc
          (5 : ZMod 7079299583) ^ 27005 = (5 : ZMod 7079299583) ^ (13502 + 13502 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 13502 * (5 : ZMod 7079299583) ^ 13502) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 562484590 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 7079299583) ^ 54010 = 428782557 := by
        calc
          (5 : ZMod 7079299583) ^ 54010 = (5 : ZMod 7079299583) ^ (27005 + 27005) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 27005 * (5 : ZMod 7079299583) ^ 27005 := by rw [pow_add]
          _ = 428782557 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 7079299583) ^ 108021 = 4112934522 := by
        calc
          (5 : ZMod 7079299583) ^ 108021 = (5 : ZMod 7079299583) ^ (54010 + 54010 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 54010 * (5 : ZMod 7079299583) ^ 54010) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4112934522 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 7079299583) ^ 216043 = 4883313621 := by
        calc
          (5 : ZMod 7079299583) ^ 216043 = (5 : ZMod 7079299583) ^ (108021 + 108021 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 108021 * (5 : ZMod 7079299583) ^ 108021) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4883313621 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 7079299583) ^ 432086 = 4256464072 := by
        calc
          (5 : ZMod 7079299583) ^ 432086 = (5 : ZMod 7079299583) ^ (216043 + 216043) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 216043 * (5 : ZMod 7079299583) ^ 216043 := by rw [pow_add]
          _ = 4256464072 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 7079299583) ^ 864172 = 671838746 := by
        calc
          (5 : ZMod 7079299583) ^ 864172 = (5 : ZMod 7079299583) ^ (432086 + 432086) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 432086 * (5 : ZMod 7079299583) ^ 432086 := by rw [pow_add]
          _ = 671838746 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 7079299583) ^ 1728344 = 1259951683 := by
        calc
          (5 : ZMod 7079299583) ^ 1728344 = (5 : ZMod 7079299583) ^ (864172 + 864172) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 864172 * (5 : ZMod 7079299583) ^ 864172 := by rw [pow_add]
          _ = 1259951683 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 7079299583) ^ 3456689 = 5059605403 := by
        calc
          (5 : ZMod 7079299583) ^ 3456689 = (5 : ZMod 7079299583) ^ (1728344 + 1728344 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1728344 * (5 : ZMod 7079299583) ^ 1728344) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 5059605403 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 7079299583) ^ 6913378 = 1700622881 := by
        calc
          (5 : ZMod 7079299583) ^ 6913378 = (5 : ZMod 7079299583) ^ (3456689 + 3456689) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 3456689 * (5 : ZMod 7079299583) ^ 3456689 := by rw [pow_add]
          _ = 1700622881 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 7079299583) ^ 13826756 = 3197252389 := by
        calc
          (5 : ZMod 7079299583) ^ 13826756 = (5 : ZMod 7079299583) ^ (6913378 + 6913378) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 6913378 * (5 : ZMod 7079299583) ^ 6913378 := by rw [pow_add]
          _ = 3197252389 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 7079299583) ^ 27653513 = 5826078498 := by
        calc
          (5 : ZMod 7079299583) ^ 27653513 = (5 : ZMod 7079299583) ^ (13826756 + 13826756 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 13826756 * (5 : ZMod 7079299583) ^ 13826756) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 5826078498 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 7079299583) ^ 55307027 = 3248866362 := by
        calc
          (5 : ZMod 7079299583) ^ 55307027 = (5 : ZMod 7079299583) ^ (27653513 + 27653513 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 27653513 * (5 : ZMod 7079299583) ^ 27653513) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 3248866362 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 7079299583) ^ 110614055 = 2517027628 := by
        calc
          (5 : ZMod 7079299583) ^ 110614055 = (5 : ZMod 7079299583) ^ (55307027 + 55307027 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 55307027 * (5 : ZMod 7079299583) ^ 55307027) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2517027628 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 7079299583) ^ 221228111 = 6739704017 := by
        calc
          (5 : ZMod 7079299583) ^ 221228111 = (5 : ZMod 7079299583) ^ (110614055 + 110614055 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 110614055 * (5 : ZMod 7079299583) ^ 110614055) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 6739704017 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 7079299583) ^ 442456223 = 6179640487 := by
        calc
          (5 : ZMod 7079299583) ^ 442456223 = (5 : ZMod 7079299583) ^ (221228111 + 221228111 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 221228111 * (5 : ZMod 7079299583) ^ 221228111) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 6179640487 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 7079299583) ^ 884912447 = 2005430557 := by
        calc
          (5 : ZMod 7079299583) ^ 884912447 = (5 : ZMod 7079299583) ^ (442456223 + 442456223 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 442456223 * (5 : ZMod 7079299583) ^ 442456223) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2005430557 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 7079299583) ^ 1769824895 = 2199229961 := by
        calc
          (5 : ZMod 7079299583) ^ 1769824895 = (5 : ZMod 7079299583) ^ (884912447 + 884912447 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 884912447 * (5 : ZMod 7079299583) ^ 884912447) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2199229961 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 7079299583) ^ 3539649791 = 7079299582 := by
        calc
          (5 : ZMod 7079299583) ^ 3539649791 = (5 : ZMod 7079299583) ^ (1769824895 + 1769824895 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1769824895 * (5 : ZMod 7079299583) ^ 1769824895) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 7079299582 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 7079299583) ^ 7079299582 = 1 := by
        calc
          (5 : ZMod 7079299583) ^ 7079299582 = (5 : ZMod 7079299583) ^ (3539649791 + 3539649791) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 3539649791 * (5 : ZMod 7079299583) ^ 3539649791 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (43, 2), (83233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (43, 2), (83233, 1)] : List FactorBlock).map factorBlockValue).prod = 7079299583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 7079299583) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 7079299583) ^ 3 = 125 := by
        calc
          (5 : ZMod 7079299583) ^ 3 = (5 : ZMod 7079299583) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1 * (5 : ZMod 7079299583) ^ 1) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 7079299583) ^ 6 = 15625 := by
        calc
          (5 : ZMod 7079299583) ^ 6 = (5 : ZMod 7079299583) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 3 * (5 : ZMod 7079299583) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 7079299583) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 7079299583) ^ 13 = (5 : ZMod 7079299583) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 6 * (5 : ZMod 7079299583) ^ 6) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 7079299583) ^ 26 = 6519462442 := by
        calc
          (5 : ZMod 7079299583) ^ 26 = (5 : ZMod 7079299583) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 13 * (5 : ZMod 7079299583) ^ 13 := by rw [pow_add]
          _ = 6519462442 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 7079299583) ^ 52 = 6188146766 := by
        calc
          (5 : ZMod 7079299583) ^ 52 = (5 : ZMod 7079299583) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 26 * (5 : ZMod 7079299583) ^ 26 := by rw [pow_add]
          _ = 6188146766 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 7079299583) ^ 105 = 4301245610 := by
        calc
          (5 : ZMod 7079299583) ^ 105 = (5 : ZMod 7079299583) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 52 * (5 : ZMod 7079299583) ^ 52) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4301245610 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 7079299583) ^ 210 = 3506267085 := by
        calc
          (5 : ZMod 7079299583) ^ 210 = (5 : ZMod 7079299583) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 105 * (5 : ZMod 7079299583) ^ 105 := by rw [pow_add]
          _ = 3506267085 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 7079299583) ^ 421 = 2565265886 := by
        calc
          (5 : ZMod 7079299583) ^ 421 = (5 : ZMod 7079299583) ^ (210 + 210 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 210 * (5 : ZMod 7079299583) ^ 210) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2565265886 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 7079299583) ^ 843 = 1538973217 := by
        calc
          (5 : ZMod 7079299583) ^ 843 = (5 : ZMod 7079299583) ^ (421 + 421 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 421 * (5 : ZMod 7079299583) ^ 421) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1538973217 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 7079299583) ^ 1687 = 604438892 := by
        calc
          (5 : ZMod 7079299583) ^ 1687 = (5 : ZMod 7079299583) ^ (843 + 843 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 843 * (5 : ZMod 7079299583) ^ 843) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 604438892 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 7079299583) ^ 3375 = 4125094071 := by
        calc
          (5 : ZMod 7079299583) ^ 3375 = (5 : ZMod 7079299583) ^ (1687 + 1687 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1687 * (5 : ZMod 7079299583) ^ 1687) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4125094071 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 7079299583) ^ 6751 = 2165181082 := by
        calc
          (5 : ZMod 7079299583) ^ 6751 = (5 : ZMod 7079299583) ^ (3375 + 3375 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 3375 * (5 : ZMod 7079299583) ^ 3375) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2165181082 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 7079299583) ^ 13502 = 4218200288 := by
        calc
          (5 : ZMod 7079299583) ^ 13502 = (5 : ZMod 7079299583) ^ (6751 + 6751) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 6751 * (5 : ZMod 7079299583) ^ 6751 := by rw [pow_add]
          _ = 4218200288 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 7079299583) ^ 27005 = 562484590 := by
        calc
          (5 : ZMod 7079299583) ^ 27005 = (5 : ZMod 7079299583) ^ (13502 + 13502 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 13502 * (5 : ZMod 7079299583) ^ 13502) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 562484590 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 7079299583) ^ 54010 = 428782557 := by
        calc
          (5 : ZMod 7079299583) ^ 54010 = (5 : ZMod 7079299583) ^ (27005 + 27005) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 27005 * (5 : ZMod 7079299583) ^ 27005 := by rw [pow_add]
          _ = 428782557 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 7079299583) ^ 108021 = 4112934522 := by
        calc
          (5 : ZMod 7079299583) ^ 108021 = (5 : ZMod 7079299583) ^ (54010 + 54010 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 54010 * (5 : ZMod 7079299583) ^ 54010) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4112934522 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 7079299583) ^ 216043 = 4883313621 := by
        calc
          (5 : ZMod 7079299583) ^ 216043 = (5 : ZMod 7079299583) ^ (108021 + 108021 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 108021 * (5 : ZMod 7079299583) ^ 108021) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4883313621 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 7079299583) ^ 432086 = 4256464072 := by
        calc
          (5 : ZMod 7079299583) ^ 432086 = (5 : ZMod 7079299583) ^ (216043 + 216043) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 216043 * (5 : ZMod 7079299583) ^ 216043 := by rw [pow_add]
          _ = 4256464072 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 7079299583) ^ 864172 = 671838746 := by
        calc
          (5 : ZMod 7079299583) ^ 864172 = (5 : ZMod 7079299583) ^ (432086 + 432086) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 432086 * (5 : ZMod 7079299583) ^ 432086 := by rw [pow_add]
          _ = 671838746 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 7079299583) ^ 1728344 = 1259951683 := by
        calc
          (5 : ZMod 7079299583) ^ 1728344 = (5 : ZMod 7079299583) ^ (864172 + 864172) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 864172 * (5 : ZMod 7079299583) ^ 864172 := by rw [pow_add]
          _ = 1259951683 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 7079299583) ^ 3456689 = 5059605403 := by
        calc
          (5 : ZMod 7079299583) ^ 3456689 = (5 : ZMod 7079299583) ^ (1728344 + 1728344 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1728344 * (5 : ZMod 7079299583) ^ 1728344) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 5059605403 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 7079299583) ^ 6913378 = 1700622881 := by
        calc
          (5 : ZMod 7079299583) ^ 6913378 = (5 : ZMod 7079299583) ^ (3456689 + 3456689) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 3456689 * (5 : ZMod 7079299583) ^ 3456689 := by rw [pow_add]
          _ = 1700622881 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 7079299583) ^ 13826756 = 3197252389 := by
        calc
          (5 : ZMod 7079299583) ^ 13826756 = (5 : ZMod 7079299583) ^ (6913378 + 6913378) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 6913378 * (5 : ZMod 7079299583) ^ 6913378 := by rw [pow_add]
          _ = 3197252389 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 7079299583) ^ 27653513 = 5826078498 := by
        calc
          (5 : ZMod 7079299583) ^ 27653513 = (5 : ZMod 7079299583) ^ (13826756 + 13826756 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 13826756 * (5 : ZMod 7079299583) ^ 13826756) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 5826078498 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 7079299583) ^ 55307027 = 3248866362 := by
        calc
          (5 : ZMod 7079299583) ^ 55307027 = (5 : ZMod 7079299583) ^ (27653513 + 27653513 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 27653513 * (5 : ZMod 7079299583) ^ 27653513) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 3248866362 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 7079299583) ^ 110614055 = 2517027628 := by
        calc
          (5 : ZMod 7079299583) ^ 110614055 = (5 : ZMod 7079299583) ^ (55307027 + 55307027 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 55307027 * (5 : ZMod 7079299583) ^ 55307027) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2517027628 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 7079299583) ^ 221228111 = 6739704017 := by
        calc
          (5 : ZMod 7079299583) ^ 221228111 = (5 : ZMod 7079299583) ^ (110614055 + 110614055 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 110614055 * (5 : ZMod 7079299583) ^ 110614055) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 6739704017 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 7079299583) ^ 442456223 = 6179640487 := by
        calc
          (5 : ZMod 7079299583) ^ 442456223 = (5 : ZMod 7079299583) ^ (221228111 + 221228111 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 221228111 * (5 : ZMod 7079299583) ^ 221228111) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 6179640487 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 7079299583) ^ 884912447 = 2005430557 := by
        calc
          (5 : ZMod 7079299583) ^ 884912447 = (5 : ZMod 7079299583) ^ (442456223 + 442456223 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 442456223 * (5 : ZMod 7079299583) ^ 442456223) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2005430557 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 7079299583) ^ 1769824895 = 2199229961 := by
        calc
          (5 : ZMod 7079299583) ^ 1769824895 = (5 : ZMod 7079299583) ^ (884912447 + 884912447 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 884912447 * (5 : ZMod 7079299583) ^ 884912447) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2199229961 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 7079299583) ^ 3539649791 = 7079299582 := by
        calc
          (5 : ZMod 7079299583) ^ 3539649791 = (5 : ZMod 7079299583) ^ (1769824895 + 1769824895 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1769824895 * (5 : ZMod 7079299583) ^ 1769824895) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 7079299582 := by rw [factor_0_30]; decide
      change (5 : ZMod 7079299583) ^ 3539649791 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (5 : ZMod 7079299583) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 7079299583) ^ 2 = 25 := by
        calc
          (5 : ZMod 7079299583) ^ 2 = (5 : ZMod 7079299583) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 1 * (5 : ZMod 7079299583) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 7079299583) ^ 4 = 625 := by
        calc
          (5 : ZMod 7079299583) ^ 4 = (5 : ZMod 7079299583) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 2 * (5 : ZMod 7079299583) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 7079299583) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 7079299583) ^ 9 = (5 : ZMod 7079299583) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 4 * (5 : ZMod 7079299583) ^ 4) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 7079299583) ^ 18 = 6034089971 := by
        calc
          (5 : ZMod 7079299583) ^ 18 = (5 : ZMod 7079299583) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 9 * (5 : ZMod 7079299583) ^ 9 := by rw [pow_add]
          _ = 6034089971 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 7079299583) ^ 36 = 6505383200 := by
        calc
          (5 : ZMod 7079299583) ^ 36 = (5 : ZMod 7079299583) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 18 * (5 : ZMod 7079299583) ^ 18 := by rw [pow_add]
          _ = 6505383200 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 7079299583) ^ 73 = 1081533368 := by
        calc
          (5 : ZMod 7079299583) ^ 73 = (5 : ZMod 7079299583) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 36 * (5 : ZMod 7079299583) ^ 36) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1081533368 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 7079299583) ^ 146 = 332036840 := by
        calc
          (5 : ZMod 7079299583) ^ 146 = (5 : ZMod 7079299583) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 73 * (5 : ZMod 7079299583) ^ 73 := by rw [pow_add]
          _ = 332036840 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 7079299583) ^ 293 = 2847278179 := by
        calc
          (5 : ZMod 7079299583) ^ 293 = (5 : ZMod 7079299583) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 146 * (5 : ZMod 7079299583) ^ 146) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2847278179 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 7079299583) ^ 587 = 2414534043 := by
        calc
          (5 : ZMod 7079299583) ^ 587 = (5 : ZMod 7079299583) ^ (293 + 293 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 293 * (5 : ZMod 7079299583) ^ 293) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2414534043 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 7079299583) ^ 1174 = 5886723921 := by
        calc
          (5 : ZMod 7079299583) ^ 1174 = (5 : ZMod 7079299583) ^ (587 + 587) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 587 * (5 : ZMod 7079299583) ^ 587 := by rw [pow_add]
          _ = 5886723921 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 7079299583) ^ 2348 = 626557666 := by
        calc
          (5 : ZMod 7079299583) ^ 2348 = (5 : ZMod 7079299583) ^ (1174 + 1174) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 1174 * (5 : ZMod 7079299583) ^ 1174 := by rw [pow_add]
          _ = 626557666 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 7079299583) ^ 4696 = 6691028010 := by
        calc
          (5 : ZMod 7079299583) ^ 4696 = (5 : ZMod 7079299583) ^ (2348 + 2348) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 2348 * (5 : ZMod 7079299583) ^ 2348 := by rw [pow_add]
          _ = 6691028010 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 7079299583) ^ 9393 = 6697778994 := by
        calc
          (5 : ZMod 7079299583) ^ 9393 = (5 : ZMod 7079299583) ^ (4696 + 4696 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 4696 * (5 : ZMod 7079299583) ^ 4696) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 6697778994 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 7079299583) ^ 18786 = 6791771860 := by
        calc
          (5 : ZMod 7079299583) ^ 18786 = (5 : ZMod 7079299583) ^ (9393 + 9393) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 9393 * (5 : ZMod 7079299583) ^ 9393 := by rw [pow_add]
          _ = 6791771860 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 7079299583) ^ 37572 = 3535898235 := by
        calc
          (5 : ZMod 7079299583) ^ 37572 = (5 : ZMod 7079299583) ^ (18786 + 18786) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 18786 * (5 : ZMod 7079299583) ^ 18786 := by rw [pow_add]
          _ = 3535898235 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 7079299583) ^ 75145 = 4412833337 := by
        calc
          (5 : ZMod 7079299583) ^ 75145 = (5 : ZMod 7079299583) ^ (37572 + 37572 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 37572 * (5 : ZMod 7079299583) ^ 37572) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4412833337 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 7079299583) ^ 150290 = 6736601720 := by
        calc
          (5 : ZMod 7079299583) ^ 150290 = (5 : ZMod 7079299583) ^ (75145 + 75145) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 75145 * (5 : ZMod 7079299583) ^ 75145 := by rw [pow_add]
          _ = 6736601720 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 7079299583) ^ 300581 = 416477961 := by
        calc
          (5 : ZMod 7079299583) ^ 300581 = (5 : ZMod 7079299583) ^ (150290 + 150290 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 150290 * (5 : ZMod 7079299583) ^ 150290) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 416477961 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 7079299583) ^ 601163 = 63542707 := by
        calc
          (5 : ZMod 7079299583) ^ 601163 = (5 : ZMod 7079299583) ^ (300581 + 300581 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 300581 * (5 : ZMod 7079299583) ^ 300581) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 63542707 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 7079299583) ^ 1202326 = 4175023382 := by
        calc
          (5 : ZMod 7079299583) ^ 1202326 = (5 : ZMod 7079299583) ^ (601163 + 601163) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 601163 * (5 : ZMod 7079299583) ^ 601163 := by rw [pow_add]
          _ = 4175023382 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 7079299583) ^ 2404653 = 5427806445 := by
        calc
          (5 : ZMod 7079299583) ^ 2404653 = (5 : ZMod 7079299583) ^ (1202326 + 1202326 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1202326 * (5 : ZMod 7079299583) ^ 1202326) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 5427806445 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 7079299583) ^ 4809306 = 3834660221 := by
        calc
          (5 : ZMod 7079299583) ^ 4809306 = (5 : ZMod 7079299583) ^ (2404653 + 2404653) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 2404653 * (5 : ZMod 7079299583) ^ 2404653 := by rw [pow_add]
          _ = 3834660221 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 7079299583) ^ 9618613 = 2303170167 := by
        calc
          (5 : ZMod 7079299583) ^ 9618613 = (5 : ZMod 7079299583) ^ (4809306 + 4809306 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 4809306 * (5 : ZMod 7079299583) ^ 4809306) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2303170167 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 7079299583) ^ 19237227 = 1633928032 := by
        calc
          (5 : ZMod 7079299583) ^ 19237227 = (5 : ZMod 7079299583) ^ (9618613 + 9618613 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 9618613 * (5 : ZMod 7079299583) ^ 9618613) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1633928032 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 7079299583) ^ 38474454 = 5135581030 := by
        calc
          (5 : ZMod 7079299583) ^ 38474454 = (5 : ZMod 7079299583) ^ (19237227 + 19237227) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 19237227 * (5 : ZMod 7079299583) ^ 19237227 := by rw [pow_add]
          _ = 5135581030 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 7079299583) ^ 76948908 = 6382688649 := by
        calc
          (5 : ZMod 7079299583) ^ 76948908 = (5 : ZMod 7079299583) ^ (38474454 + 38474454) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 38474454 * (5 : ZMod 7079299583) ^ 38474454 := by rw [pow_add]
          _ = 6382688649 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 7079299583) ^ 153897817 = 1753658928 := by
        calc
          (5 : ZMod 7079299583) ^ 153897817 = (5 : ZMod 7079299583) ^ (76948908 + 76948908 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 76948908 * (5 : ZMod 7079299583) ^ 76948908) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1753658928 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 7079299583) ^ 307795634 = 6611643819 := by
        calc
          (5 : ZMod 7079299583) ^ 307795634 = (5 : ZMod 7079299583) ^ (153897817 + 153897817) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 153897817 * (5 : ZMod 7079299583) ^ 153897817 := by rw [pow_add]
          _ = 6611643819 := by rw [factor_1_27]; decide
      change (5 : ZMod 7079299583) ^ 307795634 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (5 : ZMod 7079299583) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 7079299583) ^ 2 = 25 := by
        calc
          (5 : ZMod 7079299583) ^ 2 = (5 : ZMod 7079299583) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 1 * (5 : ZMod 7079299583) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 7079299583) ^ 4 = 625 := by
        calc
          (5 : ZMod 7079299583) ^ 4 = (5 : ZMod 7079299583) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 2 * (5 : ZMod 7079299583) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 7079299583) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 7079299583) ^ 9 = (5 : ZMod 7079299583) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 4 * (5 : ZMod 7079299583) ^ 4) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 7079299583) ^ 19 = 1853251523 := by
        calc
          (5 : ZMod 7079299583) ^ 19 = (5 : ZMod 7079299583) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 9 * (5 : ZMod 7079299583) ^ 9) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1853251523 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 7079299583) ^ 39 = 6132747538 := by
        calc
          (5 : ZMod 7079299583) ^ 39 = (5 : ZMod 7079299583) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 19 * (5 : ZMod 7079299583) ^ 19) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 6132747538 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 7079299583) ^ 78 = 2965873909 := by
        calc
          (5 : ZMod 7079299583) ^ 78 = (5 : ZMod 7079299583) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 39 * (5 : ZMod 7079299583) ^ 39 := by rw [pow_add]
          _ = 2965873909 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 7079299583) ^ 157 = 515822137 := by
        calc
          (5 : ZMod 7079299583) ^ 157 = (5 : ZMod 7079299583) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 78 * (5 : ZMod 7079299583) ^ 78) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 515822137 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 7079299583) ^ 314 = 3815214961 := by
        calc
          (5 : ZMod 7079299583) ^ 314 = (5 : ZMod 7079299583) ^ (157 + 157) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 157 * (5 : ZMod 7079299583) ^ 157 := by rw [pow_add]
          _ = 3815214961 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 7079299583) ^ 628 = 799942462 := by
        calc
          (5 : ZMod 7079299583) ^ 628 = (5 : ZMod 7079299583) ^ (314 + 314) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 314 * (5 : ZMod 7079299583) ^ 314 := by rw [pow_add]
          _ = 799942462 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 7079299583) ^ 1256 = 597843584 := by
        calc
          (5 : ZMod 7079299583) ^ 1256 = (5 : ZMod 7079299583) ^ (628 + 628) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 628 * (5 : ZMod 7079299583) ^ 628 := by rw [pow_add]
          _ = 597843584 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 7079299583) ^ 2512 = 6193100094 := by
        calc
          (5 : ZMod 7079299583) ^ 2512 = (5 : ZMod 7079299583) ^ (1256 + 1256) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 1256 * (5 : ZMod 7079299583) ^ 1256 := by rw [pow_add]
          _ = 6193100094 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 7079299583) ^ 5024 = 1799193971 := by
        calc
          (5 : ZMod 7079299583) ^ 5024 = (5 : ZMod 7079299583) ^ (2512 + 2512) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 2512 * (5 : ZMod 7079299583) ^ 2512 := by rw [pow_add]
          _ = 1799193971 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 7079299583) ^ 10048 = 4701953458 := by
        calc
          (5 : ZMod 7079299583) ^ 10048 = (5 : ZMod 7079299583) ^ (5024 + 5024) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 5024 * (5 : ZMod 7079299583) ^ 5024 := by rw [pow_add]
          _ = 4701953458 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 7079299583) ^ 20097 = 2266374339 := by
        calc
          (5 : ZMod 7079299583) ^ 20097 = (5 : ZMod 7079299583) ^ (10048 + 10048 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 10048 * (5 : ZMod 7079299583) ^ 10048) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 2266374339 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 7079299583) ^ 40194 = 3443973401 := by
        calc
          (5 : ZMod 7079299583) ^ 40194 = (5 : ZMod 7079299583) ^ (20097 + 20097) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 20097 * (5 : ZMod 7079299583) ^ 20097 := by rw [pow_add]
          _ = 3443973401 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 7079299583) ^ 80388 = 191540240 := by
        calc
          (5 : ZMod 7079299583) ^ 80388 = (5 : ZMod 7079299583) ^ (40194 + 40194) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 40194 * (5 : ZMod 7079299583) ^ 40194 := by rw [pow_add]
          _ = 191540240 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 7079299583) ^ 160776 = 490512562 := by
        calc
          (5 : ZMod 7079299583) ^ 160776 = (5 : ZMod 7079299583) ^ (80388 + 80388) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 80388 * (5 : ZMod 7079299583) ^ 80388 := by rw [pow_add]
          _ = 490512562 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 7079299583) ^ 321552 = 4315489436 := by
        calc
          (5 : ZMod 7079299583) ^ 321552 = (5 : ZMod 7079299583) ^ (160776 + 160776) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 160776 * (5 : ZMod 7079299583) ^ 160776 := by rw [pow_add]
          _ = 4315489436 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 7079299583) ^ 643104 = 2983407983 := by
        calc
          (5 : ZMod 7079299583) ^ 643104 = (5 : ZMod 7079299583) ^ (321552 + 321552) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 321552 * (5 : ZMod 7079299583) ^ 321552 := by rw [pow_add]
          _ = 2983407983 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 7079299583) ^ 1286209 = 1950028820 := by
        calc
          (5 : ZMod 7079299583) ^ 1286209 = (5 : ZMod 7079299583) ^ (643104 + 643104 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 643104 * (5 : ZMod 7079299583) ^ 643104) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1950028820 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 7079299583) ^ 2572419 = 5281182893 := by
        calc
          (5 : ZMod 7079299583) ^ 2572419 = (5 : ZMod 7079299583) ^ (1286209 + 1286209 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1286209 * (5 : ZMod 7079299583) ^ 1286209) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 5281182893 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 7079299583) ^ 5144839 = 4047044561 := by
        calc
          (5 : ZMod 7079299583) ^ 5144839 = (5 : ZMod 7079299583) ^ (2572419 + 2572419 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 2572419 * (5 : ZMod 7079299583) ^ 2572419) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4047044561 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 7079299583) ^ 10289679 = 4134898488 := by
        calc
          (5 : ZMod 7079299583) ^ 10289679 = (5 : ZMod 7079299583) ^ (5144839 + 5144839 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 5144839 * (5 : ZMod 7079299583) ^ 5144839) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4134898488 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 7079299583) ^ 20579359 = 5850728860 := by
        calc
          (5 : ZMod 7079299583) ^ 20579359 = (5 : ZMod 7079299583) ^ (10289679 + 10289679 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 10289679 * (5 : ZMod 7079299583) ^ 10289679) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 5850728860 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 7079299583) ^ 41158718 = 5527416465 := by
        calc
          (5 : ZMod 7079299583) ^ 41158718 = (5 : ZMod 7079299583) ^ (20579359 + 20579359) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 20579359 * (5 : ZMod 7079299583) ^ 20579359 := by rw [pow_add]
          _ = 5527416465 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 7079299583) ^ 82317437 = 1644457692 := by
        calc
          (5 : ZMod 7079299583) ^ 82317437 = (5 : ZMod 7079299583) ^ (41158718 + 41158718 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 41158718 * (5 : ZMod 7079299583) ^ 41158718) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1644457692 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 7079299583) ^ 164634874 = 6231842363 := by
        calc
          (5 : ZMod 7079299583) ^ 164634874 = (5 : ZMod 7079299583) ^ (82317437 + 82317437) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 82317437 * (5 : ZMod 7079299583) ^ 82317437 := by rw [pow_add]
          _ = 6231842363 := by rw [factor_2_26]; decide
      change (5 : ZMod 7079299583) ^ 164634874 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (5 : ZMod 7079299583) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 7079299583) ^ 2 = 25 := by
        calc
          (5 : ZMod 7079299583) ^ 2 = (5 : ZMod 7079299583) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 1 * (5 : ZMod 7079299583) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 7079299583) ^ 5 = 3125 := by
        calc
          (5 : ZMod 7079299583) ^ 5 = (5 : ZMod 7079299583) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 2 * (5 : ZMod 7079299583) ^ 2) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 7079299583) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 7079299583) ^ 10 = (5 : ZMod 7079299583) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 5 * (5 : ZMod 7079299583) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 7079299583) ^ 20 = 2186958032 := by
        calc
          (5 : ZMod 7079299583) ^ 20 = (5 : ZMod 7079299583) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 10 * (5 : ZMod 7079299583) ^ 10 := by rw [pow_add]
          _ = 2186958032 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 7079299583) ^ 41 = 4653397207 := by
        calc
          (5 : ZMod 7079299583) ^ 41 = (5 : ZMod 7079299583) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 20 * (5 : ZMod 7079299583) ^ 20) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4653397207 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 7079299583) ^ 83 = 1552811478 := by
        calc
          (5 : ZMod 7079299583) ^ 83 = (5 : ZMod 7079299583) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 41 * (5 : ZMod 7079299583) ^ 41) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 1552811478 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 7079299583) ^ 166 = 2908371812 := by
        calc
          (5 : ZMod 7079299583) ^ 166 = (5 : ZMod 7079299583) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 83 * (5 : ZMod 7079299583) ^ 83 := by rw [pow_add]
          _ = 2908371812 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 7079299583) ^ 332 = 6796024002 := by
        calc
          (5 : ZMod 7079299583) ^ 332 = (5 : ZMod 7079299583) ^ (166 + 166) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 166 * (5 : ZMod 7079299583) ^ 166 := by rw [pow_add]
          _ = 6796024002 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 7079299583) ^ 664 = 4695252617 := by
        calc
          (5 : ZMod 7079299583) ^ 664 = (5 : ZMod 7079299583) ^ (332 + 332) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 332 * (5 : ZMod 7079299583) ^ 332 := by rw [pow_add]
          _ = 4695252617 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 7079299583) ^ 1328 = 640682 := by
        calc
          (5 : ZMod 7079299583) ^ 1328 = (5 : ZMod 7079299583) ^ (664 + 664) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 664 * (5 : ZMod 7079299583) ^ 664 := by rw [pow_add]
          _ = 640682 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 7079299583) ^ 2657 = 6449546133 := by
        calc
          (5 : ZMod 7079299583) ^ 2657 = (5 : ZMod 7079299583) ^ (1328 + 1328 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 1328 * (5 : ZMod 7079299583) ^ 1328) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 6449546133 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 7079299583) ^ 5315 = 6220787075 := by
        calc
          (5 : ZMod 7079299583) ^ 5315 = (5 : ZMod 7079299583) ^ (2657 + 2657 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 2657 * (5 : ZMod 7079299583) ^ 2657) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 6220787075 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 7079299583) ^ 10631 = 6539656188 := by
        calc
          (5 : ZMod 7079299583) ^ 10631 = (5 : ZMod 7079299583) ^ (5315 + 5315 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 5315 * (5 : ZMod 7079299583) ^ 5315) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 6539656188 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 7079299583) ^ 21263 = 742262843 := by
        calc
          (5 : ZMod 7079299583) ^ 21263 = (5 : ZMod 7079299583) ^ (10631 + 10631 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 10631 * (5 : ZMod 7079299583) ^ 10631) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 742262843 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 7079299583) ^ 42527 = 4515387543 := by
        calc
          (5 : ZMod 7079299583) ^ 42527 = (5 : ZMod 7079299583) ^ (21263 + 21263 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = ((5 : ZMod 7079299583) ^ 21263 * (5 : ZMod 7079299583) ^ 21263) * (5 : ZMod 7079299583) := by rw [pow_succ, pow_add]
          _ = 4515387543 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 7079299583) ^ 85054 = 5062713779 := by
        calc
          (5 : ZMod 7079299583) ^ 85054 = (5 : ZMod 7079299583) ^ (42527 + 42527) :=
            congrArg (fun n : ℕ => (5 : ZMod 7079299583) ^ n) (by norm_num)
          _ = (5 : ZMod 7079299583) ^ 42527 * (5 : ZMod 7079299583) ^ 42527 := by rw [pow_add]
          _ = 5062713779 := by rw [factor_3_15]; decide
      change (5 : ZMod 7079299583) ^ 85054 ≠ 1
      rw [factor_3_16]
      decide

#print axioms prime_lucas_7079299583

end TotientTailPeriodKiller
end Erdos249257
