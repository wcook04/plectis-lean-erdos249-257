import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1719110381 : Nat.Prime 1719110381 := by
  apply lucas_primality 1719110381 (3 : ZMod 1719110381)
  ·
      have fermat_0 : (3 : ZMod 1719110381) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 1719110381) ^ 3 = 27 := by
        calc
          (3 : ZMod 1719110381) ^ 3 = (3 : ZMod 1719110381) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1 * (3 : ZMod 1719110381) ^ 1) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 1719110381) ^ 6 = 729 := by
        calc
          (3 : ZMod 1719110381) ^ 6 = (3 : ZMod 1719110381) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 3 * (3 : ZMod 1719110381) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 1719110381) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1719110381) ^ 12 = (3 : ZMod 1719110381) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 6 * (3 : ZMod 1719110381) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 1719110381) ^ 25 = 1486301991 := by
        calc
          (3 : ZMod 1719110381) ^ 25 = (3 : ZMod 1719110381) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 12 * (3 : ZMod 1719110381) ^ 12) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1486301991 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 1719110381) ^ 51 = 1598205759 := by
        calc
          (3 : ZMod 1719110381) ^ 51 = (3 : ZMod 1719110381) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 25 * (3 : ZMod 1719110381) ^ 25) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1598205759 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 1719110381) ^ 102 = 263016351 := by
        calc
          (3 : ZMod 1719110381) ^ 102 = (3 : ZMod 1719110381) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 51 * (3 : ZMod 1719110381) ^ 51 := by rw [pow_add]
          _ = 263016351 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 1719110381) ^ 204 = 911502613 := by
        calc
          (3 : ZMod 1719110381) ^ 204 = (3 : ZMod 1719110381) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 102 * (3 : ZMod 1719110381) ^ 102 := by rw [pow_add]
          _ = 911502613 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 1719110381) ^ 409 = 880739772 := by
        calc
          (3 : ZMod 1719110381) ^ 409 = (3 : ZMod 1719110381) ^ (204 + 204 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 204 * (3 : ZMod 1719110381) ^ 204) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 880739772 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 1719110381) ^ 819 = 794459490 := by
        calc
          (3 : ZMod 1719110381) ^ 819 = (3 : ZMod 1719110381) ^ (409 + 409 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 409 * (3 : ZMod 1719110381) ^ 409) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 794459490 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 1719110381) ^ 1639 = 869284090 := by
        calc
          (3 : ZMod 1719110381) ^ 1639 = (3 : ZMod 1719110381) ^ (819 + 819 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 819 * (3 : ZMod 1719110381) ^ 819) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 869284090 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 1719110381) ^ 3278 = 276346407 := by
        calc
          (3 : ZMod 1719110381) ^ 3278 = (3 : ZMod 1719110381) ^ (1639 + 1639) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 1639 * (3 : ZMod 1719110381) ^ 1639 := by rw [pow_add]
          _ = 276346407 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 1719110381) ^ 6557 = 1406598196 := by
        calc
          (3 : ZMod 1719110381) ^ 6557 = (3 : ZMod 1719110381) ^ (3278 + 3278 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 3278 * (3 : ZMod 1719110381) ^ 3278) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1406598196 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 1719110381) ^ 13115 = 1516571813 := by
        calc
          (3 : ZMod 1719110381) ^ 13115 = (3 : ZMod 1719110381) ^ (6557 + 6557 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 6557 * (3 : ZMod 1719110381) ^ 6557) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1516571813 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 1719110381) ^ 26231 = 121680310 := by
        calc
          (3 : ZMod 1719110381) ^ 26231 = (3 : ZMod 1719110381) ^ (13115 + 13115 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 13115 * (3 : ZMod 1719110381) ^ 13115) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 121680310 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 1719110381) ^ 52463 = 298998207 := by
        calc
          (3 : ZMod 1719110381) ^ 52463 = (3 : ZMod 1719110381) ^ (26231 + 26231 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 26231 * (3 : ZMod 1719110381) ^ 26231) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 298998207 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 1719110381) ^ 104926 = 898953630 := by
        calc
          (3 : ZMod 1719110381) ^ 104926 = (3 : ZMod 1719110381) ^ (52463 + 52463) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 52463 * (3 : ZMod 1719110381) ^ 52463 := by rw [pow_add]
          _ = 898953630 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 1719110381) ^ 209852 = 268941235 := by
        calc
          (3 : ZMod 1719110381) ^ 209852 = (3 : ZMod 1719110381) ^ (104926 + 104926) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 104926 * (3 : ZMod 1719110381) ^ 104926 := by rw [pow_add]
          _ = 268941235 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 1719110381) ^ 419704 = 153823714 := by
        calc
          (3 : ZMod 1719110381) ^ 419704 = (3 : ZMod 1719110381) ^ (209852 + 209852) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 209852 * (3 : ZMod 1719110381) ^ 209852 := by rw [pow_add]
          _ = 153823714 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 1719110381) ^ 839409 = 1677436444 := by
        calc
          (3 : ZMod 1719110381) ^ 839409 = (3 : ZMod 1719110381) ^ (419704 + 419704 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 419704 * (3 : ZMod 1719110381) ^ 419704) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1677436444 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 1719110381) ^ 1678818 = 1234668148 := by
        calc
          (3 : ZMod 1719110381) ^ 1678818 = (3 : ZMod 1719110381) ^ (839409 + 839409) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 839409 * (3 : ZMod 1719110381) ^ 839409 := by rw [pow_add]
          _ = 1234668148 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 1719110381) ^ 3357637 = 716224921 := by
        calc
          (3 : ZMod 1719110381) ^ 3357637 = (3 : ZMod 1719110381) ^ (1678818 + 1678818 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1678818 * (3 : ZMod 1719110381) ^ 1678818) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 716224921 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 1719110381) ^ 6715274 = 693631601 := by
        calc
          (3 : ZMod 1719110381) ^ 6715274 = (3 : ZMod 1719110381) ^ (3357637 + 3357637) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 3357637 * (3 : ZMod 1719110381) ^ 3357637 := by rw [pow_add]
          _ = 693631601 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 1719110381) ^ 13430549 = 251604583 := by
        calc
          (3 : ZMod 1719110381) ^ 13430549 = (3 : ZMod 1719110381) ^ (6715274 + 6715274 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 6715274 * (3 : ZMod 1719110381) ^ 6715274) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 251604583 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 1719110381) ^ 26861099 = 1645530305 := by
        calc
          (3 : ZMod 1719110381) ^ 26861099 = (3 : ZMod 1719110381) ^ (13430549 + 13430549 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 13430549 * (3 : ZMod 1719110381) ^ 13430549) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1645530305 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 1719110381) ^ 53722199 = 75445330 := by
        calc
          (3 : ZMod 1719110381) ^ 53722199 = (3 : ZMod 1719110381) ^ (26861099 + 26861099 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 26861099 * (3 : ZMod 1719110381) ^ 26861099) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 75445330 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 1719110381) ^ 107444398 = 998882947 := by
        calc
          (3 : ZMod 1719110381) ^ 107444398 = (3 : ZMod 1719110381) ^ (53722199 + 53722199) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 53722199 * (3 : ZMod 1719110381) ^ 53722199 := by rw [pow_add]
          _ = 998882947 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 1719110381) ^ 214888797 = 682362041 := by
        calc
          (3 : ZMod 1719110381) ^ 214888797 = (3 : ZMod 1719110381) ^ (107444398 + 107444398 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 107444398 * (3 : ZMod 1719110381) ^ 107444398) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 682362041 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 1719110381) ^ 429777595 = 1231122919 := by
        calc
          (3 : ZMod 1719110381) ^ 429777595 = (3 : ZMod 1719110381) ^ (214888797 + 214888797 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 214888797 * (3 : ZMod 1719110381) ^ 214888797) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1231122919 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 1719110381) ^ 859555190 = 1719110380 := by
        calc
          (3 : ZMod 1719110381) ^ 859555190 = (3 : ZMod 1719110381) ^ (429777595 + 429777595) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 429777595 * (3 : ZMod 1719110381) ^ 429777595 := by rw [pow_add]
          _ = 1719110380 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 1719110381) ^ 1719110380 = 1 := by
        calc
          (3 : ZMod 1719110381) ^ 1719110380 = (3 : ZMod 1719110381) ^ (859555190 + 859555190) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 859555190 * (3 : ZMod 1719110381) ^ 859555190 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (17, 1), (131, 1), (2969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (17, 1), (131, 1), (2969, 1)] : List FactorBlock).map factorBlockValue).prod = 1719110381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 1719110381) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 1719110381) ^ 3 = 27 := by
        calc
          (3 : ZMod 1719110381) ^ 3 = (3 : ZMod 1719110381) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1 * (3 : ZMod 1719110381) ^ 1) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 1719110381) ^ 6 = 729 := by
        calc
          (3 : ZMod 1719110381) ^ 6 = (3 : ZMod 1719110381) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 3 * (3 : ZMod 1719110381) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 1719110381) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1719110381) ^ 12 = (3 : ZMod 1719110381) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 6 * (3 : ZMod 1719110381) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 1719110381) ^ 25 = 1486301991 := by
        calc
          (3 : ZMod 1719110381) ^ 25 = (3 : ZMod 1719110381) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 12 * (3 : ZMod 1719110381) ^ 12) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1486301991 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 1719110381) ^ 51 = 1598205759 := by
        calc
          (3 : ZMod 1719110381) ^ 51 = (3 : ZMod 1719110381) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 25 * (3 : ZMod 1719110381) ^ 25) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1598205759 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 1719110381) ^ 102 = 263016351 := by
        calc
          (3 : ZMod 1719110381) ^ 102 = (3 : ZMod 1719110381) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 51 * (3 : ZMod 1719110381) ^ 51 := by rw [pow_add]
          _ = 263016351 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 1719110381) ^ 204 = 911502613 := by
        calc
          (3 : ZMod 1719110381) ^ 204 = (3 : ZMod 1719110381) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 102 * (3 : ZMod 1719110381) ^ 102 := by rw [pow_add]
          _ = 911502613 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 1719110381) ^ 409 = 880739772 := by
        calc
          (3 : ZMod 1719110381) ^ 409 = (3 : ZMod 1719110381) ^ (204 + 204 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 204 * (3 : ZMod 1719110381) ^ 204) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 880739772 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 1719110381) ^ 819 = 794459490 := by
        calc
          (3 : ZMod 1719110381) ^ 819 = (3 : ZMod 1719110381) ^ (409 + 409 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 409 * (3 : ZMod 1719110381) ^ 409) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 794459490 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 1719110381) ^ 1639 = 869284090 := by
        calc
          (3 : ZMod 1719110381) ^ 1639 = (3 : ZMod 1719110381) ^ (819 + 819 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 819 * (3 : ZMod 1719110381) ^ 819) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 869284090 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 1719110381) ^ 3278 = 276346407 := by
        calc
          (3 : ZMod 1719110381) ^ 3278 = (3 : ZMod 1719110381) ^ (1639 + 1639) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 1639 * (3 : ZMod 1719110381) ^ 1639 := by rw [pow_add]
          _ = 276346407 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 1719110381) ^ 6557 = 1406598196 := by
        calc
          (3 : ZMod 1719110381) ^ 6557 = (3 : ZMod 1719110381) ^ (3278 + 3278 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 3278 * (3 : ZMod 1719110381) ^ 3278) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1406598196 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 1719110381) ^ 13115 = 1516571813 := by
        calc
          (3 : ZMod 1719110381) ^ 13115 = (3 : ZMod 1719110381) ^ (6557 + 6557 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 6557 * (3 : ZMod 1719110381) ^ 6557) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1516571813 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 1719110381) ^ 26231 = 121680310 := by
        calc
          (3 : ZMod 1719110381) ^ 26231 = (3 : ZMod 1719110381) ^ (13115 + 13115 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 13115 * (3 : ZMod 1719110381) ^ 13115) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 121680310 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 1719110381) ^ 52463 = 298998207 := by
        calc
          (3 : ZMod 1719110381) ^ 52463 = (3 : ZMod 1719110381) ^ (26231 + 26231 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 26231 * (3 : ZMod 1719110381) ^ 26231) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 298998207 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 1719110381) ^ 104926 = 898953630 := by
        calc
          (3 : ZMod 1719110381) ^ 104926 = (3 : ZMod 1719110381) ^ (52463 + 52463) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 52463 * (3 : ZMod 1719110381) ^ 52463 := by rw [pow_add]
          _ = 898953630 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 1719110381) ^ 209852 = 268941235 := by
        calc
          (3 : ZMod 1719110381) ^ 209852 = (3 : ZMod 1719110381) ^ (104926 + 104926) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 104926 * (3 : ZMod 1719110381) ^ 104926 := by rw [pow_add]
          _ = 268941235 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 1719110381) ^ 419704 = 153823714 := by
        calc
          (3 : ZMod 1719110381) ^ 419704 = (3 : ZMod 1719110381) ^ (209852 + 209852) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 209852 * (3 : ZMod 1719110381) ^ 209852 := by rw [pow_add]
          _ = 153823714 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 1719110381) ^ 839409 = 1677436444 := by
        calc
          (3 : ZMod 1719110381) ^ 839409 = (3 : ZMod 1719110381) ^ (419704 + 419704 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 419704 * (3 : ZMod 1719110381) ^ 419704) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1677436444 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 1719110381) ^ 1678818 = 1234668148 := by
        calc
          (3 : ZMod 1719110381) ^ 1678818 = (3 : ZMod 1719110381) ^ (839409 + 839409) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 839409 * (3 : ZMod 1719110381) ^ 839409 := by rw [pow_add]
          _ = 1234668148 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 1719110381) ^ 3357637 = 716224921 := by
        calc
          (3 : ZMod 1719110381) ^ 3357637 = (3 : ZMod 1719110381) ^ (1678818 + 1678818 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1678818 * (3 : ZMod 1719110381) ^ 1678818) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 716224921 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 1719110381) ^ 6715274 = 693631601 := by
        calc
          (3 : ZMod 1719110381) ^ 6715274 = (3 : ZMod 1719110381) ^ (3357637 + 3357637) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 3357637 * (3 : ZMod 1719110381) ^ 3357637 := by rw [pow_add]
          _ = 693631601 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 1719110381) ^ 13430549 = 251604583 := by
        calc
          (3 : ZMod 1719110381) ^ 13430549 = (3 : ZMod 1719110381) ^ (6715274 + 6715274 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 6715274 * (3 : ZMod 1719110381) ^ 6715274) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 251604583 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 1719110381) ^ 26861099 = 1645530305 := by
        calc
          (3 : ZMod 1719110381) ^ 26861099 = (3 : ZMod 1719110381) ^ (13430549 + 13430549 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 13430549 * (3 : ZMod 1719110381) ^ 13430549) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1645530305 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 1719110381) ^ 53722199 = 75445330 := by
        calc
          (3 : ZMod 1719110381) ^ 53722199 = (3 : ZMod 1719110381) ^ (26861099 + 26861099 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 26861099 * (3 : ZMod 1719110381) ^ 26861099) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 75445330 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 1719110381) ^ 107444398 = 998882947 := by
        calc
          (3 : ZMod 1719110381) ^ 107444398 = (3 : ZMod 1719110381) ^ (53722199 + 53722199) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 53722199 * (3 : ZMod 1719110381) ^ 53722199 := by rw [pow_add]
          _ = 998882947 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 1719110381) ^ 214888797 = 682362041 := by
        calc
          (3 : ZMod 1719110381) ^ 214888797 = (3 : ZMod 1719110381) ^ (107444398 + 107444398 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 107444398 * (3 : ZMod 1719110381) ^ 107444398) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 682362041 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 1719110381) ^ 429777595 = 1231122919 := by
        calc
          (3 : ZMod 1719110381) ^ 429777595 = (3 : ZMod 1719110381) ^ (214888797 + 214888797 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 214888797 * (3 : ZMod 1719110381) ^ 214888797) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1231122919 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 1719110381) ^ 859555190 = 1719110380 := by
        calc
          (3 : ZMod 1719110381) ^ 859555190 = (3 : ZMod 1719110381) ^ (429777595 + 429777595) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 429777595 * (3 : ZMod 1719110381) ^ 429777595 := by rw [pow_add]
          _ = 1719110380 := by rw [factor_0_28]; decide
      change (3 : ZMod 1719110381) ^ 859555190 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (3 : ZMod 1719110381) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 1719110381) ^ 2 = 9 := by
        calc
          (3 : ZMod 1719110381) ^ 2 = (3 : ZMod 1719110381) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 1 * (3 : ZMod 1719110381) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 1719110381) ^ 5 = 243 := by
        calc
          (3 : ZMod 1719110381) ^ 5 = (3 : ZMod 1719110381) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 2 * (3 : ZMod 1719110381) ^ 2) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 1719110381) ^ 10 = 59049 := by
        calc
          (3 : ZMod 1719110381) ^ 10 = (3 : ZMod 1719110381) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 5 * (3 : ZMod 1719110381) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 1719110381) ^ 20 = 48563639 := by
        calc
          (3 : ZMod 1719110381) ^ 20 = (3 : ZMod 1719110381) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 10 * (3 : ZMod 1719110381) ^ 10 := by rw [pow_add]
          _ = 48563639 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 1719110381) ^ 40 = 130552993 := by
        calc
          (3 : ZMod 1719110381) ^ 40 = (3 : ZMod 1719110381) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 20 * (3 : ZMod 1719110381) ^ 20 := by rw [pow_add]
          _ = 130552993 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 1719110381) ^ 81 = 630454650 := by
        calc
          (3 : ZMod 1719110381) ^ 81 = (3 : ZMod 1719110381) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 40 * (3 : ZMod 1719110381) ^ 40) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 630454650 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 1719110381) ^ 163 = 709943608 := by
        calc
          (3 : ZMod 1719110381) ^ 163 = (3 : ZMod 1719110381) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 81 * (3 : ZMod 1719110381) ^ 81) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 709943608 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 1719110381) ^ 327 = 137632923 := by
        calc
          (3 : ZMod 1719110381) ^ 327 = (3 : ZMod 1719110381) ^ (163 + 163 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 163 * (3 : ZMod 1719110381) ^ 163) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 137632923 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 1719110381) ^ 655 = 1088672125 := by
        calc
          (3 : ZMod 1719110381) ^ 655 = (3 : ZMod 1719110381) ^ (327 + 327 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 327 * (3 : ZMod 1719110381) ^ 327) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1088672125 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 1719110381) ^ 1311 = 943814529 := by
        calc
          (3 : ZMod 1719110381) ^ 1311 = (3 : ZMod 1719110381) ^ (655 + 655 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 655 * (3 : ZMod 1719110381) ^ 655) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 943814529 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 1719110381) ^ 2623 = 1052413128 := by
        calc
          (3 : ZMod 1719110381) ^ 2623 = (3 : ZMod 1719110381) ^ (1311 + 1311 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1311 * (3 : ZMod 1719110381) ^ 1311) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1052413128 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 1719110381) ^ 5246 = 1370118896 := by
        calc
          (3 : ZMod 1719110381) ^ 5246 = (3 : ZMod 1719110381) ^ (2623 + 2623) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 2623 * (3 : ZMod 1719110381) ^ 2623 := by rw [pow_add]
          _ = 1370118896 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 1719110381) ^ 10492 = 522992762 := by
        calc
          (3 : ZMod 1719110381) ^ 10492 = (3 : ZMod 1719110381) ^ (5246 + 5246) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 5246 * (3 : ZMod 1719110381) ^ 5246 := by rw [pow_add]
          _ = 522992762 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 1719110381) ^ 20985 = 408283973 := by
        calc
          (3 : ZMod 1719110381) ^ 20985 = (3 : ZMod 1719110381) ^ (10492 + 10492 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 10492 * (3 : ZMod 1719110381) ^ 10492) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 408283973 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 1719110381) ^ 41970 = 446627952 := by
        calc
          (3 : ZMod 1719110381) ^ 41970 = (3 : ZMod 1719110381) ^ (20985 + 20985) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 20985 * (3 : ZMod 1719110381) ^ 20985 := by rw [pow_add]
          _ = 446627952 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 1719110381) ^ 83940 = 1417078364 := by
        calc
          (3 : ZMod 1719110381) ^ 83940 = (3 : ZMod 1719110381) ^ (41970 + 41970) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 41970 * (3 : ZMod 1719110381) ^ 41970 := by rw [pow_add]
          _ = 1417078364 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 1719110381) ^ 167881 = 470373114 := by
        calc
          (3 : ZMod 1719110381) ^ 167881 = (3 : ZMod 1719110381) ^ (83940 + 83940 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 83940 * (3 : ZMod 1719110381) ^ 83940) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 470373114 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 1719110381) ^ 335763 = 1569136875 := by
        calc
          (3 : ZMod 1719110381) ^ 335763 = (3 : ZMod 1719110381) ^ (167881 + 167881 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 167881 * (3 : ZMod 1719110381) ^ 167881) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1569136875 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 1719110381) ^ 671527 = 607557983 := by
        calc
          (3 : ZMod 1719110381) ^ 671527 = (3 : ZMod 1719110381) ^ (335763 + 335763 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 335763 * (3 : ZMod 1719110381) ^ 335763) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 607557983 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 1719110381) ^ 1343054 = 747308784 := by
        calc
          (3 : ZMod 1719110381) ^ 1343054 = (3 : ZMod 1719110381) ^ (671527 + 671527) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 671527 * (3 : ZMod 1719110381) ^ 671527 := by rw [pow_add]
          _ = 747308784 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 1719110381) ^ 2686109 = 677309664 := by
        calc
          (3 : ZMod 1719110381) ^ 2686109 = (3 : ZMod 1719110381) ^ (1343054 + 1343054 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1343054 * (3 : ZMod 1719110381) ^ 1343054) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 677309664 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 1719110381) ^ 5372219 = 115528279 := by
        calc
          (3 : ZMod 1719110381) ^ 5372219 = (3 : ZMod 1719110381) ^ (2686109 + 2686109 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 2686109 * (3 : ZMod 1719110381) ^ 2686109) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 115528279 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 1719110381) ^ 10744439 = 1466022984 := by
        calc
          (3 : ZMod 1719110381) ^ 10744439 = (3 : ZMod 1719110381) ^ (5372219 + 5372219 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 5372219 * (3 : ZMod 1719110381) ^ 5372219) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1466022984 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 1719110381) ^ 21488879 = 95923562 := by
        calc
          (3 : ZMod 1719110381) ^ 21488879 = (3 : ZMod 1719110381) ^ (10744439 + 10744439 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 10744439 * (3 : ZMod 1719110381) ^ 10744439) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 95923562 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 1719110381) ^ 42977759 = 53574716 := by
        calc
          (3 : ZMod 1719110381) ^ 42977759 = (3 : ZMod 1719110381) ^ (21488879 + 21488879 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 21488879 * (3 : ZMod 1719110381) ^ 21488879) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 53574716 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 1719110381) ^ 85955519 = 23563547 := by
        calc
          (3 : ZMod 1719110381) ^ 85955519 = (3 : ZMod 1719110381) ^ (42977759 + 42977759 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 42977759 * (3 : ZMod 1719110381) ^ 42977759) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 23563547 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 1719110381) ^ 171911038 = 757255448 := by
        calc
          (3 : ZMod 1719110381) ^ 171911038 = (3 : ZMod 1719110381) ^ (85955519 + 85955519) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 85955519 * (3 : ZMod 1719110381) ^ 85955519 := by rw [pow_add]
          _ = 757255448 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 1719110381) ^ 343822076 = 1159737683 := by
        calc
          (3 : ZMod 1719110381) ^ 343822076 = (3 : ZMod 1719110381) ^ (171911038 + 171911038) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 171911038 * (3 : ZMod 1719110381) ^ 171911038 := by rw [pow_add]
          _ = 1159737683 := by rw [factor_1_27]; decide
      change (3 : ZMod 1719110381) ^ 343822076 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (3 : ZMod 1719110381) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 1719110381) ^ 3 = 27 := by
        calc
          (3 : ZMod 1719110381) ^ 3 = (3 : ZMod 1719110381) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1 * (3 : ZMod 1719110381) ^ 1) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 1719110381) ^ 7 = 2187 := by
        calc
          (3 : ZMod 1719110381) ^ 7 = (3 : ZMod 1719110381) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 3 * (3 : ZMod 1719110381) ^ 3) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 1719110381) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 1719110381) ^ 15 = (3 : ZMod 1719110381) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 7 * (3 : ZMod 1719110381) ^ 7) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 1719110381) ^ 31 = 474611409 := by
        calc
          (3 : ZMod 1719110381) ^ 31 = (3 : ZMod 1719110381) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 15 * (3 : ZMod 1719110381) ^ 15) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 474611409 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 1719110381) ^ 63 = 1515490335 := by
        calc
          (3 : ZMod 1719110381) ^ 63 = (3 : ZMod 1719110381) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 31 * (3 : ZMod 1719110381) ^ 31) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1515490335 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 1719110381) ^ 126 = 606588698 := by
        calc
          (3 : ZMod 1719110381) ^ 126 = (3 : ZMod 1719110381) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 63 * (3 : ZMod 1719110381) ^ 63 := by rw [pow_add]
          _ = 606588698 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 1719110381) ^ 252 = 1413357631 := by
        calc
          (3 : ZMod 1719110381) ^ 252 = (3 : ZMod 1719110381) ^ (126 + 126) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 126 * (3 : ZMod 1719110381) ^ 126 := by rw [pow_add]
          _ = 1413357631 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 1719110381) ^ 504 = 1245578799 := by
        calc
          (3 : ZMod 1719110381) ^ 504 = (3 : ZMod 1719110381) ^ (252 + 252) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 252 * (3 : ZMod 1719110381) ^ 252 := by rw [pow_add]
          _ = 1245578799 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 1719110381) ^ 1008 = 43908486 := by
        calc
          (3 : ZMod 1719110381) ^ 1008 = (3 : ZMod 1719110381) ^ (504 + 504) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 504 * (3 : ZMod 1719110381) ^ 504 := by rw [pow_add]
          _ = 43908486 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 1719110381) ^ 2017 = 1068860376 := by
        calc
          (3 : ZMod 1719110381) ^ 2017 = (3 : ZMod 1719110381) ^ (1008 + 1008 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1008 * (3 : ZMod 1719110381) ^ 1008) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1068860376 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 1719110381) ^ 4035 = 710337350 := by
        calc
          (3 : ZMod 1719110381) ^ 4035 = (3 : ZMod 1719110381) ^ (2017 + 2017 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 2017 * (3 : ZMod 1719110381) ^ 2017) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 710337350 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 1719110381) ^ 8071 = 1707261436 := by
        calc
          (3 : ZMod 1719110381) ^ 8071 = (3 : ZMod 1719110381) ^ (4035 + 4035 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 4035 * (3 : ZMod 1719110381) ^ 4035) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1707261436 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 1719110381) ^ 16142 = 1191017517 := by
        calc
          (3 : ZMod 1719110381) ^ 16142 = (3 : ZMod 1719110381) ^ (8071 + 8071) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 8071 * (3 : ZMod 1719110381) ^ 8071 := by rw [pow_add]
          _ = 1191017517 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 1719110381) ^ 32284 = 15072370 := by
        calc
          (3 : ZMod 1719110381) ^ 32284 = (3 : ZMod 1719110381) ^ (16142 + 16142) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 16142 * (3 : ZMod 1719110381) ^ 16142 := by rw [pow_add]
          _ = 15072370 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 1719110381) ^ 64569 = 1454586298 := by
        calc
          (3 : ZMod 1719110381) ^ 64569 = (3 : ZMod 1719110381) ^ (32284 + 32284 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 32284 * (3 : ZMod 1719110381) ^ 32284) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1454586298 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 1719110381) ^ 129139 = 1609716997 := by
        calc
          (3 : ZMod 1719110381) ^ 129139 = (3 : ZMod 1719110381) ^ (64569 + 64569 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 64569 * (3 : ZMod 1719110381) ^ 64569) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1609716997 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 1719110381) ^ 258279 = 29838305 := by
        calc
          (3 : ZMod 1719110381) ^ 258279 = (3 : ZMod 1719110381) ^ (129139 + 129139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 129139 * (3 : ZMod 1719110381) ^ 129139) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 29838305 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 1719110381) ^ 516559 = 132411280 := by
        calc
          (3 : ZMod 1719110381) ^ 516559 = (3 : ZMod 1719110381) ^ (258279 + 258279 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 258279 * (3 : ZMod 1719110381) ^ 258279) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 132411280 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 1719110381) ^ 1033119 = 1331894143 := by
        calc
          (3 : ZMod 1719110381) ^ 1033119 = (3 : ZMod 1719110381) ^ (516559 + 516559 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 516559 * (3 : ZMod 1719110381) ^ 516559) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1331894143 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 1719110381) ^ 2066238 = 1586186480 := by
        calc
          (3 : ZMod 1719110381) ^ 2066238 = (3 : ZMod 1719110381) ^ (1033119 + 1033119) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 1033119 * (3 : ZMod 1719110381) ^ 1033119 := by rw [pow_add]
          _ = 1586186480 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 1719110381) ^ 4132476 = 1389476189 := by
        calc
          (3 : ZMod 1719110381) ^ 4132476 = (3 : ZMod 1719110381) ^ (2066238 + 2066238) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 2066238 * (3 : ZMod 1719110381) ^ 2066238 := by rw [pow_add]
          _ = 1389476189 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 1719110381) ^ 8264953 = 248575208 := by
        calc
          (3 : ZMod 1719110381) ^ 8264953 = (3 : ZMod 1719110381) ^ (4132476 + 4132476 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 4132476 * (3 : ZMod 1719110381) ^ 4132476) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 248575208 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 1719110381) ^ 16529907 = 919433964 := by
        calc
          (3 : ZMod 1719110381) ^ 16529907 = (3 : ZMod 1719110381) ^ (8264953 + 8264953 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 8264953 * (3 : ZMod 1719110381) ^ 8264953) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 919433964 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 1719110381) ^ 33059815 = 1526089504 := by
        calc
          (3 : ZMod 1719110381) ^ 33059815 = (3 : ZMod 1719110381) ^ (16529907 + 16529907 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 16529907 * (3 : ZMod 1719110381) ^ 16529907) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1526089504 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 1719110381) ^ 66119630 = 238806639 := by
        calc
          (3 : ZMod 1719110381) ^ 66119630 = (3 : ZMod 1719110381) ^ (33059815 + 33059815) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 33059815 * (3 : ZMod 1719110381) ^ 33059815 := by rw [pow_add]
          _ = 238806639 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 1719110381) ^ 132239260 = 12468734 := by
        calc
          (3 : ZMod 1719110381) ^ 132239260 = (3 : ZMod 1719110381) ^ (66119630 + 66119630) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 66119630 * (3 : ZMod 1719110381) ^ 66119630 := by rw [pow_add]
          _ = 12468734 := by rw [factor_2_25]; decide
      change (3 : ZMod 1719110381) ^ 132239260 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (3 : ZMod 1719110381) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 1719110381) ^ 3 = 27 := by
        calc
          (3 : ZMod 1719110381) ^ 3 = (3 : ZMod 1719110381) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1 * (3 : ZMod 1719110381) ^ 1) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 1719110381) ^ 6 = 729 := by
        calc
          (3 : ZMod 1719110381) ^ 6 = (3 : ZMod 1719110381) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 3 * (3 : ZMod 1719110381) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 1719110381) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1719110381) ^ 12 = (3 : ZMod 1719110381) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 6 * (3 : ZMod 1719110381) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 1719110381) ^ 24 = 495433997 := by
        calc
          (3 : ZMod 1719110381) ^ 24 = (3 : ZMod 1719110381) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 12 * (3 : ZMod 1719110381) ^ 12 := by rw [pow_add]
          _ = 495433997 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 1719110381) ^ 48 = 441217335 := by
        calc
          (3 : ZMod 1719110381) ^ 48 = (3 : ZMod 1719110381) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 24 * (3 : ZMod 1719110381) ^ 24 := by rw [pow_add]
          _ = 441217335 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 1719110381) ^ 96 = 1549682492 := by
        calc
          (3 : ZMod 1719110381) ^ 96 = (3 : ZMod 1719110381) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 48 * (3 : ZMod 1719110381) ^ 48 := by rw [pow_add]
          _ = 1549682492 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 1719110381) ^ 192 = 1282435461 := by
        calc
          (3 : ZMod 1719110381) ^ 192 = (3 : ZMod 1719110381) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 96 * (3 : ZMod 1719110381) ^ 96 := by rw [pow_add]
          _ = 1282435461 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 1719110381) ^ 385 = 1408400238 := by
        calc
          (3 : ZMod 1719110381) ^ 385 = (3 : ZMod 1719110381) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 192 * (3 : ZMod 1719110381) ^ 192) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1408400238 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 1719110381) ^ 771 = 475807526 := by
        calc
          (3 : ZMod 1719110381) ^ 771 = (3 : ZMod 1719110381) ^ (385 + 385 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 385 * (3 : ZMod 1719110381) ^ 385) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 475807526 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 1719110381) ^ 1543 = 32183861 := by
        calc
          (3 : ZMod 1719110381) ^ 1543 = (3 : ZMod 1719110381) ^ (771 + 771 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 771 * (3 : ZMod 1719110381) ^ 771) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 32183861 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 1719110381) ^ 3086 = 802996820 := by
        calc
          (3 : ZMod 1719110381) ^ 3086 = (3 : ZMod 1719110381) ^ (1543 + 1543) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 1543 * (3 : ZMod 1719110381) ^ 1543 := by rw [pow_add]
          _ = 802996820 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 1719110381) ^ 6172 = 449508877 := by
        calc
          (3 : ZMod 1719110381) ^ 6172 = (3 : ZMod 1719110381) ^ (3086 + 3086) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 3086 * (3 : ZMod 1719110381) ^ 3086 := by rw [pow_add]
          _ = 449508877 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 1719110381) ^ 12344 = 1171621962 := by
        calc
          (3 : ZMod 1719110381) ^ 12344 = (3 : ZMod 1719110381) ^ (6172 + 6172) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 6172 * (3 : ZMod 1719110381) ^ 6172 := by rw [pow_add]
          _ = 1171621962 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 1719110381) ^ 24688 = 360184242 := by
        calc
          (3 : ZMod 1719110381) ^ 24688 = (3 : ZMod 1719110381) ^ (12344 + 12344) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 12344 * (3 : ZMod 1719110381) ^ 12344 := by rw [pow_add]
          _ = 360184242 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 1719110381) ^ 49377 = 1084433452 := by
        calc
          (3 : ZMod 1719110381) ^ 49377 = (3 : ZMod 1719110381) ^ (24688 + 24688 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 24688 * (3 : ZMod 1719110381) ^ 24688) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1084433452 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 1719110381) ^ 98754 = 913473715 := by
        calc
          (3 : ZMod 1719110381) ^ 98754 = (3 : ZMod 1719110381) ^ (49377 + 49377) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 49377 * (3 : ZMod 1719110381) ^ 49377 := by rw [pow_add]
          _ = 913473715 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 1719110381) ^ 197508 = 378956214 := by
        calc
          (3 : ZMod 1719110381) ^ 197508 = (3 : ZMod 1719110381) ^ (98754 + 98754) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 98754 * (3 : ZMod 1719110381) ^ 98754 := by rw [pow_add]
          _ = 378956214 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 1719110381) ^ 395016 = 1048752076 := by
        calc
          (3 : ZMod 1719110381) ^ 395016 = (3 : ZMod 1719110381) ^ (197508 + 197508) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 197508 * (3 : ZMod 1719110381) ^ 197508 := by rw [pow_add]
          _ = 1048752076 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 1719110381) ^ 790032 = 294668511 := by
        calc
          (3 : ZMod 1719110381) ^ 790032 = (3 : ZMod 1719110381) ^ (395016 + 395016) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 395016 * (3 : ZMod 1719110381) ^ 395016 := by rw [pow_add]
          _ = 294668511 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 1719110381) ^ 1580064 = 1135263292 := by
        calc
          (3 : ZMod 1719110381) ^ 1580064 = (3 : ZMod 1719110381) ^ (790032 + 790032) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 790032 * (3 : ZMod 1719110381) ^ 790032 := by rw [pow_add]
          _ = 1135263292 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 1719110381) ^ 3160129 = 1253069224 := by
        calc
          (3 : ZMod 1719110381) ^ 3160129 = (3 : ZMod 1719110381) ^ (1580064 + 1580064 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1580064 * (3 : ZMod 1719110381) ^ 1580064) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1253069224 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 1719110381) ^ 6320258 = 1572965833 := by
        calc
          (3 : ZMod 1719110381) ^ 6320258 = (3 : ZMod 1719110381) ^ (3160129 + 3160129) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 3160129 * (3 : ZMod 1719110381) ^ 3160129 := by rw [pow_add]
          _ = 1572965833 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 1719110381) ^ 12640517 = 1171520150 := by
        calc
          (3 : ZMod 1719110381) ^ 12640517 = (3 : ZMod 1719110381) ^ (6320258 + 6320258 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 6320258 * (3 : ZMod 1719110381) ^ 6320258) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1171520150 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 1719110381) ^ 25281035 = 530925242 := by
        calc
          (3 : ZMod 1719110381) ^ 25281035 = (3 : ZMod 1719110381) ^ (12640517 + 12640517 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 12640517 * (3 : ZMod 1719110381) ^ 12640517) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 530925242 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 1719110381) ^ 50562070 = 1425132018 := by
        calc
          (3 : ZMod 1719110381) ^ 50562070 = (3 : ZMod 1719110381) ^ (25281035 + 25281035) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 25281035 * (3 : ZMod 1719110381) ^ 25281035 := by rw [pow_add]
          _ = 1425132018 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 1719110381) ^ 101124140 = 961262336 := by
        calc
          (3 : ZMod 1719110381) ^ 101124140 = (3 : ZMod 1719110381) ^ (50562070 + 50562070) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 50562070 * (3 : ZMod 1719110381) ^ 50562070 := by rw [pow_add]
          _ = 961262336 := by rw [factor_3_25]; decide
      change (3 : ZMod 1719110381) ^ 101124140 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (3 : ZMod 1719110381) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 1719110381) ^ 3 = 27 := by
        calc
          (3 : ZMod 1719110381) ^ 3 = (3 : ZMod 1719110381) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1 * (3 : ZMod 1719110381) ^ 1) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 1719110381) ^ 6 = 729 := by
        calc
          (3 : ZMod 1719110381) ^ 6 = (3 : ZMod 1719110381) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 3 * (3 : ZMod 1719110381) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 1719110381) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1719110381) ^ 12 = (3 : ZMod 1719110381) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 6 * (3 : ZMod 1719110381) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 1719110381) ^ 25 = 1486301991 := by
        calc
          (3 : ZMod 1719110381) ^ 25 = (3 : ZMod 1719110381) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 12 * (3 : ZMod 1719110381) ^ 12) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1486301991 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 1719110381) ^ 50 = 532735253 := by
        calc
          (3 : ZMod 1719110381) ^ 50 = (3 : ZMod 1719110381) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 25 * (3 : ZMod 1719110381) ^ 25 := by rw [pow_add]
          _ = 532735253 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 1719110381) ^ 100 = 29224039 := by
        calc
          (3 : ZMod 1719110381) ^ 100 = (3 : ZMod 1719110381) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 50 * (3 : ZMod 1719110381) ^ 50 := by rw [pow_add]
          _ = 29224039 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 1719110381) ^ 200 = 732855007 := by
        calc
          (3 : ZMod 1719110381) ^ 200 = (3 : ZMod 1719110381) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 100 * (3 : ZMod 1719110381) ^ 100 := by rw [pow_add]
          _ = 732855007 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 1719110381) ^ 400 = 230883985 := by
        calc
          (3 : ZMod 1719110381) ^ 400 = (3 : ZMod 1719110381) ^ (200 + 200) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 200 * (3 : ZMod 1719110381) ^ 200 := by rw [pow_add]
          _ = 230883985 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 1719110381) ^ 800 = 356847524 := by
        calc
          (3 : ZMod 1719110381) ^ 800 = (3 : ZMod 1719110381) ^ (400 + 400) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 400 * (3 : ZMod 1719110381) ^ 400 := by rw [pow_add]
          _ = 356847524 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 1719110381) ^ 1601 = 1402645830 := by
        calc
          (3 : ZMod 1719110381) ^ 1601 = (3 : ZMod 1719110381) ^ (800 + 800 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 800 * (3 : ZMod 1719110381) ^ 800) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1402645830 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 1719110381) ^ 3203 = 817520884 := by
        calc
          (3 : ZMod 1719110381) ^ 3203 = (3 : ZMod 1719110381) ^ (1601 + 1601 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1601 * (3 : ZMod 1719110381) ^ 1601) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 817520884 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 1719110381) ^ 6407 = 980452595 := by
        calc
          (3 : ZMod 1719110381) ^ 6407 = (3 : ZMod 1719110381) ^ (3203 + 3203 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 3203 * (3 : ZMod 1719110381) ^ 3203) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 980452595 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 1719110381) ^ 12815 = 291558002 := by
        calc
          (3 : ZMod 1719110381) ^ 12815 = (3 : ZMod 1719110381) ^ (6407 + 6407 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 6407 * (3 : ZMod 1719110381) ^ 6407) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 291558002 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 1719110381) ^ 25630 = 390775256 := by
        calc
          (3 : ZMod 1719110381) ^ 25630 = (3 : ZMod 1719110381) ^ (12815 + 12815) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 12815 * (3 : ZMod 1719110381) ^ 12815 := by rw [pow_add]
          _ = 390775256 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 1719110381) ^ 51261 = 1388734023 := by
        calc
          (3 : ZMod 1719110381) ^ 51261 = (3 : ZMod 1719110381) ^ (25630 + 25630 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 25630 * (3 : ZMod 1719110381) ^ 25630) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1388734023 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 1719110381) ^ 102523 = 1392456879 := by
        calc
          (3 : ZMod 1719110381) ^ 102523 = (3 : ZMod 1719110381) ^ (51261 + 51261 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 51261 * (3 : ZMod 1719110381) ^ 51261) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1392456879 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 1719110381) ^ 205046 = 517726078 := by
        calc
          (3 : ZMod 1719110381) ^ 205046 = (3 : ZMod 1719110381) ^ (102523 + 102523) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 102523 * (3 : ZMod 1719110381) ^ 102523 := by rw [pow_add]
          _ = 517726078 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 1719110381) ^ 410093 = 1470006344 := by
        calc
          (3 : ZMod 1719110381) ^ 410093 = (3 : ZMod 1719110381) ^ (205046 + 205046 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 205046 * (3 : ZMod 1719110381) ^ 205046) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1470006344 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 1719110381) ^ 820186 = 320152898 := by
        calc
          (3 : ZMod 1719110381) ^ 820186 = (3 : ZMod 1719110381) ^ (410093 + 410093) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 410093 * (3 : ZMod 1719110381) ^ 410093 := by rw [pow_add]
          _ = 320152898 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 1719110381) ^ 1640372 = 1079607517 := by
        calc
          (3 : ZMod 1719110381) ^ 1640372 = (3 : ZMod 1719110381) ^ (820186 + 820186) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 820186 * (3 : ZMod 1719110381) ^ 820186 := by rw [pow_add]
          _ = 1079607517 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 1719110381) ^ 3280745 = 1069493189 := by
        calc
          (3 : ZMod 1719110381) ^ 3280745 = (3 : ZMod 1719110381) ^ (1640372 + 1640372 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1640372 * (3 : ZMod 1719110381) ^ 1640372) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1069493189 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 1719110381) ^ 6561490 = 491191090 := by
        calc
          (3 : ZMod 1719110381) ^ 6561490 = (3 : ZMod 1719110381) ^ (3280745 + 3280745) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 3280745 * (3 : ZMod 1719110381) ^ 3280745 := by rw [pow_add]
          _ = 491191090 := by rw [factor_4_21]; decide
      have factor_4_23 : (3 : ZMod 1719110381) ^ 13122980 = 1226002239 := by
        calc
          (3 : ZMod 1719110381) ^ 13122980 = (3 : ZMod 1719110381) ^ (6561490 + 6561490) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 6561490 * (3 : ZMod 1719110381) ^ 6561490 := by rw [pow_add]
          _ = 1226002239 := by rw [factor_4_22]; decide
      change (3 : ZMod 1719110381) ^ 13122980 ≠ 1
      rw [factor_4_23]
      decide
    ·
      have factor_5_0 : (3 : ZMod 1719110381) ^ 1 = 3 := by norm_num
      have factor_5_1 : (3 : ZMod 1719110381) ^ 2 = 9 := by
        calc
          (3 : ZMod 1719110381) ^ 2 = (3 : ZMod 1719110381) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 1 * (3 : ZMod 1719110381) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_5_0]; decide
      have factor_5_2 : (3 : ZMod 1719110381) ^ 4 = 81 := by
        calc
          (3 : ZMod 1719110381) ^ 4 = (3 : ZMod 1719110381) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 2 * (3 : ZMod 1719110381) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_5_1]; decide
      have factor_5_3 : (3 : ZMod 1719110381) ^ 8 = 6561 := by
        calc
          (3 : ZMod 1719110381) ^ 8 = (3 : ZMod 1719110381) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 4 * (3 : ZMod 1719110381) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_5_2]; decide
      have factor_5_4 : (3 : ZMod 1719110381) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 1719110381) ^ 17 = (3 : ZMod 1719110381) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 8 * (3 : ZMod 1719110381) ^ 8) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_5_3]; decide
      have factor_5_5 : (3 : ZMod 1719110381) ^ 35 = 623095747 := by
        calc
          (3 : ZMod 1719110381) ^ 35 = (3 : ZMod 1719110381) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 17 * (3 : ZMod 1719110381) ^ 17) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 623095747 := by rw [factor_5_4]; decide
      have factor_5_6 : (3 : ZMod 1719110381) ^ 70 = 1651658458 := by
        calc
          (3 : ZMod 1719110381) ^ 70 = (3 : ZMod 1719110381) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 35 * (3 : ZMod 1719110381) ^ 35 := by rw [pow_add]
          _ = 1651658458 := by rw [factor_5_5]; decide
      have factor_5_7 : (3 : ZMod 1719110381) ^ 141 = 1450083990 := by
        calc
          (3 : ZMod 1719110381) ^ 141 = (3 : ZMod 1719110381) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 70 * (3 : ZMod 1719110381) ^ 70) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1450083990 := by rw [factor_5_6]; decide
      have factor_5_8 : (3 : ZMod 1719110381) ^ 282 = 471550482 := by
        calc
          (3 : ZMod 1719110381) ^ 282 = (3 : ZMod 1719110381) ^ (141 + 141) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 141 * (3 : ZMod 1719110381) ^ 141 := by rw [pow_add]
          _ = 471550482 := by rw [factor_5_7]; decide
      have factor_5_9 : (3 : ZMod 1719110381) ^ 565 = 1698348512 := by
        calc
          (3 : ZMod 1719110381) ^ 565 = (3 : ZMod 1719110381) ^ (282 + 282 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 282 * (3 : ZMod 1719110381) ^ 282) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 1698348512 := by rw [factor_5_8]; decide
      have factor_5_10 : (3 : ZMod 1719110381) ^ 1130 = 310110078 := by
        calc
          (3 : ZMod 1719110381) ^ 1130 = (3 : ZMod 1719110381) ^ (565 + 565) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 565 * (3 : ZMod 1719110381) ^ 565 := by rw [pow_add]
          _ = 310110078 := by rw [factor_5_9]; decide
      have factor_5_11 : (3 : ZMod 1719110381) ^ 2261 = 114973293 := by
        calc
          (3 : ZMod 1719110381) ^ 2261 = (3 : ZMod 1719110381) ^ (1130 + 1130 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 1130 * (3 : ZMod 1719110381) ^ 1130) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 114973293 := by rw [factor_5_10]; decide
      have factor_5_12 : (3 : ZMod 1719110381) ^ 4523 = 231163448 := by
        calc
          (3 : ZMod 1719110381) ^ 4523 = (3 : ZMod 1719110381) ^ (2261 + 2261 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 2261 * (3 : ZMod 1719110381) ^ 2261) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 231163448 := by rw [factor_5_11]; decide
      have factor_5_13 : (3 : ZMod 1719110381) ^ 9047 = 818145374 := by
        calc
          (3 : ZMod 1719110381) ^ 9047 = (3 : ZMod 1719110381) ^ (4523 + 4523 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 4523 * (3 : ZMod 1719110381) ^ 4523) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 818145374 := by rw [factor_5_12]; decide
      have factor_5_14 : (3 : ZMod 1719110381) ^ 18094 = 1126387721 := by
        calc
          (3 : ZMod 1719110381) ^ 18094 = (3 : ZMod 1719110381) ^ (9047 + 9047) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 9047 * (3 : ZMod 1719110381) ^ 9047 := by rw [pow_add]
          _ = 1126387721 := by rw [factor_5_13]; decide
      have factor_5_15 : (3 : ZMod 1719110381) ^ 36188 = 201485238 := by
        calc
          (3 : ZMod 1719110381) ^ 36188 = (3 : ZMod 1719110381) ^ (18094 + 18094) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 18094 * (3 : ZMod 1719110381) ^ 18094 := by rw [pow_add]
          _ = 201485238 := by rw [factor_5_14]; decide
      have factor_5_16 : (3 : ZMod 1719110381) ^ 72377 = 12291068 := by
        calc
          (3 : ZMod 1719110381) ^ 72377 = (3 : ZMod 1719110381) ^ (36188 + 36188 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 36188 * (3 : ZMod 1719110381) ^ 36188) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 12291068 := by rw [factor_5_15]; decide
      have factor_5_17 : (3 : ZMod 1719110381) ^ 144755 = 268888461 := by
        calc
          (3 : ZMod 1719110381) ^ 144755 = (3 : ZMod 1719110381) ^ (72377 + 72377 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = ((3 : ZMod 1719110381) ^ 72377 * (3 : ZMod 1719110381) ^ 72377) * (3 : ZMod 1719110381) := by rw [pow_succ, pow_add]
          _ = 268888461 := by rw [factor_5_16]; decide
      have factor_5_18 : (3 : ZMod 1719110381) ^ 289510 = 960947701 := by
        calc
          (3 : ZMod 1719110381) ^ 289510 = (3 : ZMod 1719110381) ^ (144755 + 144755) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 144755 * (3 : ZMod 1719110381) ^ 144755 := by rw [pow_add]
          _ = 960947701 := by rw [factor_5_17]; decide
      have factor_5_19 : (3 : ZMod 1719110381) ^ 579020 = 800069582 := by
        calc
          (3 : ZMod 1719110381) ^ 579020 = (3 : ZMod 1719110381) ^ (289510 + 289510) :=
            congrArg (fun n : ℕ => (3 : ZMod 1719110381) ^ n) (by norm_num)
          _ = (3 : ZMod 1719110381) ^ 289510 * (3 : ZMod 1719110381) ^ 289510 := by rw [pow_add]
          _ = 800069582 := by rw [factor_5_18]; decide
      change (3 : ZMod 1719110381) ^ 579020 ≠ 1
      rw [factor_5_19]
      decide

#print axioms prime_lucas_1719110381

end TotientTailPeriodKiller
end Erdos249257
