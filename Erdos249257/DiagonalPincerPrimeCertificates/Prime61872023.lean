import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_61872023 : Nat.Prime 61872023 := by
  apply lucas_primality 61872023 (5 : ZMod 61872023)
  ·
      have fermat_0 : (5 : ZMod 61872023) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 61872023) ^ 3 = 125 := by
        calc
          (5 : ZMod 61872023) ^ 3 = (5 : ZMod 61872023) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 1 * (5 : ZMod 61872023) ^ 1) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 61872023) ^ 7 = 78125 := by
        calc
          (5 : ZMod 61872023) ^ 7 = (5 : ZMod 61872023) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 3 * (5 : ZMod 61872023) ^ 3) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 61872023) ^ 14 = 40057371 := by
        calc
          (5 : ZMod 61872023) ^ 14 = (5 : ZMod 61872023) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 7 * (5 : ZMod 61872023) ^ 7 := by rw [pow_add]
          _ = 40057371 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 61872023) ^ 29 = 21316914 := by
        calc
          (5 : ZMod 61872023) ^ 29 = (5 : ZMod 61872023) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 14 * (5 : ZMod 61872023) ^ 14) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 21316914 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 61872023) ^ 59 = 16438821 := by
        calc
          (5 : ZMod 61872023) ^ 59 = (5 : ZMod 61872023) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 29 * (5 : ZMod 61872023) ^ 29) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 16438821 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 61872023) ^ 118 = 51462298 := by
        calc
          (5 : ZMod 61872023) ^ 118 = (5 : ZMod 61872023) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 59 * (5 : ZMod 61872023) ^ 59 := by rw [pow_add]
          _ = 51462298 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 61872023) ^ 236 = 22853540 := by
        calc
          (5 : ZMod 61872023) ^ 236 = (5 : ZMod 61872023) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 118 * (5 : ZMod 61872023) ^ 118 := by rw [pow_add]
          _ = 22853540 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 61872023) ^ 472 = 22972228 := by
        calc
          (5 : ZMod 61872023) ^ 472 = (5 : ZMod 61872023) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 236 * (5 : ZMod 61872023) ^ 236 := by rw [pow_add]
          _ = 22972228 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 61872023) ^ 944 = 7798751 := by
        calc
          (5 : ZMod 61872023) ^ 944 = (5 : ZMod 61872023) ^ (472 + 472) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 472 * (5 : ZMod 61872023) ^ 472 := by rw [pow_add]
          _ = 7798751 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 61872023) ^ 1888 = 9190886 := by
        calc
          (5 : ZMod 61872023) ^ 1888 = (5 : ZMod 61872023) ^ (944 + 944) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 944 * (5 : ZMod 61872023) ^ 944 := by rw [pow_add]
          _ = 9190886 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 61872023) ^ 3776 = 59263671 := by
        calc
          (5 : ZMod 61872023) ^ 3776 = (5 : ZMod 61872023) ^ (1888 + 1888) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 1888 * (5 : ZMod 61872023) ^ 1888 := by rw [pow_add]
          _ = 59263671 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 61872023) ^ 7552 = 52506824 := by
        calc
          (5 : ZMod 61872023) ^ 7552 = (5 : ZMod 61872023) ^ (3776 + 3776) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 3776 * (5 : ZMod 61872023) ^ 3776 := by rw [pow_add]
          _ = 52506824 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 61872023) ^ 15105 = 31217272 := by
        calc
          (5 : ZMod 61872023) ^ 15105 = (5 : ZMod 61872023) ^ (7552 + 7552 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 7552 * (5 : ZMod 61872023) ^ 7552) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 31217272 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 61872023) ^ 30210 = 50491472 := by
        calc
          (5 : ZMod 61872023) ^ 30210 = (5 : ZMod 61872023) ^ (15105 + 15105) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 15105 * (5 : ZMod 61872023) ^ 15105 := by rw [pow_add]
          _ = 50491472 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 61872023) ^ 60421 = 1020068 := by
        calc
          (5 : ZMod 61872023) ^ 60421 = (5 : ZMod 61872023) ^ (30210 + 30210 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 30210 * (5 : ZMod 61872023) ^ 30210) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 1020068 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 61872023) ^ 120843 = 60825119 := by
        calc
          (5 : ZMod 61872023) ^ 120843 = (5 : ZMod 61872023) ^ (60421 + 60421 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 60421 * (5 : ZMod 61872023) ^ 60421) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 60825119 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 61872023) ^ 241687 = 34848970 := by
        calc
          (5 : ZMod 61872023) ^ 241687 = (5 : ZMod 61872023) ^ (120843 + 120843 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 120843 * (5 : ZMod 61872023) ^ 120843) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 34848970 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 61872023) ^ 483375 = 2618981 := by
        calc
          (5 : ZMod 61872023) ^ 483375 = (5 : ZMod 61872023) ^ (241687 + 241687 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 241687 * (5 : ZMod 61872023) ^ 241687) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 2618981 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 61872023) ^ 966750 = 52752627 := by
        calc
          (5 : ZMod 61872023) ^ 966750 = (5 : ZMod 61872023) ^ (483375 + 483375) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 483375 * (5 : ZMod 61872023) ^ 483375 := by rw [pow_add]
          _ = 52752627 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 61872023) ^ 1933500 = 21722079 := by
        calc
          (5 : ZMod 61872023) ^ 1933500 = (5 : ZMod 61872023) ^ (966750 + 966750) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 966750 * (5 : ZMod 61872023) ^ 966750 := by rw [pow_add]
          _ = 21722079 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 61872023) ^ 3867001 = 48341676 := by
        calc
          (5 : ZMod 61872023) ^ 3867001 = (5 : ZMod 61872023) ^ (1933500 + 1933500 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 1933500 * (5 : ZMod 61872023) ^ 1933500) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 48341676 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 61872023) ^ 7734002 = 7198767 := by
        calc
          (5 : ZMod 61872023) ^ 7734002 = (5 : ZMod 61872023) ^ (3867001 + 3867001) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 3867001 * (5 : ZMod 61872023) ^ 3867001 := by rw [pow_add]
          _ = 7198767 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 61872023) ^ 15468005 = 46976734 := by
        calc
          (5 : ZMod 61872023) ^ 15468005 = (5 : ZMod 61872023) ^ (7734002 + 7734002 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 7734002 * (5 : ZMod 61872023) ^ 7734002) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 46976734 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 61872023) ^ 30936011 = 61872022 := by
        calc
          (5 : ZMod 61872023) ^ 30936011 = (5 : ZMod 61872023) ^ (15468005 + 15468005 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 15468005 * (5 : ZMod 61872023) ^ 15468005) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 61872022 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 61872023) ^ 61872022 = 1 := by
        calc
          (5 : ZMod 61872023) ^ 61872022 = (5 : ZMod 61872023) ^ (30936011 + 30936011) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 30936011 * (5 : ZMod 61872023) ^ 30936011 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (47, 1), (22697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (47, 1), (22697, 1)] : List FactorBlock).map factorBlockValue).prod = 61872023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 61872023) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 61872023) ^ 3 = 125 := by
        calc
          (5 : ZMod 61872023) ^ 3 = (5 : ZMod 61872023) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 1 * (5 : ZMod 61872023) ^ 1) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 61872023) ^ 7 = 78125 := by
        calc
          (5 : ZMod 61872023) ^ 7 = (5 : ZMod 61872023) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 3 * (5 : ZMod 61872023) ^ 3) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 61872023) ^ 14 = 40057371 := by
        calc
          (5 : ZMod 61872023) ^ 14 = (5 : ZMod 61872023) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 7 * (5 : ZMod 61872023) ^ 7 := by rw [pow_add]
          _ = 40057371 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 61872023) ^ 29 = 21316914 := by
        calc
          (5 : ZMod 61872023) ^ 29 = (5 : ZMod 61872023) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 14 * (5 : ZMod 61872023) ^ 14) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 21316914 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 61872023) ^ 59 = 16438821 := by
        calc
          (5 : ZMod 61872023) ^ 59 = (5 : ZMod 61872023) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 29 * (5 : ZMod 61872023) ^ 29) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 16438821 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 61872023) ^ 118 = 51462298 := by
        calc
          (5 : ZMod 61872023) ^ 118 = (5 : ZMod 61872023) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 59 * (5 : ZMod 61872023) ^ 59 := by rw [pow_add]
          _ = 51462298 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 61872023) ^ 236 = 22853540 := by
        calc
          (5 : ZMod 61872023) ^ 236 = (5 : ZMod 61872023) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 118 * (5 : ZMod 61872023) ^ 118 := by rw [pow_add]
          _ = 22853540 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 61872023) ^ 472 = 22972228 := by
        calc
          (5 : ZMod 61872023) ^ 472 = (5 : ZMod 61872023) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 236 * (5 : ZMod 61872023) ^ 236 := by rw [pow_add]
          _ = 22972228 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 61872023) ^ 944 = 7798751 := by
        calc
          (5 : ZMod 61872023) ^ 944 = (5 : ZMod 61872023) ^ (472 + 472) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 472 * (5 : ZMod 61872023) ^ 472 := by rw [pow_add]
          _ = 7798751 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 61872023) ^ 1888 = 9190886 := by
        calc
          (5 : ZMod 61872023) ^ 1888 = (5 : ZMod 61872023) ^ (944 + 944) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 944 * (5 : ZMod 61872023) ^ 944 := by rw [pow_add]
          _ = 9190886 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 61872023) ^ 3776 = 59263671 := by
        calc
          (5 : ZMod 61872023) ^ 3776 = (5 : ZMod 61872023) ^ (1888 + 1888) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 1888 * (5 : ZMod 61872023) ^ 1888 := by rw [pow_add]
          _ = 59263671 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 61872023) ^ 7552 = 52506824 := by
        calc
          (5 : ZMod 61872023) ^ 7552 = (5 : ZMod 61872023) ^ (3776 + 3776) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 3776 * (5 : ZMod 61872023) ^ 3776 := by rw [pow_add]
          _ = 52506824 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 61872023) ^ 15105 = 31217272 := by
        calc
          (5 : ZMod 61872023) ^ 15105 = (5 : ZMod 61872023) ^ (7552 + 7552 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 7552 * (5 : ZMod 61872023) ^ 7552) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 31217272 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 61872023) ^ 30210 = 50491472 := by
        calc
          (5 : ZMod 61872023) ^ 30210 = (5 : ZMod 61872023) ^ (15105 + 15105) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 15105 * (5 : ZMod 61872023) ^ 15105 := by rw [pow_add]
          _ = 50491472 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 61872023) ^ 60421 = 1020068 := by
        calc
          (5 : ZMod 61872023) ^ 60421 = (5 : ZMod 61872023) ^ (30210 + 30210 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 30210 * (5 : ZMod 61872023) ^ 30210) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 1020068 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 61872023) ^ 120843 = 60825119 := by
        calc
          (5 : ZMod 61872023) ^ 120843 = (5 : ZMod 61872023) ^ (60421 + 60421 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 60421 * (5 : ZMod 61872023) ^ 60421) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 60825119 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 61872023) ^ 241687 = 34848970 := by
        calc
          (5 : ZMod 61872023) ^ 241687 = (5 : ZMod 61872023) ^ (120843 + 120843 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 120843 * (5 : ZMod 61872023) ^ 120843) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 34848970 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 61872023) ^ 483375 = 2618981 := by
        calc
          (5 : ZMod 61872023) ^ 483375 = (5 : ZMod 61872023) ^ (241687 + 241687 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 241687 * (5 : ZMod 61872023) ^ 241687) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 2618981 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 61872023) ^ 966750 = 52752627 := by
        calc
          (5 : ZMod 61872023) ^ 966750 = (5 : ZMod 61872023) ^ (483375 + 483375) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 483375 * (5 : ZMod 61872023) ^ 483375 := by rw [pow_add]
          _ = 52752627 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 61872023) ^ 1933500 = 21722079 := by
        calc
          (5 : ZMod 61872023) ^ 1933500 = (5 : ZMod 61872023) ^ (966750 + 966750) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 966750 * (5 : ZMod 61872023) ^ 966750 := by rw [pow_add]
          _ = 21722079 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 61872023) ^ 3867001 = 48341676 := by
        calc
          (5 : ZMod 61872023) ^ 3867001 = (5 : ZMod 61872023) ^ (1933500 + 1933500 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 1933500 * (5 : ZMod 61872023) ^ 1933500) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 48341676 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 61872023) ^ 7734002 = 7198767 := by
        calc
          (5 : ZMod 61872023) ^ 7734002 = (5 : ZMod 61872023) ^ (3867001 + 3867001) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 3867001 * (5 : ZMod 61872023) ^ 3867001 := by rw [pow_add]
          _ = 7198767 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 61872023) ^ 15468005 = 46976734 := by
        calc
          (5 : ZMod 61872023) ^ 15468005 = (5 : ZMod 61872023) ^ (7734002 + 7734002 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 7734002 * (5 : ZMod 61872023) ^ 7734002) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 46976734 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 61872023) ^ 30936011 = 61872022 := by
        calc
          (5 : ZMod 61872023) ^ 30936011 = (5 : ZMod 61872023) ^ (15468005 + 15468005 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 15468005 * (5 : ZMod 61872023) ^ 15468005) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 61872022 := by rw [factor_0_23]; decide
      change (5 : ZMod 61872023) ^ 30936011 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (5 : ZMod 61872023) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 61872023) ^ 2 = 25 := by
        calc
          (5 : ZMod 61872023) ^ 2 = (5 : ZMod 61872023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 1 * (5 : ZMod 61872023) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 61872023) ^ 4 = 625 := by
        calc
          (5 : ZMod 61872023) ^ 4 = (5 : ZMod 61872023) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 2 * (5 : ZMod 61872023) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 61872023) ^ 8 = 390625 := by
        calc
          (5 : ZMod 61872023) ^ 8 = (5 : ZMod 61872023) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 4 * (5 : ZMod 61872023) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 61872023) ^ 16 = 11481907 := by
        calc
          (5 : ZMod 61872023) ^ 16 = (5 : ZMod 61872023) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 8 * (5 : ZMod 61872023) ^ 8 := by rw [pow_add]
          _ = 11481907 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 61872023) ^ 32 = 4117261 := by
        calc
          (5 : ZMod 61872023) ^ 32 = (5 : ZMod 61872023) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 16 * (5 : ZMod 61872023) ^ 16 := by rw [pow_add]
          _ = 4117261 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 61872023) ^ 65 = 25810652 := by
        calc
          (5 : ZMod 61872023) ^ 65 = (5 : ZMod 61872023) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 32 * (5 : ZMod 61872023) ^ 32) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 25810652 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 61872023) ^ 130 = 11307021 := by
        calc
          (5 : ZMod 61872023) ^ 130 = (5 : ZMod 61872023) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 65 * (5 : ZMod 61872023) ^ 65 := by rw [pow_add]
          _ = 11307021 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 61872023) ^ 260 = 26016598 := by
        calc
          (5 : ZMod 61872023) ^ 260 = (5 : ZMod 61872023) ^ (130 + 130) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 130 * (5 : ZMod 61872023) ^ 130 := by rw [pow_add]
          _ = 26016598 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 61872023) ^ 520 = 21575768 := by
        calc
          (5 : ZMod 61872023) ^ 520 = (5 : ZMod 61872023) ^ (260 + 260) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 260 * (5 : ZMod 61872023) ^ 260 := by rw [pow_add]
          _ = 21575768 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 61872023) ^ 1041 = 55334211 := by
        calc
          (5 : ZMod 61872023) ^ 1041 = (5 : ZMod 61872023) ^ (520 + 520 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 520 * (5 : ZMod 61872023) ^ 520) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 55334211 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 61872023) ^ 2083 = 51723408 := by
        calc
          (5 : ZMod 61872023) ^ 2083 = (5 : ZMod 61872023) ^ (1041 + 1041 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 1041 * (5 : ZMod 61872023) ^ 1041) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 51723408 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 61872023) ^ 4167 = 9570008 := by
        calc
          (5 : ZMod 61872023) ^ 4167 = (5 : ZMod 61872023) ^ (2083 + 2083 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 2083 * (5 : ZMod 61872023) ^ 2083) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 9570008 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 61872023) ^ 8334 = 42898705 := by
        calc
          (5 : ZMod 61872023) ^ 8334 = (5 : ZMod 61872023) ^ (4167 + 4167) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 4167 * (5 : ZMod 61872023) ^ 4167 := by rw [pow_add]
          _ = 42898705 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 61872023) ^ 16668 = 21853420 := by
        calc
          (5 : ZMod 61872023) ^ 16668 = (5 : ZMod 61872023) ^ (8334 + 8334) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 8334 * (5 : ZMod 61872023) ^ 8334 := by rw [pow_add]
          _ = 21853420 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 61872023) ^ 33336 = 10534162 := by
        calc
          (5 : ZMod 61872023) ^ 33336 = (5 : ZMod 61872023) ^ (16668 + 16668) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 16668 * (5 : ZMod 61872023) ^ 16668 := by rw [pow_add]
          _ = 10534162 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 61872023) ^ 66672 = 43967353 := by
        calc
          (5 : ZMod 61872023) ^ 66672 = (5 : ZMod 61872023) ^ (33336 + 33336) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 33336 * (5 : ZMod 61872023) ^ 33336 := by rw [pow_add]
          _ = 43967353 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 61872023) ^ 133344 = 4399115 := by
        calc
          (5 : ZMod 61872023) ^ 133344 = (5 : ZMod 61872023) ^ (66672 + 66672) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 66672 * (5 : ZMod 61872023) ^ 66672 := by rw [pow_add]
          _ = 4399115 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 61872023) ^ 266689 = 25866655 := by
        calc
          (5 : ZMod 61872023) ^ 266689 = (5 : ZMod 61872023) ^ (133344 + 133344 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 133344 * (5 : ZMod 61872023) ^ 133344) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 25866655 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 61872023) ^ 533379 = 34531539 := by
        calc
          (5 : ZMod 61872023) ^ 533379 = (5 : ZMod 61872023) ^ (266689 + 266689 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 266689 * (5 : ZMod 61872023) ^ 266689) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 34531539 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 61872023) ^ 1066759 = 41871681 := by
        calc
          (5 : ZMod 61872023) ^ 1066759 = (5 : ZMod 61872023) ^ (533379 + 533379 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 533379 * (5 : ZMod 61872023) ^ 533379) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 41871681 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 61872023) ^ 2133518 = 38201870 := by
        calc
          (5 : ZMod 61872023) ^ 2133518 = (5 : ZMod 61872023) ^ (1066759 + 1066759) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 1066759 * (5 : ZMod 61872023) ^ 1066759 := by rw [pow_add]
          _ = 38201870 := by rw [factor_1_20]; decide
      change (5 : ZMod 61872023) ^ 2133518 ≠ 1
      rw [factor_1_21]
      decide
    ·
      have factor_2_0 : (5 : ZMod 61872023) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 61872023) ^ 2 = 25 := by
        calc
          (5 : ZMod 61872023) ^ 2 = (5 : ZMod 61872023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 1 * (5 : ZMod 61872023) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 61872023) ^ 5 = 3125 := by
        calc
          (5 : ZMod 61872023) ^ 5 = (5 : ZMod 61872023) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 2 * (5 : ZMod 61872023) ^ 2) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 61872023) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 61872023) ^ 10 = (5 : ZMod 61872023) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 5 * (5 : ZMod 61872023) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 61872023) ^ 20 = 60909230 := by
        calc
          (5 : ZMod 61872023) ^ 20 = (5 : ZMod 61872023) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 10 * (5 : ZMod 61872023) ^ 10 := by rw [pow_add]
          _ = 60909230 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 61872023) ^ 40 = 3712263 := by
        calc
          (5 : ZMod 61872023) ^ 40 = (5 : ZMod 61872023) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 20 * (5 : ZMod 61872023) ^ 20 := by rw [pow_add]
          _ = 3712263 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 61872023) ^ 80 = 17154333 := by
        calc
          (5 : ZMod 61872023) ^ 80 = (5 : ZMod 61872023) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 40 * (5 : ZMod 61872023) ^ 40 := by rw [pow_add]
          _ = 17154333 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 61872023) ^ 160 = 3411991 := by
        calc
          (5 : ZMod 61872023) ^ 160 = (5 : ZMod 61872023) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 80 * (5 : ZMod 61872023) ^ 80 := by rw [pow_add]
          _ = 3411991 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 61872023) ^ 321 = 18018304 := by
        calc
          (5 : ZMod 61872023) ^ 321 = (5 : ZMod 61872023) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 160 * (5 : ZMod 61872023) ^ 160) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 18018304 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 61872023) ^ 642 = 7037183 := by
        calc
          (5 : ZMod 61872023) ^ 642 = (5 : ZMod 61872023) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 321 * (5 : ZMod 61872023) ^ 321 := by rw [pow_add]
          _ = 7037183 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 61872023) ^ 1285 = 52352250 := by
        calc
          (5 : ZMod 61872023) ^ 1285 = (5 : ZMod 61872023) ^ (642 + 642 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 642 * (5 : ZMod 61872023) ^ 642) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 52352250 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 61872023) ^ 2571 = 49301212 := by
        calc
          (5 : ZMod 61872023) ^ 2571 = (5 : ZMod 61872023) ^ (1285 + 1285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 1285 * (5 : ZMod 61872023) ^ 1285) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 49301212 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 61872023) ^ 5142 = 58902203 := by
        calc
          (5 : ZMod 61872023) ^ 5142 = (5 : ZMod 61872023) ^ (2571 + 2571) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 2571 * (5 : ZMod 61872023) ^ 2571 := by rw [pow_add]
          _ = 58902203 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 61872023) ^ 10284 = 35825773 := by
        calc
          (5 : ZMod 61872023) ^ 10284 = (5 : ZMod 61872023) ^ (5142 + 5142) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 5142 * (5 : ZMod 61872023) ^ 5142 := by rw [pow_add]
          _ = 35825773 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 61872023) ^ 20569 = 39621932 := by
        calc
          (5 : ZMod 61872023) ^ 20569 = (5 : ZMod 61872023) ^ (10284 + 10284 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 10284 * (5 : ZMod 61872023) ^ 10284) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 39621932 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 61872023) ^ 41138 = 32354701 := by
        calc
          (5 : ZMod 61872023) ^ 41138 = (5 : ZMod 61872023) ^ (20569 + 20569) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 20569 * (5 : ZMod 61872023) ^ 20569 := by rw [pow_add]
          _ = 32354701 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 61872023) ^ 82276 = 60329249 := by
        calc
          (5 : ZMod 61872023) ^ 82276 = (5 : ZMod 61872023) ^ (41138 + 41138) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 41138 * (5 : ZMod 61872023) ^ 41138 := by rw [pow_add]
          _ = 60329249 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 61872023) ^ 164553 = 45683468 := by
        calc
          (5 : ZMod 61872023) ^ 164553 = (5 : ZMod 61872023) ^ (82276 + 82276 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 82276 * (5 : ZMod 61872023) ^ 82276) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 45683468 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 61872023) ^ 329106 = 26943684 := by
        calc
          (5 : ZMod 61872023) ^ 329106 = (5 : ZMod 61872023) ^ (164553 + 164553) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 164553 * (5 : ZMod 61872023) ^ 164553 := by rw [pow_add]
          _ = 26943684 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 61872023) ^ 658213 = 16787459 := by
        calc
          (5 : ZMod 61872023) ^ 658213 = (5 : ZMod 61872023) ^ (329106 + 329106 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 329106 * (5 : ZMod 61872023) ^ 329106) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 16787459 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 61872023) ^ 1316426 = 5762763 := by
        calc
          (5 : ZMod 61872023) ^ 1316426 = (5 : ZMod 61872023) ^ (658213 + 658213) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 658213 * (5 : ZMod 61872023) ^ 658213 := by rw [pow_add]
          _ = 5762763 := by rw [factor_2_19]; decide
      change (5 : ZMod 61872023) ^ 1316426 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (5 : ZMod 61872023) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 61872023) ^ 2 = 25 := by
        calc
          (5 : ZMod 61872023) ^ 2 = (5 : ZMod 61872023) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 1 * (5 : ZMod 61872023) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 61872023) ^ 5 = 3125 := by
        calc
          (5 : ZMod 61872023) ^ 5 = (5 : ZMod 61872023) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 2 * (5 : ZMod 61872023) ^ 2) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 61872023) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 61872023) ^ 10 = (5 : ZMod 61872023) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 5 * (5 : ZMod 61872023) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 61872023) ^ 21 = 57058058 := by
        calc
          (5 : ZMod 61872023) ^ 21 = (5 : ZMod 61872023) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 10 * (5 : ZMod 61872023) ^ 10) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 57058058 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 61872023) ^ 42 = 30934552 := by
        calc
          (5 : ZMod 61872023) ^ 42 = (5 : ZMod 61872023) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 21 * (5 : ZMod 61872023) ^ 21 := by rw [pow_add]
          _ = 30934552 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 61872023) ^ 85 = 26118707 := by
        calc
          (5 : ZMod 61872023) ^ 85 = (5 : ZMod 61872023) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 42 * (5 : ZMod 61872023) ^ 42) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 26118707 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 61872023) ^ 170 = 36575093 := by
        calc
          (5 : ZMod 61872023) ^ 170 = (5 : ZMod 61872023) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 85 * (5 : ZMod 61872023) ^ 85 := by rw [pow_add]
          _ = 36575093 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 61872023) ^ 340 = 5666752 := by
        calc
          (5 : ZMod 61872023) ^ 340 = (5 : ZMod 61872023) ^ (170 + 170) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 170 * (5 : ZMod 61872023) ^ 170 := by rw [pow_add]
          _ = 5666752 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 61872023) ^ 681 = 16581600 := by
        calc
          (5 : ZMod 61872023) ^ 681 = (5 : ZMod 61872023) ^ (340 + 340 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 340 * (5 : ZMod 61872023) ^ 340) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 16581600 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 61872023) ^ 1363 = 6254239 := by
        calc
          (5 : ZMod 61872023) ^ 1363 = (5 : ZMod 61872023) ^ (681 + 681 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = ((5 : ZMod 61872023) ^ 681 * (5 : ZMod 61872023) ^ 681) * (5 : ZMod 61872023) := by rw [pow_succ, pow_add]
          _ = 6254239 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 61872023) ^ 2726 = 12528521 := by
        calc
          (5 : ZMod 61872023) ^ 2726 = (5 : ZMod 61872023) ^ (1363 + 1363) :=
            congrArg (fun n : ℕ => (5 : ZMod 61872023) ^ n) (by norm_num)
          _ = (5 : ZMod 61872023) ^ 1363 * (5 : ZMod 61872023) ^ 1363 := by rw [pow_add]
          _ = 12528521 := by rw [factor_3_10]; decide
      change (5 : ZMod 61872023) ^ 2726 ≠ 1
      rw [factor_3_11]
      decide

#print axioms prime_lucas_61872023

end TotientTailPeriodKiller
end Erdos249257
