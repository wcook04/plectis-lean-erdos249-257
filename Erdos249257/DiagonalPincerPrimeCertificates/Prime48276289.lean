import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_48276289 : Nat.Prime 48276289 := by
  apply lucas_primality 48276289 (7 : ZMod 48276289)
  ·
      have fermat_0 : (7 : ZMod 48276289) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 48276289) ^ 2 = 49 := by
        calc
          (7 : ZMod 48276289) ^ 2 = (7 : ZMod 48276289) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 1 * (7 : ZMod 48276289) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 48276289) ^ 5 = 16807 := by
        calc
          (7 : ZMod 48276289) ^ 5 = (7 : ZMod 48276289) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 2 * (7 : ZMod 48276289) ^ 2) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 48276289) ^ 11 = 46275183 := by
        calc
          (7 : ZMod 48276289) ^ 11 = (7 : ZMod 48276289) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 5 * (7 : ZMod 48276289) ^ 5) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 46275183 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 48276289) ^ 23 = 25222848 := by
        calc
          (7 : ZMod 48276289) ^ 23 = (7 : ZMod 48276289) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 11 * (7 : ZMod 48276289) ^ 11) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 25222848 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 48276289) ^ 46 = 28174621 := by
        calc
          (7 : ZMod 48276289) ^ 46 = (7 : ZMod 48276289) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 23 * (7 : ZMod 48276289) ^ 23 := by rw [pow_add]
          _ = 28174621 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 48276289) ^ 92 = 27757347 := by
        calc
          (7 : ZMod 48276289) ^ 92 = (7 : ZMod 48276289) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 46 * (7 : ZMod 48276289) ^ 46 := by rw [pow_add]
          _ = 27757347 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 48276289) ^ 184 = 2277720 := by
        calc
          (7 : ZMod 48276289) ^ 184 = (7 : ZMod 48276289) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 92 * (7 : ZMod 48276289) ^ 92 := by rw [pow_add]
          _ = 2277720 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 48276289) ^ 368 = 45277304 := by
        calc
          (7 : ZMod 48276289) ^ 368 = (7 : ZMod 48276289) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 184 * (7 : ZMod 48276289) ^ 184 := by rw [pow_add]
          _ = 45277304 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 48276289) ^ 736 = 38389525 := by
        calc
          (7 : ZMod 48276289) ^ 736 = (7 : ZMod 48276289) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 368 * (7 : ZMod 48276289) ^ 368 := by rw [pow_add]
          _ = 38389525 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 48276289) ^ 1473 = 24320011 := by
        calc
          (7 : ZMod 48276289) ^ 1473 = (7 : ZMod 48276289) ^ (736 + 736 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 736 * (7 : ZMod 48276289) ^ 736) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 24320011 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 48276289) ^ 2946 = 42373074 := by
        calc
          (7 : ZMod 48276289) ^ 2946 = (7 : ZMod 48276289) ^ (1473 + 1473) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 1473 * (7 : ZMod 48276289) ^ 1473 := by rw [pow_add]
          _ = 42373074 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 48276289) ^ 5893 = 32731452 := by
        calc
          (7 : ZMod 48276289) ^ 5893 = (7 : ZMod 48276289) ^ (2946 + 2946 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 2946 * (7 : ZMod 48276289) ^ 2946) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 32731452 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 48276289) ^ 11786 = 13501125 := by
        calc
          (7 : ZMod 48276289) ^ 11786 = (7 : ZMod 48276289) ^ (5893 + 5893) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 5893 * (7 : ZMod 48276289) ^ 5893 := by rw [pow_add]
          _ = 13501125 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 48276289) ^ 23572 = 19442939 := by
        calc
          (7 : ZMod 48276289) ^ 23572 = (7 : ZMod 48276289) ^ (11786 + 11786) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 11786 * (7 : ZMod 48276289) ^ 11786 := by rw [pow_add]
          _ = 19442939 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 48276289) ^ 47144 = 9732909 := by
        calc
          (7 : ZMod 48276289) ^ 47144 = (7 : ZMod 48276289) ^ (23572 + 23572) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 23572 * (7 : ZMod 48276289) ^ 23572 := by rw [pow_add]
          _ = 9732909 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 48276289) ^ 94289 = 28002805 := by
        calc
          (7 : ZMod 48276289) ^ 94289 = (7 : ZMod 48276289) ^ (47144 + 47144 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 47144 * (7 : ZMod 48276289) ^ 47144) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 28002805 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 48276289) ^ 188579 = 10192067 := by
        calc
          (7 : ZMod 48276289) ^ 188579 = (7 : ZMod 48276289) ^ (94289 + 94289 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 94289 * (7 : ZMod 48276289) ^ 94289) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 10192067 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 48276289) ^ 377158 = 14534473 := by
        calc
          (7 : ZMod 48276289) ^ 377158 = (7 : ZMod 48276289) ^ (188579 + 188579) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 188579 * (7 : ZMod 48276289) ^ 188579 := by rw [pow_add]
          _ = 14534473 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 48276289) ^ 754317 = 18963313 := by
        calc
          (7 : ZMod 48276289) ^ 754317 = (7 : ZMod 48276289) ^ (377158 + 377158 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 377158 * (7 : ZMod 48276289) ^ 377158) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 18963313 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 48276289) ^ 1508634 = 11476020 := by
        calc
          (7 : ZMod 48276289) ^ 1508634 = (7 : ZMod 48276289) ^ (754317 + 754317) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 754317 * (7 : ZMod 48276289) ^ 754317 := by rw [pow_add]
          _ = 11476020 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 48276289) ^ 3017268 = 15188597 := by
        calc
          (7 : ZMod 48276289) ^ 3017268 = (7 : ZMod 48276289) ^ (1508634 + 1508634) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 1508634 * (7 : ZMod 48276289) ^ 1508634 := by rw [pow_add]
          _ = 15188597 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 48276289) ^ 6034536 = 18002697 := by
        calc
          (7 : ZMod 48276289) ^ 6034536 = (7 : ZMod 48276289) ^ (3017268 + 3017268) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 3017268 * (7 : ZMod 48276289) ^ 3017268 := by rw [pow_add]
          _ = 18002697 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 48276289) ^ 12069072 = 26226989 := by
        calc
          (7 : ZMod 48276289) ^ 12069072 = (7 : ZMod 48276289) ^ (6034536 + 6034536) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 6034536 * (7 : ZMod 48276289) ^ 6034536 := by rw [pow_add]
          _ = 26226989 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 48276289) ^ 24138144 = 48276288 := by
        calc
          (7 : ZMod 48276289) ^ 24138144 = (7 : ZMod 48276289) ^ (12069072 + 12069072) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 12069072 * (7 : ZMod 48276289) ^ 12069072 := by rw [pow_add]
          _ = 48276288 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 48276289) ^ 48276288 = 1 := by
        calc
          (7 : ZMod 48276289) ^ 48276288 = (7 : ZMod 48276289) ^ (24138144 + 24138144) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 24138144 * (7 : ZMod 48276289) ^ 24138144 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (83813, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (83813, 1)] : List FactorBlock).map factorBlockValue).prod = 48276289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 48276289) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 48276289) ^ 2 = 49 := by
        calc
          (7 : ZMod 48276289) ^ 2 = (7 : ZMod 48276289) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 1 * (7 : ZMod 48276289) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 48276289) ^ 5 = 16807 := by
        calc
          (7 : ZMod 48276289) ^ 5 = (7 : ZMod 48276289) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 2 * (7 : ZMod 48276289) ^ 2) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 48276289) ^ 11 = 46275183 := by
        calc
          (7 : ZMod 48276289) ^ 11 = (7 : ZMod 48276289) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 5 * (7 : ZMod 48276289) ^ 5) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 46275183 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 48276289) ^ 23 = 25222848 := by
        calc
          (7 : ZMod 48276289) ^ 23 = (7 : ZMod 48276289) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 11 * (7 : ZMod 48276289) ^ 11) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 25222848 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 48276289) ^ 46 = 28174621 := by
        calc
          (7 : ZMod 48276289) ^ 46 = (7 : ZMod 48276289) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 23 * (7 : ZMod 48276289) ^ 23 := by rw [pow_add]
          _ = 28174621 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 48276289) ^ 92 = 27757347 := by
        calc
          (7 : ZMod 48276289) ^ 92 = (7 : ZMod 48276289) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 46 * (7 : ZMod 48276289) ^ 46 := by rw [pow_add]
          _ = 27757347 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 48276289) ^ 184 = 2277720 := by
        calc
          (7 : ZMod 48276289) ^ 184 = (7 : ZMod 48276289) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 92 * (7 : ZMod 48276289) ^ 92 := by rw [pow_add]
          _ = 2277720 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 48276289) ^ 368 = 45277304 := by
        calc
          (7 : ZMod 48276289) ^ 368 = (7 : ZMod 48276289) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 184 * (7 : ZMod 48276289) ^ 184 := by rw [pow_add]
          _ = 45277304 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 48276289) ^ 736 = 38389525 := by
        calc
          (7 : ZMod 48276289) ^ 736 = (7 : ZMod 48276289) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 368 * (7 : ZMod 48276289) ^ 368 := by rw [pow_add]
          _ = 38389525 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 48276289) ^ 1473 = 24320011 := by
        calc
          (7 : ZMod 48276289) ^ 1473 = (7 : ZMod 48276289) ^ (736 + 736 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 736 * (7 : ZMod 48276289) ^ 736) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 24320011 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 48276289) ^ 2946 = 42373074 := by
        calc
          (7 : ZMod 48276289) ^ 2946 = (7 : ZMod 48276289) ^ (1473 + 1473) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 1473 * (7 : ZMod 48276289) ^ 1473 := by rw [pow_add]
          _ = 42373074 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 48276289) ^ 5893 = 32731452 := by
        calc
          (7 : ZMod 48276289) ^ 5893 = (7 : ZMod 48276289) ^ (2946 + 2946 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 2946 * (7 : ZMod 48276289) ^ 2946) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 32731452 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 48276289) ^ 11786 = 13501125 := by
        calc
          (7 : ZMod 48276289) ^ 11786 = (7 : ZMod 48276289) ^ (5893 + 5893) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 5893 * (7 : ZMod 48276289) ^ 5893 := by rw [pow_add]
          _ = 13501125 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 48276289) ^ 23572 = 19442939 := by
        calc
          (7 : ZMod 48276289) ^ 23572 = (7 : ZMod 48276289) ^ (11786 + 11786) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 11786 * (7 : ZMod 48276289) ^ 11786 := by rw [pow_add]
          _ = 19442939 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 48276289) ^ 47144 = 9732909 := by
        calc
          (7 : ZMod 48276289) ^ 47144 = (7 : ZMod 48276289) ^ (23572 + 23572) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 23572 * (7 : ZMod 48276289) ^ 23572 := by rw [pow_add]
          _ = 9732909 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 48276289) ^ 94289 = 28002805 := by
        calc
          (7 : ZMod 48276289) ^ 94289 = (7 : ZMod 48276289) ^ (47144 + 47144 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 47144 * (7 : ZMod 48276289) ^ 47144) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 28002805 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 48276289) ^ 188579 = 10192067 := by
        calc
          (7 : ZMod 48276289) ^ 188579 = (7 : ZMod 48276289) ^ (94289 + 94289 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 94289 * (7 : ZMod 48276289) ^ 94289) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 10192067 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 48276289) ^ 377158 = 14534473 := by
        calc
          (7 : ZMod 48276289) ^ 377158 = (7 : ZMod 48276289) ^ (188579 + 188579) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 188579 * (7 : ZMod 48276289) ^ 188579 := by rw [pow_add]
          _ = 14534473 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 48276289) ^ 754317 = 18963313 := by
        calc
          (7 : ZMod 48276289) ^ 754317 = (7 : ZMod 48276289) ^ (377158 + 377158 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 377158 * (7 : ZMod 48276289) ^ 377158) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 18963313 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 48276289) ^ 1508634 = 11476020 := by
        calc
          (7 : ZMod 48276289) ^ 1508634 = (7 : ZMod 48276289) ^ (754317 + 754317) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 754317 * (7 : ZMod 48276289) ^ 754317 := by rw [pow_add]
          _ = 11476020 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 48276289) ^ 3017268 = 15188597 := by
        calc
          (7 : ZMod 48276289) ^ 3017268 = (7 : ZMod 48276289) ^ (1508634 + 1508634) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 1508634 * (7 : ZMod 48276289) ^ 1508634 := by rw [pow_add]
          _ = 15188597 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 48276289) ^ 6034536 = 18002697 := by
        calc
          (7 : ZMod 48276289) ^ 6034536 = (7 : ZMod 48276289) ^ (3017268 + 3017268) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 3017268 * (7 : ZMod 48276289) ^ 3017268 := by rw [pow_add]
          _ = 18002697 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 48276289) ^ 12069072 = 26226989 := by
        calc
          (7 : ZMod 48276289) ^ 12069072 = (7 : ZMod 48276289) ^ (6034536 + 6034536) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 6034536 * (7 : ZMod 48276289) ^ 6034536 := by rw [pow_add]
          _ = 26226989 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 48276289) ^ 24138144 = 48276288 := by
        calc
          (7 : ZMod 48276289) ^ 24138144 = (7 : ZMod 48276289) ^ (12069072 + 12069072) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 12069072 * (7 : ZMod 48276289) ^ 12069072 := by rw [pow_add]
          _ = 48276288 := by rw [factor_0_23]; decide
      change (7 : ZMod 48276289) ^ 24138144 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (7 : ZMod 48276289) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 48276289) ^ 3 = 343 := by
        calc
          (7 : ZMod 48276289) ^ 3 = (7 : ZMod 48276289) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 1 * (7 : ZMod 48276289) ^ 1) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 48276289) ^ 7 = 823543 := by
        calc
          (7 : ZMod 48276289) ^ 7 = (7 : ZMod 48276289) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 3 * (7 : ZMod 48276289) ^ 3) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 48276289) ^ 15 = 22973394 := by
        calc
          (7 : ZMod 48276289) ^ 15 = (7 : ZMod 48276289) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 7 * (7 : ZMod 48276289) ^ 7) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 22973394 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 48276289) ^ 30 = 19660989 := by
        calc
          (7 : ZMod 48276289) ^ 30 = (7 : ZMod 48276289) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 15 * (7 : ZMod 48276289) ^ 15 := by rw [pow_add]
          _ = 19660989 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 48276289) ^ 61 = 7004302 := by
        calc
          (7 : ZMod 48276289) ^ 61 = (7 : ZMod 48276289) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 30 * (7 : ZMod 48276289) ^ 30) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 7004302 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 48276289) ^ 122 = 47126422 := by
        calc
          (7 : ZMod 48276289) ^ 122 = (7 : ZMod 48276289) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 61 * (7 : ZMod 48276289) ^ 61 := by rw [pow_add]
          _ = 47126422 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 48276289) ^ 245 = 21801899 := by
        calc
          (7 : ZMod 48276289) ^ 245 = (7 : ZMod 48276289) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 122 * (7 : ZMod 48276289) ^ 122) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 21801899 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 48276289) ^ 491 = 23721763 := by
        calc
          (7 : ZMod 48276289) ^ 491 = (7 : ZMod 48276289) ^ (245 + 245 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 245 * (7 : ZMod 48276289) ^ 245) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 23721763 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 48276289) ^ 982 = 1330671 := by
        calc
          (7 : ZMod 48276289) ^ 982 = (7 : ZMod 48276289) ^ (491 + 491) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 491 * (7 : ZMod 48276289) ^ 491 := by rw [pow_add]
          _ = 1330671 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 48276289) ^ 1964 = 7582299 := by
        calc
          (7 : ZMod 48276289) ^ 1964 = (7 : ZMod 48276289) ^ (982 + 982) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 982 * (7 : ZMod 48276289) ^ 982 := by rw [pow_add]
          _ = 7582299 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 48276289) ^ 3928 = 39357370 := by
        calc
          (7 : ZMod 48276289) ^ 3928 = (7 : ZMod 48276289) ^ (1964 + 1964) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 1964 * (7 : ZMod 48276289) ^ 1964 := by rw [pow_add]
          _ = 39357370 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 48276289) ^ 7857 = 40303746 := by
        calc
          (7 : ZMod 48276289) ^ 7857 = (7 : ZMod 48276289) ^ (3928 + 3928 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 3928 * (7 : ZMod 48276289) ^ 3928) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 40303746 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 48276289) ^ 15714 = 10816247 := by
        calc
          (7 : ZMod 48276289) ^ 15714 = (7 : ZMod 48276289) ^ (7857 + 7857) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 7857 * (7 : ZMod 48276289) ^ 7857 := by rw [pow_add]
          _ = 10816247 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 48276289) ^ 31429 = 41534466 := by
        calc
          (7 : ZMod 48276289) ^ 31429 = (7 : ZMod 48276289) ^ (15714 + 15714 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 15714 * (7 : ZMod 48276289) ^ 15714) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 41534466 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 48276289) ^ 62859 = 20954780 := by
        calc
          (7 : ZMod 48276289) ^ 62859 = (7 : ZMod 48276289) ^ (31429 + 31429 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 31429 * (7 : ZMod 48276289) ^ 31429) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 20954780 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 48276289) ^ 125719 = 30830673 := by
        calc
          (7 : ZMod 48276289) ^ 125719 = (7 : ZMod 48276289) ^ (62859 + 62859 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 62859 * (7 : ZMod 48276289) ^ 62859) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 30830673 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 48276289) ^ 251439 = 37918671 := by
        calc
          (7 : ZMod 48276289) ^ 251439 = (7 : ZMod 48276289) ^ (125719 + 125719 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 125719 * (7 : ZMod 48276289) ^ 125719) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 37918671 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 48276289) ^ 502878 = 5350078 := by
        calc
          (7 : ZMod 48276289) ^ 502878 = (7 : ZMod 48276289) ^ (251439 + 251439) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 251439 * (7 : ZMod 48276289) ^ 251439 := by rw [pow_add]
          _ = 5350078 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 48276289) ^ 1005756 = 33200250 := by
        calc
          (7 : ZMod 48276289) ^ 1005756 = (7 : ZMod 48276289) ^ (502878 + 502878) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 502878 * (7 : ZMod 48276289) ^ 502878 := by rw [pow_add]
          _ = 33200250 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 48276289) ^ 2011512 = 10884516 := by
        calc
          (7 : ZMod 48276289) ^ 2011512 = (7 : ZMod 48276289) ^ (1005756 + 1005756) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 1005756 * (7 : ZMod 48276289) ^ 1005756 := by rw [pow_add]
          _ = 10884516 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 48276289) ^ 4023024 = 20152361 := by
        calc
          (7 : ZMod 48276289) ^ 4023024 = (7 : ZMod 48276289) ^ (2011512 + 2011512) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 2011512 * (7 : ZMod 48276289) ^ 2011512 := by rw [pow_add]
          _ = 20152361 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 48276289) ^ 8046048 = 34789703 := by
        calc
          (7 : ZMod 48276289) ^ 8046048 = (7 : ZMod 48276289) ^ (4023024 + 4023024) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 4023024 * (7 : ZMod 48276289) ^ 4023024 := by rw [pow_add]
          _ = 34789703 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 48276289) ^ 16092096 = 34789702 := by
        calc
          (7 : ZMod 48276289) ^ 16092096 = (7 : ZMod 48276289) ^ (8046048 + 8046048) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 8046048 * (7 : ZMod 48276289) ^ 8046048 := by rw [pow_add]
          _ = 34789702 := by rw [factor_1_22]; decide
      change (7 : ZMod 48276289) ^ 16092096 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (7 : ZMod 48276289) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 48276289) ^ 2 = 49 := by
        calc
          (7 : ZMod 48276289) ^ 2 = (7 : ZMod 48276289) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 1 * (7 : ZMod 48276289) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 48276289) ^ 4 = 2401 := by
        calc
          (7 : ZMod 48276289) ^ 4 = (7 : ZMod 48276289) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 2 * (7 : ZMod 48276289) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 48276289) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 48276289) ^ 9 = (7 : ZMod 48276289) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = ((7 : ZMod 48276289) ^ 4 * (7 : ZMod 48276289) ^ 4) * (7 : ZMod 48276289) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 48276289) ^ 18 = 10839035 := by
        calc
          (7 : ZMod 48276289) ^ 18 = (7 : ZMod 48276289) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 9 * (7 : ZMod 48276289) ^ 9 := by rw [pow_add]
          _ = 10839035 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 48276289) ^ 36 = 33860004 := by
        calc
          (7 : ZMod 48276289) ^ 36 = (7 : ZMod 48276289) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 18 * (7 : ZMod 48276289) ^ 18 := by rw [pow_add]
          _ = 33860004 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 48276289) ^ 72 = 42161381 := by
        calc
          (7 : ZMod 48276289) ^ 72 = (7 : ZMod 48276289) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 36 * (7 : ZMod 48276289) ^ 36 := by rw [pow_add]
          _ = 42161381 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 48276289) ^ 144 = 38137537 := by
        calc
          (7 : ZMod 48276289) ^ 144 = (7 : ZMod 48276289) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 72 * (7 : ZMod 48276289) ^ 72 := by rw [pow_add]
          _ = 38137537 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 48276289) ^ 288 = 24436405 := by
        calc
          (7 : ZMod 48276289) ^ 288 = (7 : ZMod 48276289) ^ (144 + 144) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 144 * (7 : ZMod 48276289) ^ 144 := by rw [pow_add]
          _ = 24436405 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 48276289) ^ 576 = 22332450 := by
        calc
          (7 : ZMod 48276289) ^ 576 = (7 : ZMod 48276289) ^ (288 + 288) :=
            congrArg (fun n : ℕ => (7 : ZMod 48276289) ^ n) (by norm_num)
          _ = (7 : ZMod 48276289) ^ 288 * (7 : ZMod 48276289) ^ 288 := by rw [pow_add]
          _ = 22332450 := by rw [factor_2_8]; decide
      change (7 : ZMod 48276289) ^ 576 ≠ 1
      rw [factor_2_9]
      decide

#print axioms prime_lucas_48276289

end TotientTailPeriodKiller
end Erdos249257
