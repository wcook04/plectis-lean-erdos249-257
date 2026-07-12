import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_43913777 : Nat.Prime 43913777 := by
  apply lucas_primality 43913777 (3 : ZMod 43913777)
  ·
      have fermat_0 : (3 : ZMod 43913777) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 43913777) ^ 2 = 9 := by
        calc
          (3 : ZMod 43913777) ^ 2 = (3 : ZMod 43913777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 1 * (3 : ZMod 43913777) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 43913777) ^ 5 = 243 := by
        calc
          (3 : ZMod 43913777) ^ 5 = (3 : ZMod 43913777) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 2 * (3 : ZMod 43913777) ^ 2) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 43913777) ^ 10 = 59049 := by
        calc
          (3 : ZMod 43913777) ^ 10 = (3 : ZMod 43913777) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 5 * (3 : ZMod 43913777) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 43913777) ^ 20 = 17596018 := by
        calc
          (3 : ZMod 43913777) ^ 20 = (3 : ZMod 43913777) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 10 * (3 : ZMod 43913777) ^ 10 := by rw [pow_add]
          _ = 17596018 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 43913777) ^ 41 = 36039111 := by
        calc
          (3 : ZMod 43913777) ^ 41 = (3 : ZMod 43913777) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 20 * (3 : ZMod 43913777) ^ 20) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 36039111 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 43913777) ^ 83 = 38605108 := by
        calc
          (3 : ZMod 43913777) ^ 83 = (3 : ZMod 43913777) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 41 * (3 : ZMod 43913777) ^ 41) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 38605108 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 43913777) ^ 167 = 22209893 := by
        calc
          (3 : ZMod 43913777) ^ 167 = (3 : ZMod 43913777) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 83 * (3 : ZMod 43913777) ^ 83) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 22209893 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 43913777) ^ 335 = 9862684 := by
        calc
          (3 : ZMod 43913777) ^ 335 = (3 : ZMod 43913777) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 167 * (3 : ZMod 43913777) ^ 167) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 9862684 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 43913777) ^ 670 = 6526696 := by
        calc
          (3 : ZMod 43913777) ^ 670 = (3 : ZMod 43913777) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 335 * (3 : ZMod 43913777) ^ 335 := by rw [pow_add]
          _ = 6526696 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 43913777) ^ 1340 = 35659329 := by
        calc
          (3 : ZMod 43913777) ^ 1340 = (3 : ZMod 43913777) ^ (670 + 670) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 670 * (3 : ZMod 43913777) ^ 670 := by rw [pow_add]
          _ = 35659329 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 43913777) ^ 2680 = 41925713 := by
        calc
          (3 : ZMod 43913777) ^ 2680 = (3 : ZMod 43913777) ^ (1340 + 1340) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 1340 * (3 : ZMod 43913777) ^ 1340 := by rw [pow_add]
          _ = 41925713 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 43913777) ^ 5360 = 26796765 := by
        calc
          (3 : ZMod 43913777) ^ 5360 = (3 : ZMod 43913777) ^ (2680 + 2680) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 2680 * (3 : ZMod 43913777) ^ 2680 := by rw [pow_add]
          _ = 26796765 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 43913777) ^ 10721 = 27284843 := by
        calc
          (3 : ZMod 43913777) ^ 10721 = (3 : ZMod 43913777) ^ (5360 + 5360 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 5360 * (3 : ZMod 43913777) ^ 5360) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 27284843 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 43913777) ^ 21442 = 37050847 := by
        calc
          (3 : ZMod 43913777) ^ 21442 = (3 : ZMod 43913777) ^ (10721 + 10721) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 10721 * (3 : ZMod 43913777) ^ 10721 := by rw [pow_add]
          _ = 37050847 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 43913777) ^ 42884 = 42749773 := by
        calc
          (3 : ZMod 43913777) ^ 42884 = (3 : ZMod 43913777) ^ (21442 + 21442) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 21442 * (3 : ZMod 43913777) ^ 21442 := by rw [pow_add]
          _ = 42749773 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 43913777) ^ 85769 = 12823151 := by
        calc
          (3 : ZMod 43913777) ^ 85769 = (3 : ZMod 43913777) ^ (42884 + 42884 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 42884 * (3 : ZMod 43913777) ^ 42884) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 12823151 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 43913777) ^ 171538 = 39712266 := by
        calc
          (3 : ZMod 43913777) ^ 171538 = (3 : ZMod 43913777) ^ (85769 + 85769) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 85769 * (3 : ZMod 43913777) ^ 85769 := by rw [pow_add]
          _ = 39712266 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 43913777) ^ 343076 = 15035776 := by
        calc
          (3 : ZMod 43913777) ^ 343076 = (3 : ZMod 43913777) ^ (171538 + 171538) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 171538 * (3 : ZMod 43913777) ^ 171538 := by rw [pow_add]
          _ = 15035776 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 43913777) ^ 686152 = 24514734 := by
        calc
          (3 : ZMod 43913777) ^ 686152 = (3 : ZMod 43913777) ^ (343076 + 343076) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 343076 * (3 : ZMod 43913777) ^ 343076 := by rw [pow_add]
          _ = 24514734 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 43913777) ^ 1372305 = 30016135 := by
        calc
          (3 : ZMod 43913777) ^ 1372305 = (3 : ZMod 43913777) ^ (686152 + 686152 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 686152 * (3 : ZMod 43913777) ^ 686152) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 30016135 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 43913777) ^ 2744611 = 30376000 := by
        calc
          (3 : ZMod 43913777) ^ 2744611 = (3 : ZMod 43913777) ^ (1372305 + 1372305 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 1372305 * (3 : ZMod 43913777) ^ 1372305) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 30376000 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 43913777) ^ 5489222 = 24360180 := by
        calc
          (3 : ZMod 43913777) ^ 5489222 = (3 : ZMod 43913777) ^ (2744611 + 2744611) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 2744611 * (3 : ZMod 43913777) ^ 2744611 := by rw [pow_add]
          _ = 24360180 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 43913777) ^ 10978444 = 39535603 := by
        calc
          (3 : ZMod 43913777) ^ 10978444 = (3 : ZMod 43913777) ^ (5489222 + 5489222) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 5489222 * (3 : ZMod 43913777) ^ 5489222 := by rw [pow_add]
          _ = 39535603 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 43913777) ^ 21956888 = 43913776 := by
        calc
          (3 : ZMod 43913777) ^ 21956888 = (3 : ZMod 43913777) ^ (10978444 + 10978444) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 10978444 * (3 : ZMod 43913777) ^ 10978444 := by rw [pow_add]
          _ = 43913776 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 43913777) ^ 43913776 = 1 := by
        calc
          (3 : ZMod 43913777) ^ 43913776 = (3 : ZMod 43913777) ^ (21956888 + 21956888) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 21956888 * (3 : ZMod 43913777) ^ 21956888 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (2744611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (2744611, 1)] : List FactorBlock).map factorBlockValue).prod = 43913777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 43913777) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 43913777) ^ 2 = 9 := by
        calc
          (3 : ZMod 43913777) ^ 2 = (3 : ZMod 43913777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 1 * (3 : ZMod 43913777) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 43913777) ^ 5 = 243 := by
        calc
          (3 : ZMod 43913777) ^ 5 = (3 : ZMod 43913777) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 2 * (3 : ZMod 43913777) ^ 2) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 43913777) ^ 10 = 59049 := by
        calc
          (3 : ZMod 43913777) ^ 10 = (3 : ZMod 43913777) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 5 * (3 : ZMod 43913777) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 43913777) ^ 20 = 17596018 := by
        calc
          (3 : ZMod 43913777) ^ 20 = (3 : ZMod 43913777) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 10 * (3 : ZMod 43913777) ^ 10 := by rw [pow_add]
          _ = 17596018 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 43913777) ^ 41 = 36039111 := by
        calc
          (3 : ZMod 43913777) ^ 41 = (3 : ZMod 43913777) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 20 * (3 : ZMod 43913777) ^ 20) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 36039111 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 43913777) ^ 83 = 38605108 := by
        calc
          (3 : ZMod 43913777) ^ 83 = (3 : ZMod 43913777) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 41 * (3 : ZMod 43913777) ^ 41) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 38605108 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 43913777) ^ 167 = 22209893 := by
        calc
          (3 : ZMod 43913777) ^ 167 = (3 : ZMod 43913777) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 83 * (3 : ZMod 43913777) ^ 83) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 22209893 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 43913777) ^ 335 = 9862684 := by
        calc
          (3 : ZMod 43913777) ^ 335 = (3 : ZMod 43913777) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 167 * (3 : ZMod 43913777) ^ 167) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 9862684 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 43913777) ^ 670 = 6526696 := by
        calc
          (3 : ZMod 43913777) ^ 670 = (3 : ZMod 43913777) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 335 * (3 : ZMod 43913777) ^ 335 := by rw [pow_add]
          _ = 6526696 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 43913777) ^ 1340 = 35659329 := by
        calc
          (3 : ZMod 43913777) ^ 1340 = (3 : ZMod 43913777) ^ (670 + 670) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 670 * (3 : ZMod 43913777) ^ 670 := by rw [pow_add]
          _ = 35659329 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 43913777) ^ 2680 = 41925713 := by
        calc
          (3 : ZMod 43913777) ^ 2680 = (3 : ZMod 43913777) ^ (1340 + 1340) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 1340 * (3 : ZMod 43913777) ^ 1340 := by rw [pow_add]
          _ = 41925713 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 43913777) ^ 5360 = 26796765 := by
        calc
          (3 : ZMod 43913777) ^ 5360 = (3 : ZMod 43913777) ^ (2680 + 2680) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 2680 * (3 : ZMod 43913777) ^ 2680 := by rw [pow_add]
          _ = 26796765 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 43913777) ^ 10721 = 27284843 := by
        calc
          (3 : ZMod 43913777) ^ 10721 = (3 : ZMod 43913777) ^ (5360 + 5360 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 5360 * (3 : ZMod 43913777) ^ 5360) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 27284843 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 43913777) ^ 21442 = 37050847 := by
        calc
          (3 : ZMod 43913777) ^ 21442 = (3 : ZMod 43913777) ^ (10721 + 10721) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 10721 * (3 : ZMod 43913777) ^ 10721 := by rw [pow_add]
          _ = 37050847 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 43913777) ^ 42884 = 42749773 := by
        calc
          (3 : ZMod 43913777) ^ 42884 = (3 : ZMod 43913777) ^ (21442 + 21442) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 21442 * (3 : ZMod 43913777) ^ 21442 := by rw [pow_add]
          _ = 42749773 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 43913777) ^ 85769 = 12823151 := by
        calc
          (3 : ZMod 43913777) ^ 85769 = (3 : ZMod 43913777) ^ (42884 + 42884 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 42884 * (3 : ZMod 43913777) ^ 42884) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 12823151 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 43913777) ^ 171538 = 39712266 := by
        calc
          (3 : ZMod 43913777) ^ 171538 = (3 : ZMod 43913777) ^ (85769 + 85769) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 85769 * (3 : ZMod 43913777) ^ 85769 := by rw [pow_add]
          _ = 39712266 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 43913777) ^ 343076 = 15035776 := by
        calc
          (3 : ZMod 43913777) ^ 343076 = (3 : ZMod 43913777) ^ (171538 + 171538) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 171538 * (3 : ZMod 43913777) ^ 171538 := by rw [pow_add]
          _ = 15035776 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 43913777) ^ 686152 = 24514734 := by
        calc
          (3 : ZMod 43913777) ^ 686152 = (3 : ZMod 43913777) ^ (343076 + 343076) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 343076 * (3 : ZMod 43913777) ^ 343076 := by rw [pow_add]
          _ = 24514734 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 43913777) ^ 1372305 = 30016135 := by
        calc
          (3 : ZMod 43913777) ^ 1372305 = (3 : ZMod 43913777) ^ (686152 + 686152 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 686152 * (3 : ZMod 43913777) ^ 686152) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 30016135 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 43913777) ^ 2744611 = 30376000 := by
        calc
          (3 : ZMod 43913777) ^ 2744611 = (3 : ZMod 43913777) ^ (1372305 + 1372305 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = ((3 : ZMod 43913777) ^ 1372305 * (3 : ZMod 43913777) ^ 1372305) * (3 : ZMod 43913777) := by rw [pow_succ, pow_add]
          _ = 30376000 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 43913777) ^ 5489222 = 24360180 := by
        calc
          (3 : ZMod 43913777) ^ 5489222 = (3 : ZMod 43913777) ^ (2744611 + 2744611) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 2744611 * (3 : ZMod 43913777) ^ 2744611 := by rw [pow_add]
          _ = 24360180 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 43913777) ^ 10978444 = 39535603 := by
        calc
          (3 : ZMod 43913777) ^ 10978444 = (3 : ZMod 43913777) ^ (5489222 + 5489222) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 5489222 * (3 : ZMod 43913777) ^ 5489222 := by rw [pow_add]
          _ = 39535603 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 43913777) ^ 21956888 = 43913776 := by
        calc
          (3 : ZMod 43913777) ^ 21956888 = (3 : ZMod 43913777) ^ (10978444 + 10978444) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 10978444 * (3 : ZMod 43913777) ^ 10978444 := by rw [pow_add]
          _ = 43913776 := by rw [factor_0_23]; decide
      change (3 : ZMod 43913777) ^ 21956888 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (3 : ZMod 43913777) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 43913777) ^ 2 = 9 := by
        calc
          (3 : ZMod 43913777) ^ 2 = (3 : ZMod 43913777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 1 * (3 : ZMod 43913777) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 43913777) ^ 4 = 81 := by
        calc
          (3 : ZMod 43913777) ^ 4 = (3 : ZMod 43913777) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 2 * (3 : ZMod 43913777) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 43913777) ^ 8 = 6561 := by
        calc
          (3 : ZMod 43913777) ^ 8 = (3 : ZMod 43913777) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 4 * (3 : ZMod 43913777) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 43913777) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 43913777) ^ 16 = (3 : ZMod 43913777) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 43913777) ^ n) (by norm_num)
          _ = (3 : ZMod 43913777) ^ 8 * (3 : ZMod 43913777) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_1_3]; decide
      change (3 : ZMod 43913777) ^ 16 ≠ 1
      rw [factor_1_4]
      decide

#print axioms prime_lucas_43913777

end TotientTailPeriodKiller
end Erdos249257
