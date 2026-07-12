import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1361244631 : Nat.Prime 1361244631 := by
  apply lucas_primality 1361244631 (12 : ZMod 1361244631)
  ·
      have fermat_0 : (12 : ZMod 1361244631) ^ 1 = 12 := by norm_num
      have fermat_1 : (12 : ZMod 1361244631) ^ 2 = 144 := by
        calc
          (12 : ZMod 1361244631) ^ 2 = (12 : ZMod 1361244631) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1 * (12 : ZMod 1361244631) ^ 1 := by rw [pow_add]
          _ = 144 := by rw [fermat_0]; decide
      have fermat_2 : (12 : ZMod 1361244631) ^ 5 = 248832 := by
        calc
          (12 : ZMod 1361244631) ^ 5 = (12 : ZMod 1361244631) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 2 * (12 : ZMod 1361244631) ^ 2) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 248832 := by rw [fermat_1]; decide
      have fermat_3 : (12 : ZMod 1361244631) ^ 10 = 661355829 := by
        calc
          (12 : ZMod 1361244631) ^ 10 = (12 : ZMod 1361244631) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 5 * (12 : ZMod 1361244631) ^ 5 := by rw [pow_add]
          _ = 661355829 := by rw [fermat_2]; decide
      have fermat_4 : (12 : ZMod 1361244631) ^ 20 = 43938450 := by
        calc
          (12 : ZMod 1361244631) ^ 20 = (12 : ZMod 1361244631) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 10 * (12 : ZMod 1361244631) ^ 10 := by rw [pow_add]
          _ = 43938450 := by rw [fermat_3]; decide
      have fermat_5 : (12 : ZMod 1361244631) ^ 40 = 829242119 := by
        calc
          (12 : ZMod 1361244631) ^ 40 = (12 : ZMod 1361244631) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 20 * (12 : ZMod 1361244631) ^ 20 := by rw [pow_add]
          _ = 829242119 := by rw [fermat_4]; decide
      have fermat_6 : (12 : ZMod 1361244631) ^ 81 = 1169771356 := by
        calc
          (12 : ZMod 1361244631) ^ 81 = (12 : ZMod 1361244631) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 40 * (12 : ZMod 1361244631) ^ 40) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1169771356 := by rw [fermat_5]; decide
      have fermat_7 : (12 : ZMod 1361244631) ^ 162 = 1347222460 := by
        calc
          (12 : ZMod 1361244631) ^ 162 = (12 : ZMod 1361244631) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 81 * (12 : ZMod 1361244631) ^ 81 := by rw [pow_add]
          _ = 1347222460 := by rw [fermat_6]; decide
      have fermat_8 : (12 : ZMod 1361244631) ^ 324 = 382562339 := by
        calc
          (12 : ZMod 1361244631) ^ 324 = (12 : ZMod 1361244631) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 162 * (12 : ZMod 1361244631) ^ 162 := by rw [pow_add]
          _ = 382562339 := by rw [fermat_7]; decide
      have fermat_9 : (12 : ZMod 1361244631) ^ 649 = 1229791762 := by
        calc
          (12 : ZMod 1361244631) ^ 649 = (12 : ZMod 1361244631) ^ (324 + 324 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 324 * (12 : ZMod 1361244631) ^ 324) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1229791762 := by rw [fermat_8]; decide
      have fermat_10 : (12 : ZMod 1361244631) ^ 1298 = 984520832 := by
        calc
          (12 : ZMod 1361244631) ^ 1298 = (12 : ZMod 1361244631) ^ (649 + 649) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 649 * (12 : ZMod 1361244631) ^ 649 := by rw [pow_add]
          _ = 984520832 := by rw [fermat_9]; decide
      have fermat_11 : (12 : ZMod 1361244631) ^ 2596 = 1032392371 := by
        calc
          (12 : ZMod 1361244631) ^ 2596 = (12 : ZMod 1361244631) ^ (1298 + 1298) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1298 * (12 : ZMod 1361244631) ^ 1298 := by rw [pow_add]
          _ = 1032392371 := by rw [fermat_10]; decide
      have fermat_12 : (12 : ZMod 1361244631) ^ 5192 = 84994169 := by
        calc
          (12 : ZMod 1361244631) ^ 5192 = (12 : ZMod 1361244631) ^ (2596 + 2596) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 2596 * (12 : ZMod 1361244631) ^ 2596 := by rw [pow_add]
          _ = 84994169 := by rw [fermat_11]; decide
      have fermat_13 : (12 : ZMod 1361244631) ^ 10385 = 85638769 := by
        calc
          (12 : ZMod 1361244631) ^ 10385 = (12 : ZMod 1361244631) ^ (5192 + 5192 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 5192 * (12 : ZMod 1361244631) ^ 5192) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 85638769 := by rw [fermat_12]; decide
      have fermat_14 : (12 : ZMod 1361244631) ^ 20770 = 638727196 := by
        calc
          (12 : ZMod 1361244631) ^ 20770 = (12 : ZMod 1361244631) ^ (10385 + 10385) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 10385 * (12 : ZMod 1361244631) ^ 10385 := by rw [pow_add]
          _ = 638727196 := by rw [fermat_13]; decide
      have fermat_15 : (12 : ZMod 1361244631) ^ 41541 = 875319046 := by
        calc
          (12 : ZMod 1361244631) ^ 41541 = (12 : ZMod 1361244631) ^ (20770 + 20770 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 20770 * (12 : ZMod 1361244631) ^ 20770) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 875319046 := by rw [fermat_14]; decide
      have fermat_16 : (12 : ZMod 1361244631) ^ 83083 = 1088934249 := by
        calc
          (12 : ZMod 1361244631) ^ 83083 = (12 : ZMod 1361244631) ^ (41541 + 41541 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 41541 * (12 : ZMod 1361244631) ^ 41541) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1088934249 := by rw [fermat_15]; decide
      have fermat_17 : (12 : ZMod 1361244631) ^ 166167 = 19562924 := by
        calc
          (12 : ZMod 1361244631) ^ 166167 = (12 : ZMod 1361244631) ^ (83083 + 83083 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 83083 * (12 : ZMod 1361244631) ^ 83083) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 19562924 := by rw [fermat_16]; decide
      have fermat_18 : (12 : ZMod 1361244631) ^ 332335 = 955054955 := by
        calc
          (12 : ZMod 1361244631) ^ 332335 = (12 : ZMod 1361244631) ^ (166167 + 166167 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 166167 * (12 : ZMod 1361244631) ^ 166167) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 955054955 := by rw [fermat_17]; decide
      have fermat_19 : (12 : ZMod 1361244631) ^ 664670 = 1266442355 := by
        calc
          (12 : ZMod 1361244631) ^ 664670 = (12 : ZMod 1361244631) ^ (332335 + 332335) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 332335 * (12 : ZMod 1361244631) ^ 332335 := by rw [pow_add]
          _ = 1266442355 := by rw [fermat_18]; decide
      have fermat_20 : (12 : ZMod 1361244631) ^ 1329340 = 873022824 := by
        calc
          (12 : ZMod 1361244631) ^ 1329340 = (12 : ZMod 1361244631) ^ (664670 + 664670) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 664670 * (12 : ZMod 1361244631) ^ 664670 := by rw [pow_add]
          _ = 873022824 := by rw [fermat_19]; decide
      have fermat_21 : (12 : ZMod 1361244631) ^ 2658680 = 1350763423 := by
        calc
          (12 : ZMod 1361244631) ^ 2658680 = (12 : ZMod 1361244631) ^ (1329340 + 1329340) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1329340 * (12 : ZMod 1361244631) ^ 1329340 := by rw [pow_add]
          _ = 1350763423 := by rw [fermat_20]; decide
      have fermat_22 : (12 : ZMod 1361244631) ^ 5317361 = 1238161100 := by
        calc
          (12 : ZMod 1361244631) ^ 5317361 = (12 : ZMod 1361244631) ^ (2658680 + 2658680 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 2658680 * (12 : ZMod 1361244631) ^ 2658680) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1238161100 := by rw [fermat_21]; decide
      have fermat_23 : (12 : ZMod 1361244631) ^ 10634723 = 282846564 := by
        calc
          (12 : ZMod 1361244631) ^ 10634723 = (12 : ZMod 1361244631) ^ (5317361 + 5317361 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 5317361 * (12 : ZMod 1361244631) ^ 5317361) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 282846564 := by rw [fermat_22]; decide
      have fermat_24 : (12 : ZMod 1361244631) ^ 21269447 = 254531764 := by
        calc
          (12 : ZMod 1361244631) ^ 21269447 = (12 : ZMod 1361244631) ^ (10634723 + 10634723 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 10634723 * (12 : ZMod 1361244631) ^ 10634723) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 254531764 := by rw [fermat_23]; decide
      have fermat_25 : (12 : ZMod 1361244631) ^ 42538894 = 759539100 := by
        calc
          (12 : ZMod 1361244631) ^ 42538894 = (12 : ZMod 1361244631) ^ (21269447 + 21269447) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 21269447 * (12 : ZMod 1361244631) ^ 21269447 := by rw [pow_add]
          _ = 759539100 := by rw [fermat_24]; decide
      have fermat_26 : (12 : ZMod 1361244631) ^ 85077789 = 1101973702 := by
        calc
          (12 : ZMod 1361244631) ^ 85077789 = (12 : ZMod 1361244631) ^ (42538894 + 42538894 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 42538894 * (12 : ZMod 1361244631) ^ 42538894) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1101973702 := by rw [fermat_25]; decide
      have fermat_27 : (12 : ZMod 1361244631) ^ 170155578 = 741933014 := by
        calc
          (12 : ZMod 1361244631) ^ 170155578 = (12 : ZMod 1361244631) ^ (85077789 + 85077789) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 85077789 * (12 : ZMod 1361244631) ^ 85077789 := by rw [pow_add]
          _ = 741933014 := by rw [fermat_26]; decide
      have fermat_28 : (12 : ZMod 1361244631) ^ 340311157 = 291051811 := by
        calc
          (12 : ZMod 1361244631) ^ 340311157 = (12 : ZMod 1361244631) ^ (170155578 + 170155578 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 170155578 * (12 : ZMod 1361244631) ^ 170155578) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 291051811 := by rw [fermat_27]; decide
      have fermat_29 : (12 : ZMod 1361244631) ^ 680622315 = 1361244630 := by
        calc
          (12 : ZMod 1361244631) ^ 680622315 = (12 : ZMod 1361244631) ^ (340311157 + 340311157 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 340311157 * (12 : ZMod 1361244631) ^ 340311157) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1361244630 := by rw [fermat_28]; decide
      have fermat_30 : (12 : ZMod 1361244631) ^ 1361244630 = 1 := by
        calc
          (12 : ZMod 1361244631) ^ 1361244630 = (12 : ZMod 1361244631) ^ (680622315 + 680622315) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 680622315 * (12 : ZMod 1361244631) ^ 680622315 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (29, 1), (149, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (29, 1), (149, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod = 1361244631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (12 : ZMod 1361244631) ^ 1 = 12 := by norm_num
      have factor_0_1 : (12 : ZMod 1361244631) ^ 2 = 144 := by
        calc
          (12 : ZMod 1361244631) ^ 2 = (12 : ZMod 1361244631) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1 * (12 : ZMod 1361244631) ^ 1 := by rw [pow_add]
          _ = 144 := by rw [factor_0_0]; decide
      have factor_0_2 : (12 : ZMod 1361244631) ^ 5 = 248832 := by
        calc
          (12 : ZMod 1361244631) ^ 5 = (12 : ZMod 1361244631) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 2 * (12 : ZMod 1361244631) ^ 2) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 248832 := by rw [factor_0_1]; decide
      have factor_0_3 : (12 : ZMod 1361244631) ^ 10 = 661355829 := by
        calc
          (12 : ZMod 1361244631) ^ 10 = (12 : ZMod 1361244631) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 5 * (12 : ZMod 1361244631) ^ 5 := by rw [pow_add]
          _ = 661355829 := by rw [factor_0_2]; decide
      have factor_0_4 : (12 : ZMod 1361244631) ^ 20 = 43938450 := by
        calc
          (12 : ZMod 1361244631) ^ 20 = (12 : ZMod 1361244631) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 10 * (12 : ZMod 1361244631) ^ 10 := by rw [pow_add]
          _ = 43938450 := by rw [factor_0_3]; decide
      have factor_0_5 : (12 : ZMod 1361244631) ^ 40 = 829242119 := by
        calc
          (12 : ZMod 1361244631) ^ 40 = (12 : ZMod 1361244631) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 20 * (12 : ZMod 1361244631) ^ 20 := by rw [pow_add]
          _ = 829242119 := by rw [factor_0_4]; decide
      have factor_0_6 : (12 : ZMod 1361244631) ^ 81 = 1169771356 := by
        calc
          (12 : ZMod 1361244631) ^ 81 = (12 : ZMod 1361244631) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 40 * (12 : ZMod 1361244631) ^ 40) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1169771356 := by rw [factor_0_5]; decide
      have factor_0_7 : (12 : ZMod 1361244631) ^ 162 = 1347222460 := by
        calc
          (12 : ZMod 1361244631) ^ 162 = (12 : ZMod 1361244631) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 81 * (12 : ZMod 1361244631) ^ 81 := by rw [pow_add]
          _ = 1347222460 := by rw [factor_0_6]; decide
      have factor_0_8 : (12 : ZMod 1361244631) ^ 324 = 382562339 := by
        calc
          (12 : ZMod 1361244631) ^ 324 = (12 : ZMod 1361244631) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 162 * (12 : ZMod 1361244631) ^ 162 := by rw [pow_add]
          _ = 382562339 := by rw [factor_0_7]; decide
      have factor_0_9 : (12 : ZMod 1361244631) ^ 649 = 1229791762 := by
        calc
          (12 : ZMod 1361244631) ^ 649 = (12 : ZMod 1361244631) ^ (324 + 324 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 324 * (12 : ZMod 1361244631) ^ 324) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1229791762 := by rw [factor_0_8]; decide
      have factor_0_10 : (12 : ZMod 1361244631) ^ 1298 = 984520832 := by
        calc
          (12 : ZMod 1361244631) ^ 1298 = (12 : ZMod 1361244631) ^ (649 + 649) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 649 * (12 : ZMod 1361244631) ^ 649 := by rw [pow_add]
          _ = 984520832 := by rw [factor_0_9]; decide
      have factor_0_11 : (12 : ZMod 1361244631) ^ 2596 = 1032392371 := by
        calc
          (12 : ZMod 1361244631) ^ 2596 = (12 : ZMod 1361244631) ^ (1298 + 1298) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1298 * (12 : ZMod 1361244631) ^ 1298 := by rw [pow_add]
          _ = 1032392371 := by rw [factor_0_10]; decide
      have factor_0_12 : (12 : ZMod 1361244631) ^ 5192 = 84994169 := by
        calc
          (12 : ZMod 1361244631) ^ 5192 = (12 : ZMod 1361244631) ^ (2596 + 2596) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 2596 * (12 : ZMod 1361244631) ^ 2596 := by rw [pow_add]
          _ = 84994169 := by rw [factor_0_11]; decide
      have factor_0_13 : (12 : ZMod 1361244631) ^ 10385 = 85638769 := by
        calc
          (12 : ZMod 1361244631) ^ 10385 = (12 : ZMod 1361244631) ^ (5192 + 5192 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 5192 * (12 : ZMod 1361244631) ^ 5192) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 85638769 := by rw [factor_0_12]; decide
      have factor_0_14 : (12 : ZMod 1361244631) ^ 20770 = 638727196 := by
        calc
          (12 : ZMod 1361244631) ^ 20770 = (12 : ZMod 1361244631) ^ (10385 + 10385) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 10385 * (12 : ZMod 1361244631) ^ 10385 := by rw [pow_add]
          _ = 638727196 := by rw [factor_0_13]; decide
      have factor_0_15 : (12 : ZMod 1361244631) ^ 41541 = 875319046 := by
        calc
          (12 : ZMod 1361244631) ^ 41541 = (12 : ZMod 1361244631) ^ (20770 + 20770 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 20770 * (12 : ZMod 1361244631) ^ 20770) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 875319046 := by rw [factor_0_14]; decide
      have factor_0_16 : (12 : ZMod 1361244631) ^ 83083 = 1088934249 := by
        calc
          (12 : ZMod 1361244631) ^ 83083 = (12 : ZMod 1361244631) ^ (41541 + 41541 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 41541 * (12 : ZMod 1361244631) ^ 41541) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1088934249 := by rw [factor_0_15]; decide
      have factor_0_17 : (12 : ZMod 1361244631) ^ 166167 = 19562924 := by
        calc
          (12 : ZMod 1361244631) ^ 166167 = (12 : ZMod 1361244631) ^ (83083 + 83083 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 83083 * (12 : ZMod 1361244631) ^ 83083) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 19562924 := by rw [factor_0_16]; decide
      have factor_0_18 : (12 : ZMod 1361244631) ^ 332335 = 955054955 := by
        calc
          (12 : ZMod 1361244631) ^ 332335 = (12 : ZMod 1361244631) ^ (166167 + 166167 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 166167 * (12 : ZMod 1361244631) ^ 166167) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 955054955 := by rw [factor_0_17]; decide
      have factor_0_19 : (12 : ZMod 1361244631) ^ 664670 = 1266442355 := by
        calc
          (12 : ZMod 1361244631) ^ 664670 = (12 : ZMod 1361244631) ^ (332335 + 332335) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 332335 * (12 : ZMod 1361244631) ^ 332335 := by rw [pow_add]
          _ = 1266442355 := by rw [factor_0_18]; decide
      have factor_0_20 : (12 : ZMod 1361244631) ^ 1329340 = 873022824 := by
        calc
          (12 : ZMod 1361244631) ^ 1329340 = (12 : ZMod 1361244631) ^ (664670 + 664670) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 664670 * (12 : ZMod 1361244631) ^ 664670 := by rw [pow_add]
          _ = 873022824 := by rw [factor_0_19]; decide
      have factor_0_21 : (12 : ZMod 1361244631) ^ 2658680 = 1350763423 := by
        calc
          (12 : ZMod 1361244631) ^ 2658680 = (12 : ZMod 1361244631) ^ (1329340 + 1329340) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1329340 * (12 : ZMod 1361244631) ^ 1329340 := by rw [pow_add]
          _ = 1350763423 := by rw [factor_0_20]; decide
      have factor_0_22 : (12 : ZMod 1361244631) ^ 5317361 = 1238161100 := by
        calc
          (12 : ZMod 1361244631) ^ 5317361 = (12 : ZMod 1361244631) ^ (2658680 + 2658680 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 2658680 * (12 : ZMod 1361244631) ^ 2658680) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1238161100 := by rw [factor_0_21]; decide
      have factor_0_23 : (12 : ZMod 1361244631) ^ 10634723 = 282846564 := by
        calc
          (12 : ZMod 1361244631) ^ 10634723 = (12 : ZMod 1361244631) ^ (5317361 + 5317361 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 5317361 * (12 : ZMod 1361244631) ^ 5317361) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 282846564 := by rw [factor_0_22]; decide
      have factor_0_24 : (12 : ZMod 1361244631) ^ 21269447 = 254531764 := by
        calc
          (12 : ZMod 1361244631) ^ 21269447 = (12 : ZMod 1361244631) ^ (10634723 + 10634723 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 10634723 * (12 : ZMod 1361244631) ^ 10634723) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 254531764 := by rw [factor_0_23]; decide
      have factor_0_25 : (12 : ZMod 1361244631) ^ 42538894 = 759539100 := by
        calc
          (12 : ZMod 1361244631) ^ 42538894 = (12 : ZMod 1361244631) ^ (21269447 + 21269447) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 21269447 * (12 : ZMod 1361244631) ^ 21269447 := by rw [pow_add]
          _ = 759539100 := by rw [factor_0_24]; decide
      have factor_0_26 : (12 : ZMod 1361244631) ^ 85077789 = 1101973702 := by
        calc
          (12 : ZMod 1361244631) ^ 85077789 = (12 : ZMod 1361244631) ^ (42538894 + 42538894 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 42538894 * (12 : ZMod 1361244631) ^ 42538894) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1101973702 := by rw [factor_0_25]; decide
      have factor_0_27 : (12 : ZMod 1361244631) ^ 170155578 = 741933014 := by
        calc
          (12 : ZMod 1361244631) ^ 170155578 = (12 : ZMod 1361244631) ^ (85077789 + 85077789) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 85077789 * (12 : ZMod 1361244631) ^ 85077789 := by rw [pow_add]
          _ = 741933014 := by rw [factor_0_26]; decide
      have factor_0_28 : (12 : ZMod 1361244631) ^ 340311157 = 291051811 := by
        calc
          (12 : ZMod 1361244631) ^ 340311157 = (12 : ZMod 1361244631) ^ (170155578 + 170155578 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 170155578 * (12 : ZMod 1361244631) ^ 170155578) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 291051811 := by rw [factor_0_27]; decide
      have factor_0_29 : (12 : ZMod 1361244631) ^ 680622315 = 1361244630 := by
        calc
          (12 : ZMod 1361244631) ^ 680622315 = (12 : ZMod 1361244631) ^ (340311157 + 340311157 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 340311157 * (12 : ZMod 1361244631) ^ 340311157) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1361244630 := by rw [factor_0_28]; decide
      change (12 : ZMod 1361244631) ^ 680622315 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (12 : ZMod 1361244631) ^ 1 = 12 := by norm_num
      have factor_1_1 : (12 : ZMod 1361244631) ^ 3 = 1728 := by
        calc
          (12 : ZMod 1361244631) ^ 3 = (12 : ZMod 1361244631) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 1 * (12 : ZMod 1361244631) ^ 1) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1728 := by rw [factor_1_0]; decide
      have factor_1_2 : (12 : ZMod 1361244631) ^ 6 = 2985984 := by
        calc
          (12 : ZMod 1361244631) ^ 6 = (12 : ZMod 1361244631) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 3 * (12 : ZMod 1361244631) ^ 3 := by rw [pow_add]
          _ = 2985984 := by rw [factor_1_1]; decide
      have factor_1_3 : (12 : ZMod 1361244631) ^ 13 = 738627103 := by
        calc
          (12 : ZMod 1361244631) ^ 13 = (12 : ZMod 1361244631) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 6 * (12 : ZMod 1361244631) ^ 6) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 738627103 := by rw [factor_1_2]; decide
      have factor_1_4 : (12 : ZMod 1361244631) ^ 27 = 343917096 := by
        calc
          (12 : ZMod 1361244631) ^ 27 = (12 : ZMod 1361244631) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 13 * (12 : ZMod 1361244631) ^ 13) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 343917096 := by rw [factor_1_3]; decide
      have factor_1_5 : (12 : ZMod 1361244631) ^ 54 = 947647606 := by
        calc
          (12 : ZMod 1361244631) ^ 54 = (12 : ZMod 1361244631) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 27 * (12 : ZMod 1361244631) ^ 27 := by rw [pow_add]
          _ = 947647606 := by rw [factor_1_4]; decide
      have factor_1_6 : (12 : ZMod 1361244631) ^ 108 = 507159292 := by
        calc
          (12 : ZMod 1361244631) ^ 108 = (12 : ZMod 1361244631) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 54 * (12 : ZMod 1361244631) ^ 54 := by rw [pow_add]
          _ = 507159292 := by rw [factor_1_5]; decide
      have factor_1_7 : (12 : ZMod 1361244631) ^ 216 = 1270295646 := by
        calc
          (12 : ZMod 1361244631) ^ 216 = (12 : ZMod 1361244631) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 108 * (12 : ZMod 1361244631) ^ 108 := by rw [pow_add]
          _ = 1270295646 := by rw [factor_1_6]; decide
      have factor_1_8 : (12 : ZMod 1361244631) ^ 432 = 527709721 := by
        calc
          (12 : ZMod 1361244631) ^ 432 = (12 : ZMod 1361244631) ^ (216 + 216) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 216 * (12 : ZMod 1361244631) ^ 216 := by rw [pow_add]
          _ = 527709721 := by rw [factor_1_7]; decide
      have factor_1_9 : (12 : ZMod 1361244631) ^ 865 = 1058101571 := by
        calc
          (12 : ZMod 1361244631) ^ 865 = (12 : ZMod 1361244631) ^ (432 + 432 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 432 * (12 : ZMod 1361244631) ^ 432) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1058101571 := by rw [factor_1_8]; decide
      have factor_1_10 : (12 : ZMod 1361244631) ^ 1730 = 974815524 := by
        calc
          (12 : ZMod 1361244631) ^ 1730 = (12 : ZMod 1361244631) ^ (865 + 865) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 865 * (12 : ZMod 1361244631) ^ 865 := by rw [pow_add]
          _ = 974815524 := by rw [factor_1_9]; decide
      have factor_1_11 : (12 : ZMod 1361244631) ^ 3461 = 1338476711 := by
        calc
          (12 : ZMod 1361244631) ^ 3461 = (12 : ZMod 1361244631) ^ (1730 + 1730 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 1730 * (12 : ZMod 1361244631) ^ 1730) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1338476711 := by rw [factor_1_10]; decide
      have factor_1_12 : (12 : ZMod 1361244631) ^ 6923 = 49716967 := by
        calc
          (12 : ZMod 1361244631) ^ 6923 = (12 : ZMod 1361244631) ^ (3461 + 3461 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 3461 * (12 : ZMod 1361244631) ^ 3461) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 49716967 := by rw [factor_1_11]; decide
      have factor_1_13 : (12 : ZMod 1361244631) ^ 13847 = 1285619825 := by
        calc
          (12 : ZMod 1361244631) ^ 13847 = (12 : ZMod 1361244631) ^ (6923 + 6923 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 6923 * (12 : ZMod 1361244631) ^ 6923) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1285619825 := by rw [factor_1_12]; decide
      have factor_1_14 : (12 : ZMod 1361244631) ^ 27694 = 1231012963 := by
        calc
          (12 : ZMod 1361244631) ^ 27694 = (12 : ZMod 1361244631) ^ (13847 + 13847) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 13847 * (12 : ZMod 1361244631) ^ 13847 := by rw [pow_add]
          _ = 1231012963 := by rw [factor_1_13]; decide
      have factor_1_15 : (12 : ZMod 1361244631) ^ 55389 = 939776604 := by
        calc
          (12 : ZMod 1361244631) ^ 55389 = (12 : ZMod 1361244631) ^ (27694 + 27694 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 27694 * (12 : ZMod 1361244631) ^ 27694) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 939776604 := by rw [factor_1_14]; decide
      have factor_1_16 : (12 : ZMod 1361244631) ^ 110778 = 914660645 := by
        calc
          (12 : ZMod 1361244631) ^ 110778 = (12 : ZMod 1361244631) ^ (55389 + 55389) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 55389 * (12 : ZMod 1361244631) ^ 55389 := by rw [pow_add]
          _ = 914660645 := by rw [factor_1_15]; decide
      have factor_1_17 : (12 : ZMod 1361244631) ^ 221556 = 230237067 := by
        calc
          (12 : ZMod 1361244631) ^ 221556 = (12 : ZMod 1361244631) ^ (110778 + 110778) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 110778 * (12 : ZMod 1361244631) ^ 110778 := by rw [pow_add]
          _ = 230237067 := by rw [factor_1_16]; decide
      have factor_1_18 : (12 : ZMod 1361244631) ^ 443113 = 326539832 := by
        calc
          (12 : ZMod 1361244631) ^ 443113 = (12 : ZMod 1361244631) ^ (221556 + 221556 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 221556 * (12 : ZMod 1361244631) ^ 221556) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 326539832 := by rw [factor_1_17]; decide
      have factor_1_19 : (12 : ZMod 1361244631) ^ 886226 = 215377167 := by
        calc
          (12 : ZMod 1361244631) ^ 886226 = (12 : ZMod 1361244631) ^ (443113 + 443113) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 443113 * (12 : ZMod 1361244631) ^ 443113 := by rw [pow_add]
          _ = 215377167 := by rw [factor_1_18]; decide
      have factor_1_20 : (12 : ZMod 1361244631) ^ 1772453 = 1040081957 := by
        calc
          (12 : ZMod 1361244631) ^ 1772453 = (12 : ZMod 1361244631) ^ (886226 + 886226 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 886226 * (12 : ZMod 1361244631) ^ 886226) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1040081957 := by rw [factor_1_19]; decide
      have factor_1_21 : (12 : ZMod 1361244631) ^ 3544907 = 18081615 := by
        calc
          (12 : ZMod 1361244631) ^ 3544907 = (12 : ZMod 1361244631) ^ (1772453 + 1772453 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 1772453 * (12 : ZMod 1361244631) ^ 1772453) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 18081615 := by rw [factor_1_20]; decide
      have factor_1_22 : (12 : ZMod 1361244631) ^ 7089815 = 535214061 := by
        calc
          (12 : ZMod 1361244631) ^ 7089815 = (12 : ZMod 1361244631) ^ (3544907 + 3544907 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 3544907 * (12 : ZMod 1361244631) ^ 3544907) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 535214061 := by rw [factor_1_21]; decide
      have factor_1_23 : (12 : ZMod 1361244631) ^ 14179631 = 1360082755 := by
        calc
          (12 : ZMod 1361244631) ^ 14179631 = (12 : ZMod 1361244631) ^ (7089815 + 7089815 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 7089815 * (12 : ZMod 1361244631) ^ 7089815) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1360082755 := by rw [factor_1_22]; decide
      have factor_1_24 : (12 : ZMod 1361244631) ^ 28359263 = 658963612 := by
        calc
          (12 : ZMod 1361244631) ^ 28359263 = (12 : ZMod 1361244631) ^ (14179631 + 14179631 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 14179631 * (12 : ZMod 1361244631) ^ 14179631) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 658963612 := by rw [factor_1_23]; decide
      have factor_1_25 : (12 : ZMod 1361244631) ^ 56718526 = 1265323160 := by
        calc
          (12 : ZMod 1361244631) ^ 56718526 = (12 : ZMod 1361244631) ^ (28359263 + 28359263) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 28359263 * (12 : ZMod 1361244631) ^ 28359263 := by rw [pow_add]
          _ = 1265323160 := by rw [factor_1_24]; decide
      have factor_1_26 : (12 : ZMod 1361244631) ^ 113437052 = 1166459379 := by
        calc
          (12 : ZMod 1361244631) ^ 113437052 = (12 : ZMod 1361244631) ^ (56718526 + 56718526) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 56718526 * (12 : ZMod 1361244631) ^ 56718526 := by rw [pow_add]
          _ = 1166459379 := by rw [factor_1_25]; decide
      have factor_1_27 : (12 : ZMod 1361244631) ^ 226874105 = 192533118 := by
        calc
          (12 : ZMod 1361244631) ^ 226874105 = (12 : ZMod 1361244631) ^ (113437052 + 113437052 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 113437052 * (12 : ZMod 1361244631) ^ 113437052) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 192533118 := by rw [factor_1_26]; decide
      have factor_1_28 : (12 : ZMod 1361244631) ^ 453748210 = 192533117 := by
        calc
          (12 : ZMod 1361244631) ^ 453748210 = (12 : ZMod 1361244631) ^ (226874105 + 226874105) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 226874105 * (12 : ZMod 1361244631) ^ 226874105 := by rw [pow_add]
          _ = 192533117 := by rw [factor_1_27]; decide
      change (12 : ZMod 1361244631) ^ 453748210 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (12 : ZMod 1361244631) ^ 1 = 12 := by norm_num
      have factor_2_1 : (12 : ZMod 1361244631) ^ 2 = 144 := by
        calc
          (12 : ZMod 1361244631) ^ 2 = (12 : ZMod 1361244631) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1 * (12 : ZMod 1361244631) ^ 1 := by rw [pow_add]
          _ = 144 := by rw [factor_2_0]; decide
      have factor_2_2 : (12 : ZMod 1361244631) ^ 4 = 20736 := by
        calc
          (12 : ZMod 1361244631) ^ 4 = (12 : ZMod 1361244631) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 2 * (12 : ZMod 1361244631) ^ 2 := by rw [pow_add]
          _ = 20736 := by rw [factor_2_1]; decide
      have factor_2_3 : (12 : ZMod 1361244631) ^ 8 = 429981696 := by
        calc
          (12 : ZMod 1361244631) ^ 8 = (12 : ZMod 1361244631) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 4 * (12 : ZMod 1361244631) ^ 4 := by rw [pow_add]
          _ = 429981696 := by rw [factor_2_2]; decide
      have factor_2_4 : (12 : ZMod 1361244631) ^ 16 = 861414737 := by
        calc
          (12 : ZMod 1361244631) ^ 16 = (12 : ZMod 1361244631) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 8 * (12 : ZMod 1361244631) ^ 8 := by rw [pow_add]
          _ = 861414737 := by rw [factor_2_3]; decide
      have factor_2_5 : (12 : ZMod 1361244631) ^ 32 = 212614795 := by
        calc
          (12 : ZMod 1361244631) ^ 32 = (12 : ZMod 1361244631) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 16 * (12 : ZMod 1361244631) ^ 16 := by rw [pow_add]
          _ = 212614795 := by rw [factor_2_4]; decide
      have factor_2_6 : (12 : ZMod 1361244631) ^ 64 = 819951329 := by
        calc
          (12 : ZMod 1361244631) ^ 64 = (12 : ZMod 1361244631) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 32 * (12 : ZMod 1361244631) ^ 32 := by rw [pow_add]
          _ = 819951329 := by rw [factor_2_5]; decide
      have factor_2_7 : (12 : ZMod 1361244631) ^ 129 = 1252129494 := by
        calc
          (12 : ZMod 1361244631) ^ 129 = (12 : ZMod 1361244631) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 64 * (12 : ZMod 1361244631) ^ 64) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1252129494 := by rw [factor_2_6]; decide
      have factor_2_8 : (12 : ZMod 1361244631) ^ 259 = 32979793 := by
        calc
          (12 : ZMod 1361244631) ^ 259 = (12 : ZMod 1361244631) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 129 * (12 : ZMod 1361244631) ^ 129) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 32979793 := by rw [factor_2_7]; decide
      have factor_2_9 : (12 : ZMod 1361244631) ^ 519 = 840370984 := by
        calc
          (12 : ZMod 1361244631) ^ 519 = (12 : ZMod 1361244631) ^ (259 + 259 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 259 * (12 : ZMod 1361244631) ^ 259) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 840370984 := by rw [factor_2_8]; decide
      have factor_2_10 : (12 : ZMod 1361244631) ^ 1038 = 459491108 := by
        calc
          (12 : ZMod 1361244631) ^ 1038 = (12 : ZMod 1361244631) ^ (519 + 519) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 519 * (12 : ZMod 1361244631) ^ 519 := by rw [pow_add]
          _ = 459491108 := by rw [factor_2_9]; decide
      have factor_2_11 : (12 : ZMod 1361244631) ^ 2077 = 404307884 := by
        calc
          (12 : ZMod 1361244631) ^ 2077 = (12 : ZMod 1361244631) ^ (1038 + 1038 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 1038 * (12 : ZMod 1361244631) ^ 1038) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 404307884 := by rw [factor_2_10]; decide
      have factor_2_12 : (12 : ZMod 1361244631) ^ 4154 = 931393951 := by
        calc
          (12 : ZMod 1361244631) ^ 4154 = (12 : ZMod 1361244631) ^ (2077 + 2077) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 2077 * (12 : ZMod 1361244631) ^ 2077 := by rw [pow_add]
          _ = 931393951 := by rw [factor_2_11]; decide
      have factor_2_13 : (12 : ZMod 1361244631) ^ 8308 = 223523757 := by
        calc
          (12 : ZMod 1361244631) ^ 8308 = (12 : ZMod 1361244631) ^ (4154 + 4154) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 4154 * (12 : ZMod 1361244631) ^ 4154 := by rw [pow_add]
          _ = 223523757 := by rw [factor_2_12]; decide
      have factor_2_14 : (12 : ZMod 1361244631) ^ 16616 = 198672415 := by
        calc
          (12 : ZMod 1361244631) ^ 16616 = (12 : ZMod 1361244631) ^ (8308 + 8308) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 8308 * (12 : ZMod 1361244631) ^ 8308 := by rw [pow_add]
          _ = 198672415 := by rw [factor_2_13]; decide
      have factor_2_15 : (12 : ZMod 1361244631) ^ 33233 = 1149966893 := by
        calc
          (12 : ZMod 1361244631) ^ 33233 = (12 : ZMod 1361244631) ^ (16616 + 16616 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 16616 * (12 : ZMod 1361244631) ^ 16616) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1149966893 := by rw [factor_2_14]; decide
      have factor_2_16 : (12 : ZMod 1361244631) ^ 66467 = 510984665 := by
        calc
          (12 : ZMod 1361244631) ^ 66467 = (12 : ZMod 1361244631) ^ (33233 + 33233 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 33233 * (12 : ZMod 1361244631) ^ 33233) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 510984665 := by rw [factor_2_15]; decide
      have factor_2_17 : (12 : ZMod 1361244631) ^ 132934 = 786501086 := by
        calc
          (12 : ZMod 1361244631) ^ 132934 = (12 : ZMod 1361244631) ^ (66467 + 66467) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 66467 * (12 : ZMod 1361244631) ^ 66467 := by rw [pow_add]
          _ = 786501086 := by rw [factor_2_16]; decide
      have factor_2_18 : (12 : ZMod 1361244631) ^ 265868 = 662198657 := by
        calc
          (12 : ZMod 1361244631) ^ 265868 = (12 : ZMod 1361244631) ^ (132934 + 132934) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 132934 * (12 : ZMod 1361244631) ^ 132934 := by rw [pow_add]
          _ = 662198657 := by rw [factor_2_17]; decide
      have factor_2_19 : (12 : ZMod 1361244631) ^ 531736 = 1100362037 := by
        calc
          (12 : ZMod 1361244631) ^ 531736 = (12 : ZMod 1361244631) ^ (265868 + 265868) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 265868 * (12 : ZMod 1361244631) ^ 265868 := by rw [pow_add]
          _ = 1100362037 := by rw [factor_2_18]; decide
      have factor_2_20 : (12 : ZMod 1361244631) ^ 1063472 = 992289876 := by
        calc
          (12 : ZMod 1361244631) ^ 1063472 = (12 : ZMod 1361244631) ^ (531736 + 531736) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 531736 * (12 : ZMod 1361244631) ^ 531736 := by rw [pow_add]
          _ = 992289876 := by rw [factor_2_19]; decide
      have factor_2_21 : (12 : ZMod 1361244631) ^ 2126944 = 939523153 := by
        calc
          (12 : ZMod 1361244631) ^ 2126944 = (12 : ZMod 1361244631) ^ (1063472 + 1063472) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1063472 * (12 : ZMod 1361244631) ^ 1063472 := by rw [pow_add]
          _ = 939523153 := by rw [factor_2_20]; decide
      have factor_2_22 : (12 : ZMod 1361244631) ^ 4253889 = 1250805815 := by
        calc
          (12 : ZMod 1361244631) ^ 4253889 = (12 : ZMod 1361244631) ^ (2126944 + 2126944 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 2126944 * (12 : ZMod 1361244631) ^ 2126944) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1250805815 := by rw [factor_2_21]; decide
      have factor_2_23 : (12 : ZMod 1361244631) ^ 8507778 = 604391321 := by
        calc
          (12 : ZMod 1361244631) ^ 8507778 = (12 : ZMod 1361244631) ^ (4253889 + 4253889) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 4253889 * (12 : ZMod 1361244631) ^ 4253889 := by rw [pow_add]
          _ = 604391321 := by rw [factor_2_22]; decide
      have factor_2_24 : (12 : ZMod 1361244631) ^ 17015557 = 910666525 := by
        calc
          (12 : ZMod 1361244631) ^ 17015557 = (12 : ZMod 1361244631) ^ (8507778 + 8507778 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 8507778 * (12 : ZMod 1361244631) ^ 8507778) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 910666525 := by rw [factor_2_23]; decide
      have factor_2_25 : (12 : ZMod 1361244631) ^ 34031115 = 260957494 := by
        calc
          (12 : ZMod 1361244631) ^ 34031115 = (12 : ZMod 1361244631) ^ (17015557 + 17015557 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 17015557 * (12 : ZMod 1361244631) ^ 17015557) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 260957494 := by rw [factor_2_24]; decide
      have factor_2_26 : (12 : ZMod 1361244631) ^ 68062231 = 438558504 := by
        calc
          (12 : ZMod 1361244631) ^ 68062231 = (12 : ZMod 1361244631) ^ (34031115 + 34031115 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 34031115 * (12 : ZMod 1361244631) ^ 34031115) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 438558504 := by rw [factor_2_25]; decide
      have factor_2_27 : (12 : ZMod 1361244631) ^ 136124463 = 391030125 := by
        calc
          (12 : ZMod 1361244631) ^ 136124463 = (12 : ZMod 1361244631) ^ (68062231 + 68062231 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 68062231 * (12 : ZMod 1361244631) ^ 68062231) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 391030125 := by rw [factor_2_26]; decide
      have factor_2_28 : (12 : ZMod 1361244631) ^ 272248926 = 321307481 := by
        calc
          (12 : ZMod 1361244631) ^ 272248926 = (12 : ZMod 1361244631) ^ (136124463 + 136124463) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 136124463 * (12 : ZMod 1361244631) ^ 136124463 := by rw [pow_add]
          _ = 321307481 := by rw [factor_2_27]; decide
      change (12 : ZMod 1361244631) ^ 272248926 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (12 : ZMod 1361244631) ^ 1 = 12 := by norm_num
      have factor_3_1 : (12 : ZMod 1361244631) ^ 2 = 144 := by
        calc
          (12 : ZMod 1361244631) ^ 2 = (12 : ZMod 1361244631) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1 * (12 : ZMod 1361244631) ^ 1 := by rw [pow_add]
          _ = 144 := by rw [factor_3_0]; decide
      have factor_3_2 : (12 : ZMod 1361244631) ^ 5 = 248832 := by
        calc
          (12 : ZMod 1361244631) ^ 5 = (12 : ZMod 1361244631) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 2 * (12 : ZMod 1361244631) ^ 2) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 248832 := by rw [factor_3_1]; decide
      have factor_3_3 : (12 : ZMod 1361244631) ^ 11 = 1130046793 := by
        calc
          (12 : ZMod 1361244631) ^ 11 = (12 : ZMod 1361244631) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 5 * (12 : ZMod 1361244631) ^ 5) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1130046793 := by rw [factor_3_2]; decide
      have factor_3_4 : (12 : ZMod 1361244631) ^ 22 = 882158276 := by
        calc
          (12 : ZMod 1361244631) ^ 22 = (12 : ZMod 1361244631) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 11 * (12 : ZMod 1361244631) ^ 11 := by rw [pow_add]
          _ = 882158276 := by rw [factor_3_3]; decide
      have factor_3_5 : (12 : ZMod 1361244631) ^ 44 = 1283645423 := by
        calc
          (12 : ZMod 1361244631) ^ 44 = (12 : ZMod 1361244631) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 22 * (12 : ZMod 1361244631) ^ 22 := by rw [pow_add]
          _ = 1283645423 := by rw [factor_3_4]; decide
      have factor_3_6 : (12 : ZMod 1361244631) ^ 89 = 643347727 := by
        calc
          (12 : ZMod 1361244631) ^ 89 = (12 : ZMod 1361244631) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 44 * (12 : ZMod 1361244631) ^ 44) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 643347727 := by rw [factor_3_5]; decide
      have factor_3_7 : (12 : ZMod 1361244631) ^ 179 = 56992289 := by
        calc
          (12 : ZMod 1361244631) ^ 179 = (12 : ZMod 1361244631) ^ (89 + 89 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 89 * (12 : ZMod 1361244631) ^ 89) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 56992289 := by rw [factor_3_6]; decide
      have factor_3_8 : (12 : ZMod 1361244631) ^ 358 = 741645181 := by
        calc
          (12 : ZMod 1361244631) ^ 358 = (12 : ZMod 1361244631) ^ (179 + 179) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 179 * (12 : ZMod 1361244631) ^ 179 := by rw [pow_add]
          _ = 741645181 := by rw [factor_3_7]; decide
      have factor_3_9 : (12 : ZMod 1361244631) ^ 716 = 950205161 := by
        calc
          (12 : ZMod 1361244631) ^ 716 = (12 : ZMod 1361244631) ^ (358 + 358) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 358 * (12 : ZMod 1361244631) ^ 358 := by rw [pow_add]
          _ = 950205161 := by rw [factor_3_8]; decide
      have factor_3_10 : (12 : ZMod 1361244631) ^ 1432 = 1213941834 := by
        calc
          (12 : ZMod 1361244631) ^ 1432 = (12 : ZMod 1361244631) ^ (716 + 716) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 716 * (12 : ZMod 1361244631) ^ 716 := by rw [pow_add]
          _ = 1213941834 := by rw [factor_3_9]; decide
      have factor_3_11 : (12 : ZMod 1361244631) ^ 2864 = 1181633892 := by
        calc
          (12 : ZMod 1361244631) ^ 2864 = (12 : ZMod 1361244631) ^ (1432 + 1432) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1432 * (12 : ZMod 1361244631) ^ 1432 := by rw [pow_add]
          _ = 1181633892 := by rw [factor_3_10]; decide
      have factor_3_12 : (12 : ZMod 1361244631) ^ 5729 = 594303371 := by
        calc
          (12 : ZMod 1361244631) ^ 5729 = (12 : ZMod 1361244631) ^ (2864 + 2864 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 2864 * (12 : ZMod 1361244631) ^ 2864) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 594303371 := by rw [factor_3_11]; decide
      have factor_3_13 : (12 : ZMod 1361244631) ^ 11459 = 803167289 := by
        calc
          (12 : ZMod 1361244631) ^ 11459 = (12 : ZMod 1361244631) ^ (5729 + 5729 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 5729 * (12 : ZMod 1361244631) ^ 5729) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 803167289 := by rw [factor_3_12]; decide
      have factor_3_14 : (12 : ZMod 1361244631) ^ 22919 = 274518633 := by
        calc
          (12 : ZMod 1361244631) ^ 22919 = (12 : ZMod 1361244631) ^ (11459 + 11459 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 11459 * (12 : ZMod 1361244631) ^ 11459) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 274518633 := by rw [factor_3_13]; decide
      have factor_3_15 : (12 : ZMod 1361244631) ^ 45839 = 1332915200 := by
        calc
          (12 : ZMod 1361244631) ^ 45839 = (12 : ZMod 1361244631) ^ (22919 + 22919 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 22919 * (12 : ZMod 1361244631) ^ 22919) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1332915200 := by rw [factor_3_14]; decide
      have factor_3_16 : (12 : ZMod 1361244631) ^ 91678 = 857461936 := by
        calc
          (12 : ZMod 1361244631) ^ 91678 = (12 : ZMod 1361244631) ^ (45839 + 45839) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 45839 * (12 : ZMod 1361244631) ^ 45839 := by rw [pow_add]
          _ = 857461936 := by rw [factor_3_15]; decide
      have factor_3_17 : (12 : ZMod 1361244631) ^ 183357 = 535363227 := by
        calc
          (12 : ZMod 1361244631) ^ 183357 = (12 : ZMod 1361244631) ^ (91678 + 91678 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 91678 * (12 : ZMod 1361244631) ^ 91678) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 535363227 := by rw [factor_3_16]; decide
      have factor_3_18 : (12 : ZMod 1361244631) ^ 366714 = 679003851 := by
        calc
          (12 : ZMod 1361244631) ^ 366714 = (12 : ZMod 1361244631) ^ (183357 + 183357) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 183357 * (12 : ZMod 1361244631) ^ 183357 := by rw [pow_add]
          _ = 679003851 := by rw [factor_3_17]; decide
      have factor_3_19 : (12 : ZMod 1361244631) ^ 733429 = 628278702 := by
        calc
          (12 : ZMod 1361244631) ^ 733429 = (12 : ZMod 1361244631) ^ (366714 + 366714 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 366714 * (12 : ZMod 1361244631) ^ 366714) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 628278702 := by rw [factor_3_18]; decide
      have factor_3_20 : (12 : ZMod 1361244631) ^ 1466858 = 916035504 := by
        calc
          (12 : ZMod 1361244631) ^ 1466858 = (12 : ZMod 1361244631) ^ (733429 + 733429) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 733429 * (12 : ZMod 1361244631) ^ 733429 := by rw [pow_add]
          _ = 916035504 := by rw [factor_3_19]; decide
      have factor_3_21 : (12 : ZMod 1361244631) ^ 2933716 = 1178012903 := by
        calc
          (12 : ZMod 1361244631) ^ 2933716 = (12 : ZMod 1361244631) ^ (1466858 + 1466858) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1466858 * (12 : ZMod 1361244631) ^ 1466858 := by rw [pow_add]
          _ = 1178012903 := by rw [factor_3_20]; decide
      have factor_3_22 : (12 : ZMod 1361244631) ^ 5867433 = 512416885 := by
        calc
          (12 : ZMod 1361244631) ^ 5867433 = (12 : ZMod 1361244631) ^ (2933716 + 2933716 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 2933716 * (12 : ZMod 1361244631) ^ 2933716) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 512416885 := by rw [factor_3_21]; decide
      have factor_3_23 : (12 : ZMod 1361244631) ^ 11734867 = 111948644 := by
        calc
          (12 : ZMod 1361244631) ^ 11734867 = (12 : ZMod 1361244631) ^ (5867433 + 5867433 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 5867433 * (12 : ZMod 1361244631) ^ 5867433) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 111948644 := by rw [factor_3_22]; decide
      have factor_3_24 : (12 : ZMod 1361244631) ^ 23469735 = 1142117748 := by
        calc
          (12 : ZMod 1361244631) ^ 23469735 = (12 : ZMod 1361244631) ^ (11734867 + 11734867 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 11734867 * (12 : ZMod 1361244631) ^ 11734867) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1142117748 := by rw [factor_3_23]; decide
      have factor_3_25 : (12 : ZMod 1361244631) ^ 46939470 = 95839604 := by
        calc
          (12 : ZMod 1361244631) ^ 46939470 = (12 : ZMod 1361244631) ^ (23469735 + 23469735) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 23469735 * (12 : ZMod 1361244631) ^ 23469735 := by rw [pow_add]
          _ = 95839604 := by rw [factor_3_24]; decide
      change (12 : ZMod 1361244631) ^ 46939470 ≠ 1
      rw [factor_3_25]
      decide
    ·
      have factor_4_0 : (12 : ZMod 1361244631) ^ 1 = 12 := by norm_num
      have factor_4_1 : (12 : ZMod 1361244631) ^ 2 = 144 := by
        calc
          (12 : ZMod 1361244631) ^ 2 = (12 : ZMod 1361244631) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1 * (12 : ZMod 1361244631) ^ 1 := by rw [pow_add]
          _ = 144 := by rw [factor_4_0]; decide
      have factor_4_2 : (12 : ZMod 1361244631) ^ 4 = 20736 := by
        calc
          (12 : ZMod 1361244631) ^ 4 = (12 : ZMod 1361244631) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 2 * (12 : ZMod 1361244631) ^ 2 := by rw [pow_add]
          _ = 20736 := by rw [factor_4_1]; decide
      have factor_4_3 : (12 : ZMod 1361244631) ^ 8 = 429981696 := by
        calc
          (12 : ZMod 1361244631) ^ 8 = (12 : ZMod 1361244631) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 4 * (12 : ZMod 1361244631) ^ 4 := by rw [pow_add]
          _ = 429981696 := by rw [factor_4_2]; decide
      have factor_4_4 : (12 : ZMod 1361244631) ^ 17 = 808264427 := by
        calc
          (12 : ZMod 1361244631) ^ 17 = (12 : ZMod 1361244631) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 8 * (12 : ZMod 1361244631) ^ 8) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 808264427 := by rw [factor_4_3]; decide
      have factor_4_5 : (12 : ZMod 1361244631) ^ 34 = 669148598 := by
        calc
          (12 : ZMod 1361244631) ^ 34 = (12 : ZMod 1361244631) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 17 * (12 : ZMod 1361244631) ^ 17 := by rw [pow_add]
          _ = 669148598 := by rw [factor_4_4]; decide
      have factor_4_6 : (12 : ZMod 1361244631) ^ 69 = 1338824924 := by
        calc
          (12 : ZMod 1361244631) ^ 69 = (12 : ZMod 1361244631) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 34 * (12 : ZMod 1361244631) ^ 34) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1338824924 := by rw [factor_4_5]; decide
      have factor_4_7 : (12 : ZMod 1361244631) ^ 139 = 623800996 := by
        calc
          (12 : ZMod 1361244631) ^ 139 = (12 : ZMod 1361244631) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 69 * (12 : ZMod 1361244631) ^ 69) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 623800996 := by rw [factor_4_6]; decide
      have factor_4_8 : (12 : ZMod 1361244631) ^ 278 = 56973412 := by
        calc
          (12 : ZMod 1361244631) ^ 278 = (12 : ZMod 1361244631) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 139 * (12 : ZMod 1361244631) ^ 139 := by rw [pow_add]
          _ = 56973412 := by rw [factor_4_7]; decide
      have factor_4_9 : (12 : ZMod 1361244631) ^ 557 = 770247977 := by
        calc
          (12 : ZMod 1361244631) ^ 557 = (12 : ZMod 1361244631) ^ (278 + 278 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 278 * (12 : ZMod 1361244631) ^ 278) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 770247977 := by rw [factor_4_8]; decide
      have factor_4_10 : (12 : ZMod 1361244631) ^ 1115 = 822711476 := by
        calc
          (12 : ZMod 1361244631) ^ 1115 = (12 : ZMod 1361244631) ^ (557 + 557 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 557 * (12 : ZMod 1361244631) ^ 557) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 822711476 := by rw [factor_4_9]; decide
      have factor_4_11 : (12 : ZMod 1361244631) ^ 2230 = 179847536 := by
        calc
          (12 : ZMod 1361244631) ^ 2230 = (12 : ZMod 1361244631) ^ (1115 + 1115) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 1115 * (12 : ZMod 1361244631) ^ 1115 := by rw [pow_add]
          _ = 179847536 := by rw [factor_4_10]; decide
      have factor_4_12 : (12 : ZMod 1361244631) ^ 4460 = 857953394 := by
        calc
          (12 : ZMod 1361244631) ^ 4460 = (12 : ZMod 1361244631) ^ (2230 + 2230) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 2230 * (12 : ZMod 1361244631) ^ 2230 := by rw [pow_add]
          _ = 857953394 := by rw [factor_4_11]; decide
      have factor_4_13 : (12 : ZMod 1361244631) ^ 8921 = 1190578542 := by
        calc
          (12 : ZMod 1361244631) ^ 8921 = (12 : ZMod 1361244631) ^ (4460 + 4460 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 4460 * (12 : ZMod 1361244631) ^ 4460) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1190578542 := by rw [factor_4_12]; decide
      have factor_4_14 : (12 : ZMod 1361244631) ^ 17843 = 242746376 := by
        calc
          (12 : ZMod 1361244631) ^ 17843 = (12 : ZMod 1361244631) ^ (8921 + 8921 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 8921 * (12 : ZMod 1361244631) ^ 8921) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 242746376 := by rw [factor_4_13]; decide
      have factor_4_15 : (12 : ZMod 1361244631) ^ 35686 = 450371796 := by
        calc
          (12 : ZMod 1361244631) ^ 35686 = (12 : ZMod 1361244631) ^ (17843 + 17843) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 17843 * (12 : ZMod 1361244631) ^ 17843 := by rw [pow_add]
          _ = 450371796 := by rw [factor_4_14]; decide
      have factor_4_16 : (12 : ZMod 1361244631) ^ 71373 = 629574248 := by
        calc
          (12 : ZMod 1361244631) ^ 71373 = (12 : ZMod 1361244631) ^ (35686 + 35686 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 35686 * (12 : ZMod 1361244631) ^ 35686) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 629574248 := by rw [factor_4_15]; decide
      have factor_4_17 : (12 : ZMod 1361244631) ^ 142747 = 842612508 := by
        calc
          (12 : ZMod 1361244631) ^ 142747 = (12 : ZMod 1361244631) ^ (71373 + 71373 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 71373 * (12 : ZMod 1361244631) ^ 71373) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 842612508 := by rw [factor_4_16]; decide
      have factor_4_18 : (12 : ZMod 1361244631) ^ 285495 = 249242498 := by
        calc
          (12 : ZMod 1361244631) ^ 285495 = (12 : ZMod 1361244631) ^ (142747 + 142747 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 142747 * (12 : ZMod 1361244631) ^ 142747) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 249242498 := by rw [factor_4_17]; decide
      have factor_4_19 : (12 : ZMod 1361244631) ^ 570991 = 1179287105 := by
        calc
          (12 : ZMod 1361244631) ^ 570991 = (12 : ZMod 1361244631) ^ (285495 + 285495 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 285495 * (12 : ZMod 1361244631) ^ 285495) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1179287105 := by rw [factor_4_18]; decide
      have factor_4_20 : (12 : ZMod 1361244631) ^ 1141983 = 962085263 := by
        calc
          (12 : ZMod 1361244631) ^ 1141983 = (12 : ZMod 1361244631) ^ (570991 + 570991 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 570991 * (12 : ZMod 1361244631) ^ 570991) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 962085263 := by rw [factor_4_19]; decide
      have factor_4_21 : (12 : ZMod 1361244631) ^ 2283967 = 1163797104 := by
        calc
          (12 : ZMod 1361244631) ^ 2283967 = (12 : ZMod 1361244631) ^ (1141983 + 1141983 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 1141983 * (12 : ZMod 1361244631) ^ 1141983) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1163797104 := by rw [factor_4_20]; decide
      have factor_4_22 : (12 : ZMod 1361244631) ^ 4567935 = 268031145 := by
        calc
          (12 : ZMod 1361244631) ^ 4567935 = (12 : ZMod 1361244631) ^ (2283967 + 2283967 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 2283967 * (12 : ZMod 1361244631) ^ 2283967) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 268031145 := by rw [factor_4_21]; decide
      have factor_4_23 : (12 : ZMod 1361244631) ^ 9135870 = 606714454 := by
        calc
          (12 : ZMod 1361244631) ^ 9135870 = (12 : ZMod 1361244631) ^ (4567935 + 4567935) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 4567935 * (12 : ZMod 1361244631) ^ 4567935 := by rw [pow_add]
          _ = 606714454 := by rw [factor_4_22]; decide
      change (12 : ZMod 1361244631) ^ 9135870 ≠ 1
      rw [factor_4_23]
      decide
    ·
      have factor_5_0 : (12 : ZMod 1361244631) ^ 1 = 12 := by norm_num
      have factor_5_1 : (12 : ZMod 1361244631) ^ 3 = 1728 := by
        calc
          (12 : ZMod 1361244631) ^ 3 = (12 : ZMod 1361244631) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 1 * (12 : ZMod 1361244631) ^ 1) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1728 := by rw [factor_5_0]; decide
      have factor_5_2 : (12 : ZMod 1361244631) ^ 7 = 35831808 := by
        calc
          (12 : ZMod 1361244631) ^ 7 = (12 : ZMod 1361244631) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 3 * (12 : ZMod 1361244631) ^ 3) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 35831808 := by rw [factor_5_1]; decide
      have factor_5_3 : (12 : ZMod 1361244631) ^ 15 = 185221614 := by
        calc
          (12 : ZMod 1361244631) ^ 15 = (12 : ZMod 1361244631) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 7 * (12 : ZMod 1361244631) ^ 7) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 185221614 := by rw [factor_5_2]; decide
      have factor_5_4 : (12 : ZMod 1361244631) ^ 31 = 1265525478 := by
        calc
          (12 : ZMod 1361244631) ^ 31 = (12 : ZMod 1361244631) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 15 * (12 : ZMod 1361244631) ^ 15) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1265525478 := by rw [factor_5_3]; decide
      have factor_5_5 : (12 : ZMod 1361244631) ^ 63 = 181766330 := by
        calc
          (12 : ZMod 1361244631) ^ 63 = (12 : ZMod 1361244631) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 31 * (12 : ZMod 1361244631) ^ 31) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 181766330 := by rw [factor_5_4]; decide
      have factor_5_6 : (12 : ZMod 1361244631) ^ 126 = 232325261 := by
        calc
          (12 : ZMod 1361244631) ^ 126 = (12 : ZMod 1361244631) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 63 * (12 : ZMod 1361244631) ^ 63 := by rw [pow_add]
          _ = 232325261 := by rw [factor_5_5]; decide
      have factor_5_7 : (12 : ZMod 1361244631) ^ 253 = 1352948117 := by
        calc
          (12 : ZMod 1361244631) ^ 253 = (12 : ZMod 1361244631) ^ (126 + 126 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 126 * (12 : ZMod 1361244631) ^ 126) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1352948117 := by rw [factor_5_6]; decide
      have factor_5_8 : (12 : ZMod 1361244631) ^ 506 = 809785681 := by
        calc
          (12 : ZMod 1361244631) ^ 506 = (12 : ZMod 1361244631) ^ (253 + 253) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 253 * (12 : ZMod 1361244631) ^ 253 := by rw [pow_add]
          _ = 809785681 := by rw [factor_5_7]; decide
      have factor_5_9 : (12 : ZMod 1361244631) ^ 1012 = 709116804 := by
        calc
          (12 : ZMod 1361244631) ^ 1012 = (12 : ZMod 1361244631) ^ (506 + 506) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 506 * (12 : ZMod 1361244631) ^ 506 := by rw [pow_add]
          _ = 709116804 := by rw [factor_5_8]; decide
      have factor_5_10 : (12 : ZMod 1361244631) ^ 2025 = 901364928 := by
        calc
          (12 : ZMod 1361244631) ^ 2025 = (12 : ZMod 1361244631) ^ (1012 + 1012 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 1012 * (12 : ZMod 1361244631) ^ 1012) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 901364928 := by rw [factor_5_9]; decide
      have factor_5_11 : (12 : ZMod 1361244631) ^ 4050 = 650601236 := by
        calc
          (12 : ZMod 1361244631) ^ 4050 = (12 : ZMod 1361244631) ^ (2025 + 2025) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 2025 * (12 : ZMod 1361244631) ^ 2025 := by rw [pow_add]
          _ = 650601236 := by rw [factor_5_10]; decide
      have factor_5_12 : (12 : ZMod 1361244631) ^ 8101 = 52969304 := by
        calc
          (12 : ZMod 1361244631) ^ 8101 = (12 : ZMod 1361244631) ^ (4050 + 4050 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 4050 * (12 : ZMod 1361244631) ^ 4050) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 52969304 := by rw [factor_5_11]; decide
      have factor_5_13 : (12 : ZMod 1361244631) ^ 16203 = 1186542756 := by
        calc
          (12 : ZMod 1361244631) ^ 16203 = (12 : ZMod 1361244631) ^ (8101 + 8101 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 8101 * (12 : ZMod 1361244631) ^ 8101) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1186542756 := by rw [factor_5_12]; decide
      have factor_5_14 : (12 : ZMod 1361244631) ^ 32407 = 1059338609 := by
        calc
          (12 : ZMod 1361244631) ^ 32407 = (12 : ZMod 1361244631) ^ (16203 + 16203 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 16203 * (12 : ZMod 1361244631) ^ 16203) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 1059338609 := by rw [factor_5_13]; decide
      have factor_5_15 : (12 : ZMod 1361244631) ^ 64815 = 448307055 := by
        calc
          (12 : ZMod 1361244631) ^ 64815 = (12 : ZMod 1361244631) ^ (32407 + 32407 + 1) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = ((12 : ZMod 1361244631) ^ 32407 * (12 : ZMod 1361244631) ^ 32407) * (12 : ZMod 1361244631) := by rw [pow_succ, pow_add]
          _ = 448307055 := by rw [factor_5_14]; decide
      have factor_5_16 : (12 : ZMod 1361244631) ^ 129630 = 1218128860 := by
        calc
          (12 : ZMod 1361244631) ^ 129630 = (12 : ZMod 1361244631) ^ (64815 + 64815) :=
            congrArg (fun n : ℕ => (12 : ZMod 1361244631) ^ n) (by norm_num)
          _ = (12 : ZMod 1361244631) ^ 64815 * (12 : ZMod 1361244631) ^ 64815 := by rw [pow_add]
          _ = 1218128860 := by rw [factor_5_15]; decide
      change (12 : ZMod 1361244631) ^ 129630 ≠ 1
      rw [factor_5_16]
      decide

#print axioms prime_lucas_1361244631

end TotientTailPeriodKiller
end Erdos249257
