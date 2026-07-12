import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_4579662077 : Nat.Prime 4579662077 := by
  apply lucas_primality 4579662077 (2 : ZMod 4579662077)
  ·
      have fermat_0 : (2 : ZMod 4579662077) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 4579662077) ^ 2 = 4 := by
        calc
          (2 : ZMod 4579662077) ^ 2 = (2 : ZMod 4579662077) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 1 * (2 : ZMod 4579662077) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 4579662077) ^ 4 = 16 := by
        calc
          (2 : ZMod 4579662077) ^ 4 = (2 : ZMod 4579662077) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 2 * (2 : ZMod 4579662077) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 4579662077) ^ 8 = 256 := by
        calc
          (2 : ZMod 4579662077) ^ 8 = (2 : ZMod 4579662077) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 4 * (2 : ZMod 4579662077) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 4579662077) ^ 17 = 131072 := by
        calc
          (2 : ZMod 4579662077) ^ 17 = (2 : ZMod 4579662077) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 8 * (2 : ZMod 4579662077) ^ 8) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 4579662077) ^ 34 = 3440882953 := by
        calc
          (2 : ZMod 4579662077) ^ 34 = (2 : ZMod 4579662077) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 17 * (2 : ZMod 4579662077) ^ 17 := by rw [pow_add]
          _ = 3440882953 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 4579662077) ^ 68 = 2223753768 := by
        calc
          (2 : ZMod 4579662077) ^ 68 = (2 : ZMod 4579662077) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 34 * (2 : ZMod 4579662077) ^ 34 := by rw [pow_add]
          _ = 2223753768 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 4579662077) ^ 136 = 504223621 := by
        calc
          (2 : ZMod 4579662077) ^ 136 = (2 : ZMod 4579662077) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 68 * (2 : ZMod 4579662077) ^ 68 := by rw [pow_add]
          _ = 504223621 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 4579662077) ^ 272 = 3901549154 := by
        calc
          (2 : ZMod 4579662077) ^ 272 = (2 : ZMod 4579662077) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 136 * (2 : ZMod 4579662077) ^ 136 := by rw [pow_add]
          _ = 3901549154 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 4579662077) ^ 545 = 3162236315 := by
        calc
          (2 : ZMod 4579662077) ^ 545 = (2 : ZMod 4579662077) ^ (272 + 272 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 272 * (2 : ZMod 4579662077) ^ 272) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 3162236315 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 4579662077) ^ 1091 = 4552823354 := by
        calc
          (2 : ZMod 4579662077) ^ 1091 = (2 : ZMod 4579662077) ^ (545 + 545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 545 * (2 : ZMod 4579662077) ^ 545) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 4552823354 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 4579662077) ^ 2183 = 645655414 := by
        calc
          (2 : ZMod 4579662077) ^ 2183 = (2 : ZMod 4579662077) ^ (1091 + 1091 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 1091 * (2 : ZMod 4579662077) ^ 1091) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 645655414 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 4579662077) ^ 4367 = 2635547628 := by
        calc
          (2 : ZMod 4579662077) ^ 4367 = (2 : ZMod 4579662077) ^ (2183 + 2183 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 2183 * (2 : ZMod 4579662077) ^ 2183) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2635547628 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 4579662077) ^ 8735 = 100976061 := by
        calc
          (2 : ZMod 4579662077) ^ 8735 = (2 : ZMod 4579662077) ^ (4367 + 4367 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 4367 * (2 : ZMod 4579662077) ^ 4367) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 100976061 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 4579662077) ^ 17470 = 667180844 := by
        calc
          (2 : ZMod 4579662077) ^ 17470 = (2 : ZMod 4579662077) ^ (8735 + 8735) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 8735 * (2 : ZMod 4579662077) ^ 8735 := by rw [pow_add]
          _ = 667180844 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 4579662077) ^ 34940 = 2725912860 := by
        calc
          (2 : ZMod 4579662077) ^ 34940 = (2 : ZMod 4579662077) ^ (17470 + 17470) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 17470 * (2 : ZMod 4579662077) ^ 17470 := by rw [pow_add]
          _ = 2725912860 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 4579662077) ^ 69880 = 320629703 := by
        calc
          (2 : ZMod 4579662077) ^ 69880 = (2 : ZMod 4579662077) ^ (34940 + 34940) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 34940 * (2 : ZMod 4579662077) ^ 34940 := by rw [pow_add]
          _ = 320629703 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 4579662077) ^ 139760 = 3958518531 := by
        calc
          (2 : ZMod 4579662077) ^ 139760 = (2 : ZMod 4579662077) ^ (69880 + 69880) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 69880 * (2 : ZMod 4579662077) ^ 69880 := by rw [pow_add]
          _ = 3958518531 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 4579662077) ^ 279520 = 3438937790 := by
        calc
          (2 : ZMod 4579662077) ^ 279520 = (2 : ZMod 4579662077) ^ (139760 + 139760) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 139760 * (2 : ZMod 4579662077) ^ 139760 := by rw [pow_add]
          _ = 3438937790 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 4579662077) ^ 559040 = 1992563746 := by
        calc
          (2 : ZMod 4579662077) ^ 559040 = (2 : ZMod 4579662077) ^ (279520 + 279520) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 279520 * (2 : ZMod 4579662077) ^ 279520 := by rw [pow_add]
          _ = 1992563746 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 4579662077) ^ 1118081 = 3100502426 := by
        calc
          (2 : ZMod 4579662077) ^ 1118081 = (2 : ZMod 4579662077) ^ (559040 + 559040 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 559040 * (2 : ZMod 4579662077) ^ 559040) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 3100502426 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 4579662077) ^ 2236163 = 2945723745 := by
        calc
          (2 : ZMod 4579662077) ^ 2236163 = (2 : ZMod 4579662077) ^ (1118081 + 1118081 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 1118081 * (2 : ZMod 4579662077) ^ 1118081) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2945723745 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 4579662077) ^ 4472326 = 3677341929 := by
        calc
          (2 : ZMod 4579662077) ^ 4472326 = (2 : ZMod 4579662077) ^ (2236163 + 2236163) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 2236163 * (2 : ZMod 4579662077) ^ 2236163 := by rw [pow_add]
          _ = 3677341929 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 4579662077) ^ 8944652 = 1245693132 := by
        calc
          (2 : ZMod 4579662077) ^ 8944652 = (2 : ZMod 4579662077) ^ (4472326 + 4472326) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 4472326 * (2 : ZMod 4579662077) ^ 4472326 := by rw [pow_add]
          _ = 1245693132 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 4579662077) ^ 17889304 = 3847919936 := by
        calc
          (2 : ZMod 4579662077) ^ 17889304 = (2 : ZMod 4579662077) ^ (8944652 + 8944652) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 8944652 * (2 : ZMod 4579662077) ^ 8944652 := by rw [pow_add]
          _ = 3847919936 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 4579662077) ^ 35778609 = 4253419015 := by
        calc
          (2 : ZMod 4579662077) ^ 35778609 = (2 : ZMod 4579662077) ^ (17889304 + 17889304 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 17889304 * (2 : ZMod 4579662077) ^ 17889304) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 4253419015 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 4579662077) ^ 71557219 = 2777700504 := by
        calc
          (2 : ZMod 4579662077) ^ 71557219 = (2 : ZMod 4579662077) ^ (35778609 + 35778609 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 35778609 * (2 : ZMod 4579662077) ^ 35778609) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2777700504 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 4579662077) ^ 143114439 = 1969501107 := by
        calc
          (2 : ZMod 4579662077) ^ 143114439 = (2 : ZMod 4579662077) ^ (71557219 + 71557219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 71557219 * (2 : ZMod 4579662077) ^ 71557219) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1969501107 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 4579662077) ^ 286228879 = 2209940060 := by
        calc
          (2 : ZMod 4579662077) ^ 286228879 = (2 : ZMod 4579662077) ^ (143114439 + 143114439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 143114439 * (2 : ZMod 4579662077) ^ 143114439) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2209940060 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 4579662077) ^ 572457759 = 4351893782 := by
        calc
          (2 : ZMod 4579662077) ^ 572457759 = (2 : ZMod 4579662077) ^ (286228879 + 286228879 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 286228879 * (2 : ZMod 4579662077) ^ 286228879) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 4351893782 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 4579662077) ^ 1144915519 = 455536589 := by
        calc
          (2 : ZMod 4579662077) ^ 1144915519 = (2 : ZMod 4579662077) ^ (572457759 + 572457759 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 572457759 * (2 : ZMod 4579662077) ^ 572457759) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 455536589 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 4579662077) ^ 2289831038 = 4579662076 := by
        calc
          (2 : ZMod 4579662077) ^ 2289831038 = (2 : ZMod 4579662077) ^ (1144915519 + 1144915519) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 1144915519 * (2 : ZMod 4579662077) ^ 1144915519 := by rw [pow_add]
          _ = 4579662076 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 4579662077) ^ 4579662076 = 1 := by
        calc
          (2 : ZMod 4579662077) ^ 4579662076 = (2 : ZMod 4579662077) ^ (2289831038 + 2289831038) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 2289831038 * (2 : ZMod 4579662077) ^ 2289831038 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (5281, 1), (19709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (5281, 1), (19709, 1)] : List FactorBlock).map factorBlockValue).prod = 4579662077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 4579662077) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 4579662077) ^ 2 = 4 := by
        calc
          (2 : ZMod 4579662077) ^ 2 = (2 : ZMod 4579662077) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 1 * (2 : ZMod 4579662077) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 4579662077) ^ 4 = 16 := by
        calc
          (2 : ZMod 4579662077) ^ 4 = (2 : ZMod 4579662077) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 2 * (2 : ZMod 4579662077) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 4579662077) ^ 8 = 256 := by
        calc
          (2 : ZMod 4579662077) ^ 8 = (2 : ZMod 4579662077) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 4 * (2 : ZMod 4579662077) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 4579662077) ^ 17 = 131072 := by
        calc
          (2 : ZMod 4579662077) ^ 17 = (2 : ZMod 4579662077) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 8 * (2 : ZMod 4579662077) ^ 8) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 4579662077) ^ 34 = 3440882953 := by
        calc
          (2 : ZMod 4579662077) ^ 34 = (2 : ZMod 4579662077) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 17 * (2 : ZMod 4579662077) ^ 17 := by rw [pow_add]
          _ = 3440882953 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 4579662077) ^ 68 = 2223753768 := by
        calc
          (2 : ZMod 4579662077) ^ 68 = (2 : ZMod 4579662077) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 34 * (2 : ZMod 4579662077) ^ 34 := by rw [pow_add]
          _ = 2223753768 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 4579662077) ^ 136 = 504223621 := by
        calc
          (2 : ZMod 4579662077) ^ 136 = (2 : ZMod 4579662077) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 68 * (2 : ZMod 4579662077) ^ 68 := by rw [pow_add]
          _ = 504223621 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 4579662077) ^ 272 = 3901549154 := by
        calc
          (2 : ZMod 4579662077) ^ 272 = (2 : ZMod 4579662077) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 136 * (2 : ZMod 4579662077) ^ 136 := by rw [pow_add]
          _ = 3901549154 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 4579662077) ^ 545 = 3162236315 := by
        calc
          (2 : ZMod 4579662077) ^ 545 = (2 : ZMod 4579662077) ^ (272 + 272 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 272 * (2 : ZMod 4579662077) ^ 272) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 3162236315 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 4579662077) ^ 1091 = 4552823354 := by
        calc
          (2 : ZMod 4579662077) ^ 1091 = (2 : ZMod 4579662077) ^ (545 + 545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 545 * (2 : ZMod 4579662077) ^ 545) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 4552823354 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 4579662077) ^ 2183 = 645655414 := by
        calc
          (2 : ZMod 4579662077) ^ 2183 = (2 : ZMod 4579662077) ^ (1091 + 1091 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 1091 * (2 : ZMod 4579662077) ^ 1091) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 645655414 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 4579662077) ^ 4367 = 2635547628 := by
        calc
          (2 : ZMod 4579662077) ^ 4367 = (2 : ZMod 4579662077) ^ (2183 + 2183 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 2183 * (2 : ZMod 4579662077) ^ 2183) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2635547628 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 4579662077) ^ 8735 = 100976061 := by
        calc
          (2 : ZMod 4579662077) ^ 8735 = (2 : ZMod 4579662077) ^ (4367 + 4367 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 4367 * (2 : ZMod 4579662077) ^ 4367) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 100976061 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 4579662077) ^ 17470 = 667180844 := by
        calc
          (2 : ZMod 4579662077) ^ 17470 = (2 : ZMod 4579662077) ^ (8735 + 8735) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 8735 * (2 : ZMod 4579662077) ^ 8735 := by rw [pow_add]
          _ = 667180844 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 4579662077) ^ 34940 = 2725912860 := by
        calc
          (2 : ZMod 4579662077) ^ 34940 = (2 : ZMod 4579662077) ^ (17470 + 17470) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 17470 * (2 : ZMod 4579662077) ^ 17470 := by rw [pow_add]
          _ = 2725912860 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 4579662077) ^ 69880 = 320629703 := by
        calc
          (2 : ZMod 4579662077) ^ 69880 = (2 : ZMod 4579662077) ^ (34940 + 34940) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 34940 * (2 : ZMod 4579662077) ^ 34940 := by rw [pow_add]
          _ = 320629703 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 4579662077) ^ 139760 = 3958518531 := by
        calc
          (2 : ZMod 4579662077) ^ 139760 = (2 : ZMod 4579662077) ^ (69880 + 69880) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 69880 * (2 : ZMod 4579662077) ^ 69880 := by rw [pow_add]
          _ = 3958518531 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 4579662077) ^ 279520 = 3438937790 := by
        calc
          (2 : ZMod 4579662077) ^ 279520 = (2 : ZMod 4579662077) ^ (139760 + 139760) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 139760 * (2 : ZMod 4579662077) ^ 139760 := by rw [pow_add]
          _ = 3438937790 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 4579662077) ^ 559040 = 1992563746 := by
        calc
          (2 : ZMod 4579662077) ^ 559040 = (2 : ZMod 4579662077) ^ (279520 + 279520) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 279520 * (2 : ZMod 4579662077) ^ 279520 := by rw [pow_add]
          _ = 1992563746 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 4579662077) ^ 1118081 = 3100502426 := by
        calc
          (2 : ZMod 4579662077) ^ 1118081 = (2 : ZMod 4579662077) ^ (559040 + 559040 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 559040 * (2 : ZMod 4579662077) ^ 559040) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 3100502426 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 4579662077) ^ 2236163 = 2945723745 := by
        calc
          (2 : ZMod 4579662077) ^ 2236163 = (2 : ZMod 4579662077) ^ (1118081 + 1118081 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 1118081 * (2 : ZMod 4579662077) ^ 1118081) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2945723745 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 4579662077) ^ 4472326 = 3677341929 := by
        calc
          (2 : ZMod 4579662077) ^ 4472326 = (2 : ZMod 4579662077) ^ (2236163 + 2236163) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 2236163 * (2 : ZMod 4579662077) ^ 2236163 := by rw [pow_add]
          _ = 3677341929 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 4579662077) ^ 8944652 = 1245693132 := by
        calc
          (2 : ZMod 4579662077) ^ 8944652 = (2 : ZMod 4579662077) ^ (4472326 + 4472326) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 4472326 * (2 : ZMod 4579662077) ^ 4472326 := by rw [pow_add]
          _ = 1245693132 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 4579662077) ^ 17889304 = 3847919936 := by
        calc
          (2 : ZMod 4579662077) ^ 17889304 = (2 : ZMod 4579662077) ^ (8944652 + 8944652) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 8944652 * (2 : ZMod 4579662077) ^ 8944652 := by rw [pow_add]
          _ = 3847919936 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 4579662077) ^ 35778609 = 4253419015 := by
        calc
          (2 : ZMod 4579662077) ^ 35778609 = (2 : ZMod 4579662077) ^ (17889304 + 17889304 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 17889304 * (2 : ZMod 4579662077) ^ 17889304) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 4253419015 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 4579662077) ^ 71557219 = 2777700504 := by
        calc
          (2 : ZMod 4579662077) ^ 71557219 = (2 : ZMod 4579662077) ^ (35778609 + 35778609 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 35778609 * (2 : ZMod 4579662077) ^ 35778609) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2777700504 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 4579662077) ^ 143114439 = 1969501107 := by
        calc
          (2 : ZMod 4579662077) ^ 143114439 = (2 : ZMod 4579662077) ^ (71557219 + 71557219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 71557219 * (2 : ZMod 4579662077) ^ 71557219) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1969501107 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 4579662077) ^ 286228879 = 2209940060 := by
        calc
          (2 : ZMod 4579662077) ^ 286228879 = (2 : ZMod 4579662077) ^ (143114439 + 143114439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 143114439 * (2 : ZMod 4579662077) ^ 143114439) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2209940060 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 4579662077) ^ 572457759 = 4351893782 := by
        calc
          (2 : ZMod 4579662077) ^ 572457759 = (2 : ZMod 4579662077) ^ (286228879 + 286228879 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 286228879 * (2 : ZMod 4579662077) ^ 286228879) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 4351893782 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 4579662077) ^ 1144915519 = 455536589 := by
        calc
          (2 : ZMod 4579662077) ^ 1144915519 = (2 : ZMod 4579662077) ^ (572457759 + 572457759 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 572457759 * (2 : ZMod 4579662077) ^ 572457759) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 455536589 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 4579662077) ^ 2289831038 = 4579662076 := by
        calc
          (2 : ZMod 4579662077) ^ 2289831038 = (2 : ZMod 4579662077) ^ (1144915519 + 1144915519) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 1144915519 * (2 : ZMod 4579662077) ^ 1144915519 := by rw [pow_add]
          _ = 4579662076 := by rw [factor_0_30]; decide
      change (2 : ZMod 4579662077) ^ 2289831038 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (2 : ZMod 4579662077) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 4579662077) ^ 3 = 8 := by
        calc
          (2 : ZMod 4579662077) ^ 3 = (2 : ZMod 4579662077) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 1 * (2 : ZMod 4579662077) ^ 1) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 4579662077) ^ 6 = 64 := by
        calc
          (2 : ZMod 4579662077) ^ 6 = (2 : ZMod 4579662077) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 3 * (2 : ZMod 4579662077) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 4579662077) ^ 12 = 4096 := by
        calc
          (2 : ZMod 4579662077) ^ 12 = (2 : ZMod 4579662077) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 6 * (2 : ZMod 4579662077) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 4579662077) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 4579662077) ^ 24 = (2 : ZMod 4579662077) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 12 * (2 : ZMod 4579662077) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 4579662077) ^ 49 = 4151930241 := by
        calc
          (2 : ZMod 4579662077) ^ 49 = (2 : ZMod 4579662077) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 24 * (2 : ZMod 4579662077) ^ 24) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 4151930241 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 4579662077) ^ 99 = 664261892 := by
        calc
          (2 : ZMod 4579662077) ^ 99 = (2 : ZMod 4579662077) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 49 * (2 : ZMod 4579662077) ^ 49) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 664261892 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 4579662077) ^ 198 = 1018874313 := by
        calc
          (2 : ZMod 4579662077) ^ 198 = (2 : ZMod 4579662077) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 99 * (2 : ZMod 4579662077) ^ 99 := by rw [pow_add]
          _ = 1018874313 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 4579662077) ^ 397 = 2664796911 := by
        calc
          (2 : ZMod 4579662077) ^ 397 = (2 : ZMod 4579662077) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 198 * (2 : ZMod 4579662077) ^ 198) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2664796911 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 4579662077) ^ 794 = 409657212 := by
        calc
          (2 : ZMod 4579662077) ^ 794 = (2 : ZMod 4579662077) ^ (397 + 397) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 397 * (2 : ZMod 4579662077) ^ 397 := by rw [pow_add]
          _ = 409657212 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 4579662077) ^ 1588 = 2793587143 := by
        calc
          (2 : ZMod 4579662077) ^ 1588 = (2 : ZMod 4579662077) ^ (794 + 794) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 794 * (2 : ZMod 4579662077) ^ 794 := by rw [pow_add]
          _ = 2793587143 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 4579662077) ^ 3176 = 2831020214 := by
        calc
          (2 : ZMod 4579662077) ^ 3176 = (2 : ZMod 4579662077) ^ (1588 + 1588) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 1588 * (2 : ZMod 4579662077) ^ 1588 := by rw [pow_add]
          _ = 2831020214 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 4579662077) ^ 6352 = 1634337699 := by
        calc
          (2 : ZMod 4579662077) ^ 6352 = (2 : ZMod 4579662077) ^ (3176 + 3176) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 3176 * (2 : ZMod 4579662077) ^ 3176 := by rw [pow_add]
          _ = 1634337699 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 4579662077) ^ 12705 = 724221226 := by
        calc
          (2 : ZMod 4579662077) ^ 12705 = (2 : ZMod 4579662077) ^ (6352 + 6352 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 6352 * (2 : ZMod 4579662077) ^ 6352) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 724221226 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 4579662077) ^ 25410 = 1221458129 := by
        calc
          (2 : ZMod 4579662077) ^ 25410 = (2 : ZMod 4579662077) ^ (12705 + 12705) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 12705 * (2 : ZMod 4579662077) ^ 12705 := by rw [pow_add]
          _ = 1221458129 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 4579662077) ^ 50821 = 2223194361 := by
        calc
          (2 : ZMod 4579662077) ^ 50821 = (2 : ZMod 4579662077) ^ (25410 + 25410 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 25410 * (2 : ZMod 4579662077) ^ 25410) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2223194361 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 4579662077) ^ 101643 = 1427604420 := by
        calc
          (2 : ZMod 4579662077) ^ 101643 = (2 : ZMod 4579662077) ^ (50821 + 50821 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 50821 * (2 : ZMod 4579662077) ^ 50821) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1427604420 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 4579662077) ^ 203287 = 1096374204 := by
        calc
          (2 : ZMod 4579662077) ^ 203287 = (2 : ZMod 4579662077) ^ (101643 + 101643 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 101643 * (2 : ZMod 4579662077) ^ 101643) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1096374204 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 4579662077) ^ 406575 = 2215919274 := by
        calc
          (2 : ZMod 4579662077) ^ 406575 = (2 : ZMod 4579662077) ^ (203287 + 203287 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 203287 * (2 : ZMod 4579662077) ^ 203287) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2215919274 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 4579662077) ^ 813150 = 1705134874 := by
        calc
          (2 : ZMod 4579662077) ^ 813150 = (2 : ZMod 4579662077) ^ (406575 + 406575) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 406575 * (2 : ZMod 4579662077) ^ 406575 := by rw [pow_add]
          _ = 1705134874 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 4579662077) ^ 1626300 = 347870039 := by
        calc
          (2 : ZMod 4579662077) ^ 1626300 = (2 : ZMod 4579662077) ^ (813150 + 813150) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 813150 * (2 : ZMod 4579662077) ^ 813150 := by rw [pow_add]
          _ = 347870039 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 4579662077) ^ 3252600 = 853453896 := by
        calc
          (2 : ZMod 4579662077) ^ 3252600 = (2 : ZMod 4579662077) ^ (1626300 + 1626300) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 1626300 * (2 : ZMod 4579662077) ^ 1626300 := by rw [pow_add]
          _ = 853453896 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 4579662077) ^ 6505201 = 574671102 := by
        calc
          (2 : ZMod 4579662077) ^ 6505201 = (2 : ZMod 4579662077) ^ (3252600 + 3252600 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 3252600 * (2 : ZMod 4579662077) ^ 3252600) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 574671102 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 4579662077) ^ 13010403 = 2301098558 := by
        calc
          (2 : ZMod 4579662077) ^ 13010403 = (2 : ZMod 4579662077) ^ (6505201 + 6505201 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 6505201 * (2 : ZMod 4579662077) ^ 6505201) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2301098558 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 4579662077) ^ 26020807 = 1496999611 := by
        calc
          (2 : ZMod 4579662077) ^ 26020807 = (2 : ZMod 4579662077) ^ (13010403 + 13010403 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 13010403 * (2 : ZMod 4579662077) ^ 13010403) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1496999611 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 4579662077) ^ 52041614 = 1779288696 := by
        calc
          (2 : ZMod 4579662077) ^ 52041614 = (2 : ZMod 4579662077) ^ (26020807 + 26020807) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 26020807 * (2 : ZMod 4579662077) ^ 26020807 := by rw [pow_add]
          _ = 1779288696 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 4579662077) ^ 104083229 = 353405814 := by
        calc
          (2 : ZMod 4579662077) ^ 104083229 = (2 : ZMod 4579662077) ^ (52041614 + 52041614 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 52041614 * (2 : ZMod 4579662077) ^ 52041614) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 353405814 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 4579662077) ^ 208166458 = 4500177380 := by
        calc
          (2 : ZMod 4579662077) ^ 208166458 = (2 : ZMod 4579662077) ^ (104083229 + 104083229) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 104083229 * (2 : ZMod 4579662077) ^ 104083229 := by rw [pow_add]
          _ = 4500177380 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 4579662077) ^ 416332916 = 3774463460 := by
        calc
          (2 : ZMod 4579662077) ^ 416332916 = (2 : ZMod 4579662077) ^ (208166458 + 208166458) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 208166458 * (2 : ZMod 4579662077) ^ 208166458 := by rw [pow_add]
          _ = 3774463460 := by rw [factor_1_27]; decide
      change (2 : ZMod 4579662077) ^ 416332916 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (2 : ZMod 4579662077) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 4579662077) ^ 3 = 8 := by
        calc
          (2 : ZMod 4579662077) ^ 3 = (2 : ZMod 4579662077) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 1 * (2 : ZMod 4579662077) ^ 1) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 4579662077) ^ 6 = 64 := by
        calc
          (2 : ZMod 4579662077) ^ 6 = (2 : ZMod 4579662077) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 3 * (2 : ZMod 4579662077) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 4579662077) ^ 13 = 8192 := by
        calc
          (2 : ZMod 4579662077) ^ 13 = (2 : ZMod 4579662077) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 6 * (2 : ZMod 4579662077) ^ 6) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 4579662077) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 4579662077) ^ 26 = (2 : ZMod 4579662077) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 13 * (2 : ZMod 4579662077) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 4579662077) ^ 52 = 1157807389 := by
        calc
          (2 : ZMod 4579662077) ^ 52 = (2 : ZMod 4579662077) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 26 * (2 : ZMod 4579662077) ^ 26 := by rw [pow_add]
          _ = 1157807389 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 4579662077) ^ 105 = 1295802395 := by
        calc
          (2 : ZMod 4579662077) ^ 105 = (2 : ZMod 4579662077) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 52 * (2 : ZMod 4579662077) ^ 52) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1295802395 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 4579662077) ^ 211 = 2474067802 := by
        calc
          (2 : ZMod 4579662077) ^ 211 = (2 : ZMod 4579662077) ^ (105 + 105 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 105 * (2 : ZMod 4579662077) ^ 105) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2474067802 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 4579662077) ^ 423 = 3422745638 := by
        calc
          (2 : ZMod 4579662077) ^ 423 = (2 : ZMod 4579662077) ^ (211 + 211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 211 * (2 : ZMod 4579662077) ^ 211) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 3422745638 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 4579662077) ^ 846 = 4010366122 := by
        calc
          (2 : ZMod 4579662077) ^ 846 = (2 : ZMod 4579662077) ^ (423 + 423) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 423 * (2 : ZMod 4579662077) ^ 423 := by rw [pow_add]
          _ = 4010366122 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 4579662077) ^ 1693 = 1931519519 := by
        calc
          (2 : ZMod 4579662077) ^ 1693 = (2 : ZMod 4579662077) ^ (846 + 846 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 846 * (2 : ZMod 4579662077) ^ 846) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1931519519 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 4579662077) ^ 3387 = 3741858615 := by
        calc
          (2 : ZMod 4579662077) ^ 3387 = (2 : ZMod 4579662077) ^ (1693 + 1693 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 1693 * (2 : ZMod 4579662077) ^ 1693) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 3741858615 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 4579662077) ^ 6774 = 1247206384 := by
        calc
          (2 : ZMod 4579662077) ^ 6774 = (2 : ZMod 4579662077) ^ (3387 + 3387) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 3387 * (2 : ZMod 4579662077) ^ 3387 := by rw [pow_add]
          _ = 1247206384 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 4579662077) ^ 13549 = 24872055 := by
        calc
          (2 : ZMod 4579662077) ^ 13549 = (2 : ZMod 4579662077) ^ (6774 + 6774 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 6774 * (2 : ZMod 4579662077) ^ 6774) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 24872055 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 4579662077) ^ 27099 = 1312785807 := by
        calc
          (2 : ZMod 4579662077) ^ 27099 = (2 : ZMod 4579662077) ^ (13549 + 13549 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 13549 * (2 : ZMod 4579662077) ^ 13549) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1312785807 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 4579662077) ^ 54199 = 2557899281 := by
        calc
          (2 : ZMod 4579662077) ^ 54199 = (2 : ZMod 4579662077) ^ (27099 + 27099 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 27099 * (2 : ZMod 4579662077) ^ 27099) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2557899281 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 4579662077) ^ 108399 = 286711460 := by
        calc
          (2 : ZMod 4579662077) ^ 108399 = (2 : ZMod 4579662077) ^ (54199 + 54199 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 54199 * (2 : ZMod 4579662077) ^ 54199) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 286711460 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 4579662077) ^ 216799 = 3328740788 := by
        calc
          (2 : ZMod 4579662077) ^ 216799 = (2 : ZMod 4579662077) ^ (108399 + 108399 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 108399 * (2 : ZMod 4579662077) ^ 108399) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 3328740788 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 4579662077) ^ 433598 = 4198245022 := by
        calc
          (2 : ZMod 4579662077) ^ 433598 = (2 : ZMod 4579662077) ^ (216799 + 216799) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 216799 * (2 : ZMod 4579662077) ^ 216799 := by rw [pow_add]
          _ = 4198245022 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 4579662077) ^ 867196 = 31985078 := by
        calc
          (2 : ZMod 4579662077) ^ 867196 = (2 : ZMod 4579662077) ^ (433598 + 433598) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 433598 * (2 : ZMod 4579662077) ^ 433598 := by rw [pow_add]
          _ = 31985078 := by rw [factor_2_18]; decide
      change (2 : ZMod 4579662077) ^ 867196 ≠ 1
      rw [factor_2_19]
      decide
    ·
      have factor_3_0 : (2 : ZMod 4579662077) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 4579662077) ^ 3 = 8 := by
        calc
          (2 : ZMod 4579662077) ^ 3 = (2 : ZMod 4579662077) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 1 * (2 : ZMod 4579662077) ^ 1) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 4579662077) ^ 7 = 128 := by
        calc
          (2 : ZMod 4579662077) ^ 7 = (2 : ZMod 4579662077) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 3 * (2 : ZMod 4579662077) ^ 3) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 4579662077) ^ 14 = 16384 := by
        calc
          (2 : ZMod 4579662077) ^ 14 = (2 : ZMod 4579662077) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 7 * (2 : ZMod 4579662077) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 4579662077) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 4579662077) ^ 28 = (2 : ZMod 4579662077) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 14 * (2 : ZMod 4579662077) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 4579662077) ^ 56 = 206269916 := by
        calc
          (2 : ZMod 4579662077) ^ 56 = (2 : ZMod 4579662077) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 28 * (2 : ZMod 4579662077) ^ 28 := by rw [pow_add]
          _ = 206269916 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 4579662077) ^ 113 = 1989743576 := by
        calc
          (2 : ZMod 4579662077) ^ 113 = (2 : ZMod 4579662077) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 56 * (2 : ZMod 4579662077) ^ 56) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1989743576 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 4579662077) ^ 226 = 1075648882 := by
        calc
          (2 : ZMod 4579662077) ^ 226 = (2 : ZMod 4579662077) ^ (113 + 113) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 113 * (2 : ZMod 4579662077) ^ 113 := by rw [pow_add]
          _ = 1075648882 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 4579662077) ^ 453 = 1896915893 := by
        calc
          (2 : ZMod 4579662077) ^ 453 = (2 : ZMod 4579662077) ^ (226 + 226 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 226 * (2 : ZMod 4579662077) ^ 226) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 1896915893 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 4579662077) ^ 907 = 2485877392 := by
        calc
          (2 : ZMod 4579662077) ^ 907 = (2 : ZMod 4579662077) ^ (453 + 453 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 453 * (2 : ZMod 4579662077) ^ 453) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2485877392 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 4579662077) ^ 1815 = 2074061523 := by
        calc
          (2 : ZMod 4579662077) ^ 1815 = (2 : ZMod 4579662077) ^ (907 + 907 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 907 * (2 : ZMod 4579662077) ^ 907) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 2074061523 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 4579662077) ^ 3630 = 4372373381 := by
        calc
          (2 : ZMod 4579662077) ^ 3630 = (2 : ZMod 4579662077) ^ (1815 + 1815) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 1815 * (2 : ZMod 4579662077) ^ 1815 := by rw [pow_add]
          _ = 4372373381 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 4579662077) ^ 7261 = 3812366450 := by
        calc
          (2 : ZMod 4579662077) ^ 7261 = (2 : ZMod 4579662077) ^ (3630 + 3630 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 3630 * (2 : ZMod 4579662077) ^ 3630) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 3812366450 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 4579662077) ^ 14522 = 3788380906 := by
        calc
          (2 : ZMod 4579662077) ^ 14522 = (2 : ZMod 4579662077) ^ (7261 + 7261) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 7261 * (2 : ZMod 4579662077) ^ 7261 := by rw [pow_add]
          _ = 3788380906 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 4579662077) ^ 29045 = 3490339744 := by
        calc
          (2 : ZMod 4579662077) ^ 29045 = (2 : ZMod 4579662077) ^ (14522 + 14522 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 14522 * (2 : ZMod 4579662077) ^ 14522) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 3490339744 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 4579662077) ^ 58091 = 4469266218 := by
        calc
          (2 : ZMod 4579662077) ^ 58091 = (2 : ZMod 4579662077) ^ (29045 + 29045 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = ((2 : ZMod 4579662077) ^ 29045 * (2 : ZMod 4579662077) ^ 29045) * (2 : ZMod 4579662077) := by rw [pow_succ, pow_add]
          _ = 4469266218 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 4579662077) ^ 116182 = 93884022 := by
        calc
          (2 : ZMod 4579662077) ^ 116182 = (2 : ZMod 4579662077) ^ (58091 + 58091) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 58091 * (2 : ZMod 4579662077) ^ 58091 := by rw [pow_add]
          _ = 93884022 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 4579662077) ^ 232364 = 4187357127 := by
        calc
          (2 : ZMod 4579662077) ^ 232364 = (2 : ZMod 4579662077) ^ (116182 + 116182) :=
            congrArg (fun n : ℕ => (2 : ZMod 4579662077) ^ n) (by norm_num)
          _ = (2 : ZMod 4579662077) ^ 116182 * (2 : ZMod 4579662077) ^ 116182 := by rw [pow_add]
          _ = 4187357127 := by rw [factor_3_16]; decide
      change (2 : ZMod 4579662077) ^ 232364 ≠ 1
      rw [factor_3_17]
      decide

#print axioms prime_lucas_4579662077

end TotientTailPeriodKiller
end Erdos249257
