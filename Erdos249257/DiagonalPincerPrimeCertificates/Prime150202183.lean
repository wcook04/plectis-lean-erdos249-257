import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_150202183 : Nat.Prime 150202183 := by
  apply lucas_primality 150202183 (3 : ZMod 150202183)
  ·
      have fermat_0 : (3 : ZMod 150202183) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 150202183) ^ 2 = 9 := by
        calc
          (3 : ZMod 150202183) ^ 2 = (3 : ZMod 150202183) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 1 * (3 : ZMod 150202183) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 150202183) ^ 4 = 81 := by
        calc
          (3 : ZMod 150202183) ^ 4 = (3 : ZMod 150202183) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 2 * (3 : ZMod 150202183) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 150202183) ^ 8 = 6561 := by
        calc
          (3 : ZMod 150202183) ^ 8 = (3 : ZMod 150202183) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 4 * (3 : ZMod 150202183) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 150202183) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 150202183) ^ 17 = (3 : ZMod 150202183) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 8 * (3 : ZMod 150202183) ^ 8) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 150202183) ^ 35 = 21356927 := by
        calc
          (3 : ZMod 150202183) ^ 35 = (3 : ZMod 150202183) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 17 * (3 : ZMod 150202183) ^ 17) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 21356927 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 150202183) ^ 71 = 37930066 := by
        calc
          (3 : ZMod 150202183) ^ 71 = (3 : ZMod 150202183) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 35 * (3 : ZMod 150202183) ^ 35) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 37930066 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 150202183) ^ 143 = 78443990 := by
        calc
          (3 : ZMod 150202183) ^ 143 = (3 : ZMod 150202183) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 71 * (3 : ZMod 150202183) ^ 71) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 78443990 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 150202183) ^ 286 = 115718831 := by
        calc
          (3 : ZMod 150202183) ^ 286 = (3 : ZMod 150202183) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 143 * (3 : ZMod 150202183) ^ 143 := by rw [pow_add]
          _ = 115718831 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 150202183) ^ 572 = 148660928 := by
        calc
          (3 : ZMod 150202183) ^ 572 = (3 : ZMod 150202183) ^ (286 + 286) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 286 * (3 : ZMod 150202183) ^ 286 := by rw [pow_add]
          _ = 148660928 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 150202183) ^ 1145 = 58352640 := by
        calc
          (3 : ZMod 150202183) ^ 1145 = (3 : ZMod 150202183) ^ (572 + 572 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 572 * (3 : ZMod 150202183) ^ 572) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 58352640 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 150202183) ^ 2291 = 82786231 := by
        calc
          (3 : ZMod 150202183) ^ 2291 = (3 : ZMod 150202183) ^ (1145 + 1145 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1145 * (3 : ZMod 150202183) ^ 1145) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 82786231 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 150202183) ^ 4583 = 17305264 := by
        calc
          (3 : ZMod 150202183) ^ 4583 = (3 : ZMod 150202183) ^ (2291 + 2291 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 2291 * (3 : ZMod 150202183) ^ 2291) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 17305264 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 150202183) ^ 9167 = 2774365 := by
        calc
          (3 : ZMod 150202183) ^ 9167 = (3 : ZMod 150202183) ^ (4583 + 4583 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 4583 * (3 : ZMod 150202183) ^ 4583) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 2774365 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 150202183) ^ 18335 = 121058353 := by
        calc
          (3 : ZMod 150202183) ^ 18335 = (3 : ZMod 150202183) ^ (9167 + 9167 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 9167 * (3 : ZMod 150202183) ^ 9167) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 121058353 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 150202183) ^ 36670 = 123449232 := by
        calc
          (3 : ZMod 150202183) ^ 36670 = (3 : ZMod 150202183) ^ (18335 + 18335) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 18335 * (3 : ZMod 150202183) ^ 18335 := by rw [pow_add]
          _ = 123449232 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 150202183) ^ 73340 = 75912983 := by
        calc
          (3 : ZMod 150202183) ^ 73340 = (3 : ZMod 150202183) ^ (36670 + 36670) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 36670 * (3 : ZMod 150202183) ^ 36670 := by rw [pow_add]
          _ = 75912983 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 150202183) ^ 146681 = 54133576 := by
        calc
          (3 : ZMod 150202183) ^ 146681 = (3 : ZMod 150202183) ^ (73340 + 73340 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 73340 * (3 : ZMod 150202183) ^ 73340) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 54133576 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 150202183) ^ 293363 = 32877341 := by
        calc
          (3 : ZMod 150202183) ^ 293363 = (3 : ZMod 150202183) ^ (146681 + 146681 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 146681 * (3 : ZMod 150202183) ^ 146681) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 32877341 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 150202183) ^ 586727 = 16068590 := by
        calc
          (3 : ZMod 150202183) ^ 586727 = (3 : ZMod 150202183) ^ (293363 + 293363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 293363 * (3 : ZMod 150202183) ^ 293363) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 16068590 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 150202183) ^ 1173454 = 79382721 := by
        calc
          (3 : ZMod 150202183) ^ 1173454 = (3 : ZMod 150202183) ^ (586727 + 586727) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 586727 * (3 : ZMod 150202183) ^ 586727 := by rw [pow_add]
          _ = 79382721 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 150202183) ^ 2346909 = 36063266 := by
        calc
          (3 : ZMod 150202183) ^ 2346909 = (3 : ZMod 150202183) ^ (1173454 + 1173454 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1173454 * (3 : ZMod 150202183) ^ 1173454) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 36063266 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 150202183) ^ 4693818 = 57994447 := by
        calc
          (3 : ZMod 150202183) ^ 4693818 = (3 : ZMod 150202183) ^ (2346909 + 2346909) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 2346909 * (3 : ZMod 150202183) ^ 2346909 := by rw [pow_add]
          _ = 57994447 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 150202183) ^ 9387636 = 62685039 := by
        calc
          (3 : ZMod 150202183) ^ 9387636 = (3 : ZMod 150202183) ^ (4693818 + 4693818) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 4693818 * (3 : ZMod 150202183) ^ 4693818 := by rw [pow_add]
          _ = 62685039 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 150202183) ^ 18775272 = 38935265 := by
        calc
          (3 : ZMod 150202183) ^ 18775272 = (3 : ZMod 150202183) ^ (9387636 + 9387636) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 9387636 * (3 : ZMod 150202183) ^ 9387636 := by rw [pow_add]
          _ = 38935265 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 150202183) ^ 37550545 = 77364520 := by
        calc
          (3 : ZMod 150202183) ^ 37550545 = (3 : ZMod 150202183) ^ (18775272 + 18775272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 18775272 * (3 : ZMod 150202183) ^ 18775272) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 77364520 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 150202183) ^ 75101091 = 150202182 := by
        calc
          (3 : ZMod 150202183) ^ 75101091 = (3 : ZMod 150202183) ^ (37550545 + 37550545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 37550545 * (3 : ZMod 150202183) ^ 37550545) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 150202182 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 150202183) ^ 150202182 = 1 := by
        calc
          (3 : ZMod 150202183) ^ 150202182 = (3 : ZMod 150202183) ^ (75101091 + 75101091) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 75101091 * (3 : ZMod 150202183) ^ 75101091 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (19, 1), (43, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (19, 1), (43, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod = 150202183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 150202183) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 150202183) ^ 2 = 9 := by
        calc
          (3 : ZMod 150202183) ^ 2 = (3 : ZMod 150202183) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 1 * (3 : ZMod 150202183) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 150202183) ^ 4 = 81 := by
        calc
          (3 : ZMod 150202183) ^ 4 = (3 : ZMod 150202183) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 2 * (3 : ZMod 150202183) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 150202183) ^ 8 = 6561 := by
        calc
          (3 : ZMod 150202183) ^ 8 = (3 : ZMod 150202183) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 4 * (3 : ZMod 150202183) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 150202183) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 150202183) ^ 17 = (3 : ZMod 150202183) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 8 * (3 : ZMod 150202183) ^ 8) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 150202183) ^ 35 = 21356927 := by
        calc
          (3 : ZMod 150202183) ^ 35 = (3 : ZMod 150202183) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 17 * (3 : ZMod 150202183) ^ 17) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 21356927 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 150202183) ^ 71 = 37930066 := by
        calc
          (3 : ZMod 150202183) ^ 71 = (3 : ZMod 150202183) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 35 * (3 : ZMod 150202183) ^ 35) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 37930066 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 150202183) ^ 143 = 78443990 := by
        calc
          (3 : ZMod 150202183) ^ 143 = (3 : ZMod 150202183) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 71 * (3 : ZMod 150202183) ^ 71) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 78443990 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 150202183) ^ 286 = 115718831 := by
        calc
          (3 : ZMod 150202183) ^ 286 = (3 : ZMod 150202183) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 143 * (3 : ZMod 150202183) ^ 143 := by rw [pow_add]
          _ = 115718831 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 150202183) ^ 572 = 148660928 := by
        calc
          (3 : ZMod 150202183) ^ 572 = (3 : ZMod 150202183) ^ (286 + 286) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 286 * (3 : ZMod 150202183) ^ 286 := by rw [pow_add]
          _ = 148660928 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 150202183) ^ 1145 = 58352640 := by
        calc
          (3 : ZMod 150202183) ^ 1145 = (3 : ZMod 150202183) ^ (572 + 572 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 572 * (3 : ZMod 150202183) ^ 572) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 58352640 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 150202183) ^ 2291 = 82786231 := by
        calc
          (3 : ZMod 150202183) ^ 2291 = (3 : ZMod 150202183) ^ (1145 + 1145 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1145 * (3 : ZMod 150202183) ^ 1145) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 82786231 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 150202183) ^ 4583 = 17305264 := by
        calc
          (3 : ZMod 150202183) ^ 4583 = (3 : ZMod 150202183) ^ (2291 + 2291 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 2291 * (3 : ZMod 150202183) ^ 2291) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 17305264 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 150202183) ^ 9167 = 2774365 := by
        calc
          (3 : ZMod 150202183) ^ 9167 = (3 : ZMod 150202183) ^ (4583 + 4583 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 4583 * (3 : ZMod 150202183) ^ 4583) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 2774365 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 150202183) ^ 18335 = 121058353 := by
        calc
          (3 : ZMod 150202183) ^ 18335 = (3 : ZMod 150202183) ^ (9167 + 9167 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 9167 * (3 : ZMod 150202183) ^ 9167) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 121058353 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 150202183) ^ 36670 = 123449232 := by
        calc
          (3 : ZMod 150202183) ^ 36670 = (3 : ZMod 150202183) ^ (18335 + 18335) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 18335 * (3 : ZMod 150202183) ^ 18335 := by rw [pow_add]
          _ = 123449232 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 150202183) ^ 73340 = 75912983 := by
        calc
          (3 : ZMod 150202183) ^ 73340 = (3 : ZMod 150202183) ^ (36670 + 36670) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 36670 * (3 : ZMod 150202183) ^ 36670 := by rw [pow_add]
          _ = 75912983 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 150202183) ^ 146681 = 54133576 := by
        calc
          (3 : ZMod 150202183) ^ 146681 = (3 : ZMod 150202183) ^ (73340 + 73340 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 73340 * (3 : ZMod 150202183) ^ 73340) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 54133576 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 150202183) ^ 293363 = 32877341 := by
        calc
          (3 : ZMod 150202183) ^ 293363 = (3 : ZMod 150202183) ^ (146681 + 146681 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 146681 * (3 : ZMod 150202183) ^ 146681) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 32877341 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 150202183) ^ 586727 = 16068590 := by
        calc
          (3 : ZMod 150202183) ^ 586727 = (3 : ZMod 150202183) ^ (293363 + 293363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 293363 * (3 : ZMod 150202183) ^ 293363) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 16068590 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 150202183) ^ 1173454 = 79382721 := by
        calc
          (3 : ZMod 150202183) ^ 1173454 = (3 : ZMod 150202183) ^ (586727 + 586727) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 586727 * (3 : ZMod 150202183) ^ 586727 := by rw [pow_add]
          _ = 79382721 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 150202183) ^ 2346909 = 36063266 := by
        calc
          (3 : ZMod 150202183) ^ 2346909 = (3 : ZMod 150202183) ^ (1173454 + 1173454 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1173454 * (3 : ZMod 150202183) ^ 1173454) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 36063266 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 150202183) ^ 4693818 = 57994447 := by
        calc
          (3 : ZMod 150202183) ^ 4693818 = (3 : ZMod 150202183) ^ (2346909 + 2346909) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 2346909 * (3 : ZMod 150202183) ^ 2346909 := by rw [pow_add]
          _ = 57994447 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 150202183) ^ 9387636 = 62685039 := by
        calc
          (3 : ZMod 150202183) ^ 9387636 = (3 : ZMod 150202183) ^ (4693818 + 4693818) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 4693818 * (3 : ZMod 150202183) ^ 4693818 := by rw [pow_add]
          _ = 62685039 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 150202183) ^ 18775272 = 38935265 := by
        calc
          (3 : ZMod 150202183) ^ 18775272 = (3 : ZMod 150202183) ^ (9387636 + 9387636) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 9387636 * (3 : ZMod 150202183) ^ 9387636 := by rw [pow_add]
          _ = 38935265 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 150202183) ^ 37550545 = 77364520 := by
        calc
          (3 : ZMod 150202183) ^ 37550545 = (3 : ZMod 150202183) ^ (18775272 + 18775272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 18775272 * (3 : ZMod 150202183) ^ 18775272) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 77364520 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 150202183) ^ 75101091 = 150202182 := by
        calc
          (3 : ZMod 150202183) ^ 75101091 = (3 : ZMod 150202183) ^ (37550545 + 37550545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 37550545 * (3 : ZMod 150202183) ^ 37550545) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 150202182 := by rw [factor_0_25]; decide
      change (3 : ZMod 150202183) ^ 75101091 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (3 : ZMod 150202183) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 150202183) ^ 2 = 9 := by
        calc
          (3 : ZMod 150202183) ^ 2 = (3 : ZMod 150202183) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 1 * (3 : ZMod 150202183) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 150202183) ^ 5 = 243 := by
        calc
          (3 : ZMod 150202183) ^ 5 = (3 : ZMod 150202183) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 2 * (3 : ZMod 150202183) ^ 2) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 150202183) ^ 11 = 177147 := by
        calc
          (3 : ZMod 150202183) ^ 11 = (3 : ZMod 150202183) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 5 * (3 : ZMod 150202183) ^ 5) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 150202183) ^ 23 = 116612269 := by
        calc
          (3 : ZMod 150202183) ^ 23 = (3 : ZMod 150202183) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 11 * (3 : ZMod 150202183) ^ 11) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 116612269 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 150202183) ^ 47 = 68885595 := by
        calc
          (3 : ZMod 150202183) ^ 47 = (3 : ZMod 150202183) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 23 * (3 : ZMod 150202183) ^ 23) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 68885595 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 150202183) ^ 95 = 96855910 := by
        calc
          (3 : ZMod 150202183) ^ 95 = (3 : ZMod 150202183) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 47 * (3 : ZMod 150202183) ^ 47) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 96855910 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 150202183) ^ 190 = 107103788 := by
        calc
          (3 : ZMod 150202183) ^ 190 = (3 : ZMod 150202183) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 95 * (3 : ZMod 150202183) ^ 95 := by rw [pow_add]
          _ = 107103788 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 150202183) ^ 381 = 31278934 := by
        calc
          (3 : ZMod 150202183) ^ 381 = (3 : ZMod 150202183) ^ (190 + 190 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 190 * (3 : ZMod 150202183) ^ 190) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 31278934 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 150202183) ^ 763 = 9318683 := by
        calc
          (3 : ZMod 150202183) ^ 763 = (3 : ZMod 150202183) ^ (381 + 381 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 381 * (3 : ZMod 150202183) ^ 381) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 9318683 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 150202183) ^ 1527 = 38526790 := by
        calc
          (3 : ZMod 150202183) ^ 1527 = (3 : ZMod 150202183) ^ (763 + 763 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 763 * (3 : ZMod 150202183) ^ 763) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 38526790 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 150202183) ^ 3055 = 13015387 := by
        calc
          (3 : ZMod 150202183) ^ 3055 = (3 : ZMod 150202183) ^ (1527 + 1527 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1527 * (3 : ZMod 150202183) ^ 1527) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 13015387 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 150202183) ^ 6111 = 71218872 := by
        calc
          (3 : ZMod 150202183) ^ 6111 = (3 : ZMod 150202183) ^ (3055 + 3055 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 3055 * (3 : ZMod 150202183) ^ 3055) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 71218872 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 150202183) ^ 12223 = 84848237 := by
        calc
          (3 : ZMod 150202183) ^ 12223 = (3 : ZMod 150202183) ^ (6111 + 6111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 6111 * (3 : ZMod 150202183) ^ 6111) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 84848237 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 150202183) ^ 24446 = 96944458 := by
        calc
          (3 : ZMod 150202183) ^ 24446 = (3 : ZMod 150202183) ^ (12223 + 12223) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 12223 * (3 : ZMod 150202183) ^ 12223 := by rw [pow_add]
          _ = 96944458 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 150202183) ^ 48893 = 127640740 := by
        calc
          (3 : ZMod 150202183) ^ 48893 = (3 : ZMod 150202183) ^ (24446 + 24446 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 24446 * (3 : ZMod 150202183) ^ 24446) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 127640740 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 150202183) ^ 97787 = 102886137 := by
        calc
          (3 : ZMod 150202183) ^ 97787 = (3 : ZMod 150202183) ^ (48893 + 48893 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 48893 * (3 : ZMod 150202183) ^ 48893) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 102886137 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 150202183) ^ 195575 = 34030112 := by
        calc
          (3 : ZMod 150202183) ^ 195575 = (3 : ZMod 150202183) ^ (97787 + 97787 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 97787 * (3 : ZMod 150202183) ^ 97787) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 34030112 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 150202183) ^ 391151 = 17057330 := by
        calc
          (3 : ZMod 150202183) ^ 391151 = (3 : ZMod 150202183) ^ (195575 + 195575 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 195575 * (3 : ZMod 150202183) ^ 195575) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 17057330 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 150202183) ^ 782303 = 40899989 := by
        calc
          (3 : ZMod 150202183) ^ 782303 = (3 : ZMod 150202183) ^ (391151 + 391151 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 391151 * (3 : ZMod 150202183) ^ 391151) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 40899989 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 150202183) ^ 1564606 = 28222154 := by
        calc
          (3 : ZMod 150202183) ^ 1564606 = (3 : ZMod 150202183) ^ (782303 + 782303) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 782303 * (3 : ZMod 150202183) ^ 782303 := by rw [pow_add]
          _ = 28222154 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 150202183) ^ 3129212 = 93420061 := by
        calc
          (3 : ZMod 150202183) ^ 3129212 = (3 : ZMod 150202183) ^ (1564606 + 1564606) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 1564606 * (3 : ZMod 150202183) ^ 1564606 := by rw [pow_add]
          _ = 93420061 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 150202183) ^ 6258424 = 109992399 := by
        calc
          (3 : ZMod 150202183) ^ 6258424 = (3 : ZMod 150202183) ^ (3129212 + 3129212) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 3129212 * (3 : ZMod 150202183) ^ 3129212 := by rw [pow_add]
          _ = 109992399 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 150202183) ^ 12516848 = 113783351 := by
        calc
          (3 : ZMod 150202183) ^ 12516848 = (3 : ZMod 150202183) ^ (6258424 + 6258424) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 6258424 * (3 : ZMod 150202183) ^ 6258424 := by rw [pow_add]
          _ = 113783351 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 150202183) ^ 25033697 = 109256495 := by
        calc
          (3 : ZMod 150202183) ^ 25033697 = (3 : ZMod 150202183) ^ (12516848 + 12516848 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 12516848 * (3 : ZMod 150202183) ^ 12516848) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 109256495 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 150202183) ^ 50067394 = 109256494 := by
        calc
          (3 : ZMod 150202183) ^ 50067394 = (3 : ZMod 150202183) ^ (25033697 + 25033697) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 25033697 * (3 : ZMod 150202183) ^ 25033697 := by rw [pow_add]
          _ = 109256494 := by rw [factor_1_24]; decide
      change (3 : ZMod 150202183) ^ 50067394 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (3 : ZMod 150202183) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 150202183) ^ 2 = 9 := by
        calc
          (3 : ZMod 150202183) ^ 2 = (3 : ZMod 150202183) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 1 * (3 : ZMod 150202183) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 150202183) ^ 5 = 243 := by
        calc
          (3 : ZMod 150202183) ^ 5 = (3 : ZMod 150202183) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 2 * (3 : ZMod 150202183) ^ 2) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 150202183) ^ 11 = 177147 := by
        calc
          (3 : ZMod 150202183) ^ 11 = (3 : ZMod 150202183) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 5 * (3 : ZMod 150202183) ^ 5) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 150202183) ^ 22 = 139005545 := by
        calc
          (3 : ZMod 150202183) ^ 22 = (3 : ZMod 150202183) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 11 * (3 : ZMod 150202183) ^ 11 := by rw [pow_add]
          _ = 139005545 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 150202183) ^ 44 = 102686107 := by
        calc
          (3 : ZMod 150202183) ^ 44 = (3 : ZMod 150202183) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 22 * (3 : ZMod 150202183) ^ 22 := by rw [pow_add]
          _ = 102686107 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 150202183) ^ 88 = 146881172 := by
        calc
          (3 : ZMod 150202183) ^ 88 = (3 : ZMod 150202183) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 44 * (3 : ZMod 150202183) ^ 44 := by rw [pow_add]
          _ = 146881172 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 150202183) ^ 176 = 68168797 := by
        calc
          (3 : ZMod 150202183) ^ 176 = (3 : ZMod 150202183) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 88 * (3 : ZMod 150202183) ^ 88 := by rw [pow_add]
          _ = 68168797 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 150202183) ^ 352 = 6740975 := by
        calc
          (3 : ZMod 150202183) ^ 352 = (3 : ZMod 150202183) ^ (176 + 176) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 176 * (3 : ZMod 150202183) ^ 176 := by rw [pow_add]
          _ = 6740975 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 150202183) ^ 705 = 82380722 := by
        calc
          (3 : ZMod 150202183) ^ 705 = (3 : ZMod 150202183) ^ (352 + 352 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 352 * (3 : ZMod 150202183) ^ 352) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 82380722 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 150202183) ^ 1410 = 75380663 := by
        calc
          (3 : ZMod 150202183) ^ 1410 = (3 : ZMod 150202183) ^ (705 + 705) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 705 * (3 : ZMod 150202183) ^ 705 := by rw [pow_add]
          _ = 75380663 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 150202183) ^ 2820 = 92638998 := by
        calc
          (3 : ZMod 150202183) ^ 2820 = (3 : ZMod 150202183) ^ (1410 + 1410) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 1410 * (3 : ZMod 150202183) ^ 1410 := by rw [pow_add]
          _ = 92638998 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 150202183) ^ 5641 = 88473075 := by
        calc
          (3 : ZMod 150202183) ^ 5641 = (3 : ZMod 150202183) ^ (2820 + 2820 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 2820 * (3 : ZMod 150202183) ^ 2820) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 88473075 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 150202183) ^ 11283 = 117490999 := by
        calc
          (3 : ZMod 150202183) ^ 11283 = (3 : ZMod 150202183) ^ (5641 + 5641 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 5641 * (3 : ZMod 150202183) ^ 5641) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 117490999 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 150202183) ^ 22566 = 132464914 := by
        calc
          (3 : ZMod 150202183) ^ 22566 = (3 : ZMod 150202183) ^ (11283 + 11283) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 11283 * (3 : ZMod 150202183) ^ 11283 := by rw [pow_add]
          _ = 132464914 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 150202183) ^ 45132 = 72908038 := by
        calc
          (3 : ZMod 150202183) ^ 45132 = (3 : ZMod 150202183) ^ (22566 + 22566) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 22566 * (3 : ZMod 150202183) ^ 22566 := by rw [pow_add]
          _ = 72908038 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 150202183) ^ 90265 = 141914244 := by
        calc
          (3 : ZMod 150202183) ^ 90265 = (3 : ZMod 150202183) ^ (45132 + 45132 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 45132 * (3 : ZMod 150202183) ^ 45132) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 141914244 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 150202183) ^ 180531 = 63838496 := by
        calc
          (3 : ZMod 150202183) ^ 180531 = (3 : ZMod 150202183) ^ (90265 + 90265 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 90265 * (3 : ZMod 150202183) ^ 90265) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 63838496 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 150202183) ^ 361062 = 50999300 := by
        calc
          (3 : ZMod 150202183) ^ 361062 = (3 : ZMod 150202183) ^ (180531 + 180531) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 180531 * (3 : ZMod 150202183) ^ 180531 := by rw [pow_add]
          _ = 50999300 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 150202183) ^ 722125 = 37583167 := by
        calc
          (3 : ZMod 150202183) ^ 722125 = (3 : ZMod 150202183) ^ (361062 + 361062 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 361062 * (3 : ZMod 150202183) ^ 361062) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 37583167 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 150202183) ^ 1444251 = 66354921 := by
        calc
          (3 : ZMod 150202183) ^ 1444251 = (3 : ZMod 150202183) ^ (722125 + 722125 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 722125 * (3 : ZMod 150202183) ^ 722125) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 66354921 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 150202183) ^ 2888503 = 52398115 := by
        calc
          (3 : ZMod 150202183) ^ 2888503 = (3 : ZMod 150202183) ^ (1444251 + 1444251 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1444251 * (3 : ZMod 150202183) ^ 1444251) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 52398115 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 150202183) ^ 5777007 = 89959553 := by
        calc
          (3 : ZMod 150202183) ^ 5777007 = (3 : ZMod 150202183) ^ (2888503 + 2888503 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 2888503 * (3 : ZMod 150202183) ^ 2888503) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 89959553 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 150202183) ^ 11554014 = 138228076 := by
        calc
          (3 : ZMod 150202183) ^ 11554014 = (3 : ZMod 150202183) ^ (5777007 + 5777007) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 5777007 * (3 : ZMod 150202183) ^ 5777007 := by rw [pow_add]
          _ = 138228076 := by rw [factor_2_22]; decide
      change (3 : ZMod 150202183) ^ 11554014 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (3 : ZMod 150202183) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 150202183) ^ 3 = 27 := by
        calc
          (3 : ZMod 150202183) ^ 3 = (3 : ZMod 150202183) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1 * (3 : ZMod 150202183) ^ 1) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 150202183) ^ 7 = 2187 := by
        calc
          (3 : ZMod 150202183) ^ 7 = (3 : ZMod 150202183) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 3 * (3 : ZMod 150202183) ^ 3) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 150202183) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 150202183) ^ 15 = (3 : ZMod 150202183) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 7 * (3 : ZMod 150202183) ^ 7) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 150202183) ^ 30 = 137927752 := by
        calc
          (3 : ZMod 150202183) ^ 30 = (3 : ZMod 150202183) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 15 * (3 : ZMod 150202183) ^ 15 := by rw [pow_add]
          _ = 137927752 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 150202183) ^ 60 = 4895964 := by
        calc
          (3 : ZMod 150202183) ^ 60 = (3 : ZMod 150202183) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 30 * (3 : ZMod 150202183) ^ 30 := by rw [pow_add]
          _ = 4895964 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 150202183) ^ 120 = 147710875 := by
        calc
          (3 : ZMod 150202183) ^ 120 = (3 : ZMod 150202183) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 60 * (3 : ZMod 150202183) ^ 60 := by rw [pow_add]
          _ = 147710875 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 150202183) ^ 241 = 33036997 := by
        calc
          (3 : ZMod 150202183) ^ 241 = (3 : ZMod 150202183) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 120 * (3 : ZMod 150202183) ^ 120) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 33036997 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 150202183) ^ 482 = 59423790 := by
        calc
          (3 : ZMod 150202183) ^ 482 = (3 : ZMod 150202183) ^ (241 + 241) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 241 * (3 : ZMod 150202183) ^ 241 := by rw [pow_add]
          _ = 59423790 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 150202183) ^ 965 = 105603507 := by
        calc
          (3 : ZMod 150202183) ^ 965 = (3 : ZMod 150202183) ^ (482 + 482 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 482 * (3 : ZMod 150202183) ^ 482) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 105603507 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 150202183) ^ 1930 = 6728286 := by
        calc
          (3 : ZMod 150202183) ^ 1930 = (3 : ZMod 150202183) ^ (965 + 965) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 965 * (3 : ZMod 150202183) ^ 965 := by rw [pow_add]
          _ = 6728286 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 150202183) ^ 3860 = 96159060 := by
        calc
          (3 : ZMod 150202183) ^ 3860 = (3 : ZMod 150202183) ^ (1930 + 1930) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 1930 * (3 : ZMod 150202183) ^ 1930 := by rw [pow_add]
          _ = 96159060 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 150202183) ^ 7720 = 75283396 := by
        calc
          (3 : ZMod 150202183) ^ 7720 = (3 : ZMod 150202183) ^ (3860 + 3860) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 3860 * (3 : ZMod 150202183) ^ 3860 := by rw [pow_add]
          _ = 75283396 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 150202183) ^ 15440 = 77798823 := by
        calc
          (3 : ZMod 150202183) ^ 15440 = (3 : ZMod 150202183) ^ (7720 + 7720) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 7720 * (3 : ZMod 150202183) ^ 7720 := by rw [pow_add]
          _ = 77798823 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 150202183) ^ 30880 = 46423739 := by
        calc
          (3 : ZMod 150202183) ^ 30880 = (3 : ZMod 150202183) ^ (15440 + 15440) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 15440 * (3 : ZMod 150202183) ^ 15440 := by rw [pow_add]
          _ = 46423739 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 150202183) ^ 61760 = 136947993 := by
        calc
          (3 : ZMod 150202183) ^ 61760 = (3 : ZMod 150202183) ^ (30880 + 30880) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 30880 * (3 : ZMod 150202183) ^ 30880 := by rw [pow_add]
          _ = 136947993 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 150202183) ^ 123521 = 99886697 := by
        calc
          (3 : ZMod 150202183) ^ 123521 = (3 : ZMod 150202183) ^ (61760 + 61760 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 61760 * (3 : ZMod 150202183) ^ 61760) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 99886697 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 150202183) ^ 247043 = 150077090 := by
        calc
          (3 : ZMod 150202183) ^ 247043 = (3 : ZMod 150202183) ^ (123521 + 123521 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 123521 * (3 : ZMod 150202183) ^ 123521) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 150077090 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 150202183) ^ 494086 = 27231617 := by
        calc
          (3 : ZMod 150202183) ^ 494086 = (3 : ZMod 150202183) ^ (247043 + 247043) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 247043 * (3 : ZMod 150202183) ^ 247043 := by rw [pow_add]
          _ = 27231617 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 150202183) ^ 988172 = 19778134 := by
        calc
          (3 : ZMod 150202183) ^ 988172 = (3 : ZMod 150202183) ^ (494086 + 494086) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 494086 * (3 : ZMod 150202183) ^ 494086 := by rw [pow_add]
          _ = 19778134 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 150202183) ^ 1976344 = 35291396 := by
        calc
          (3 : ZMod 150202183) ^ 1976344 = (3 : ZMod 150202183) ^ (988172 + 988172) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 988172 * (3 : ZMod 150202183) ^ 988172 := by rw [pow_add]
          _ = 35291396 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 150202183) ^ 3952689 = 65912122 := by
        calc
          (3 : ZMod 150202183) ^ 3952689 = (3 : ZMod 150202183) ^ (1976344 + 1976344 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1976344 * (3 : ZMod 150202183) ^ 1976344) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 65912122 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 150202183) ^ 7905378 = 139635928 := by
        calc
          (3 : ZMod 150202183) ^ 7905378 = (3 : ZMod 150202183) ^ (3952689 + 3952689) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 3952689 * (3 : ZMod 150202183) ^ 3952689 := by rw [pow_add]
          _ = 139635928 := by rw [factor_3_21]; decide
      change (3 : ZMod 150202183) ^ 7905378 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (3 : ZMod 150202183) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 150202183) ^ 3 = 27 := by
        calc
          (3 : ZMod 150202183) ^ 3 = (3 : ZMod 150202183) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1 * (3 : ZMod 150202183) ^ 1) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 150202183) ^ 6 = 729 := by
        calc
          (3 : ZMod 150202183) ^ 6 = (3 : ZMod 150202183) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 3 * (3 : ZMod 150202183) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 150202183) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 150202183) ^ 13 = (3 : ZMod 150202183) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 6 * (3 : ZMod 150202183) ^ 6) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 150202183) ^ 26 = 144487603 := by
        calc
          (3 : ZMod 150202183) ^ 26 = (3 : ZMod 150202183) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 13 * (3 : ZMod 150202183) ^ 13 := by rw [pow_add]
          _ = 144487603 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 150202183) ^ 53 = 50069633 := by
        calc
          (3 : ZMod 150202183) ^ 53 = (3 : ZMod 150202183) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 26 * (3 : ZMod 150202183) ^ 26) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 50069633 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 150202183) ^ 106 = 138524680 := by
        calc
          (3 : ZMod 150202183) ^ 106 = (3 : ZMod 150202183) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 53 * (3 : ZMod 150202183) ^ 53 := by rw [pow_add]
          _ = 138524680 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 150202183) ^ 213 = 61304397 := by
        calc
          (3 : ZMod 150202183) ^ 213 = (3 : ZMod 150202183) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 106 * (3 : ZMod 150202183) ^ 106) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 61304397 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 150202183) ^ 426 = 143598087 := by
        calc
          (3 : ZMod 150202183) ^ 426 = (3 : ZMod 150202183) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 213 * (3 : ZMod 150202183) ^ 213 := by rw [pow_add]
          _ = 143598087 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 150202183) ^ 852 = 26301689 := by
        calc
          (3 : ZMod 150202183) ^ 852 = (3 : ZMod 150202183) ^ (426 + 426) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 426 * (3 : ZMod 150202183) ^ 426 := by rw [pow_add]
          _ = 26301689 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 150202183) ^ 1705 = 29749764 := by
        calc
          (3 : ZMod 150202183) ^ 1705 = (3 : ZMod 150202183) ^ (852 + 852 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 852 * (3 : ZMod 150202183) ^ 852) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 29749764 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 150202183) ^ 3411 = 56566102 := by
        calc
          (3 : ZMod 150202183) ^ 3411 = (3 : ZMod 150202183) ^ (1705 + 1705 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1705 * (3 : ZMod 150202183) ^ 1705) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 56566102 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 150202183) ^ 6822 = 135910030 := by
        calc
          (3 : ZMod 150202183) ^ 6822 = (3 : ZMod 150202183) ^ (3411 + 3411) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 3411 * (3 : ZMod 150202183) ^ 3411 := by rw [pow_add]
          _ = 135910030 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 150202183) ^ 13644 = 131232938 := by
        calc
          (3 : ZMod 150202183) ^ 13644 = (3 : ZMod 150202183) ^ (6822 + 6822) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 6822 * (3 : ZMod 150202183) ^ 6822 := by rw [pow_add]
          _ = 131232938 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 150202183) ^ 27289 = 137082944 := by
        calc
          (3 : ZMod 150202183) ^ 27289 = (3 : ZMod 150202183) ^ (13644 + 13644 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 13644 * (3 : ZMod 150202183) ^ 13644) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 137082944 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 150202183) ^ 54579 = 10416498 := by
        calc
          (3 : ZMod 150202183) ^ 54579 = (3 : ZMod 150202183) ^ (27289 + 27289 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 27289 * (3 : ZMod 150202183) ^ 27289) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 10416498 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 150202183) ^ 109158 = 77224098 := by
        calc
          (3 : ZMod 150202183) ^ 109158 = (3 : ZMod 150202183) ^ (54579 + 54579) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 54579 * (3 : ZMod 150202183) ^ 54579 := by rw [pow_add]
          _ = 77224098 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 150202183) ^ 218317 = 81530738 := by
        calc
          (3 : ZMod 150202183) ^ 218317 = (3 : ZMod 150202183) ^ (109158 + 109158 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 109158 * (3 : ZMod 150202183) ^ 109158) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 81530738 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 150202183) ^ 436634 = 94636235 := by
        calc
          (3 : ZMod 150202183) ^ 436634 = (3 : ZMod 150202183) ^ (218317 + 218317) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 218317 * (3 : ZMod 150202183) ^ 218317 := by rw [pow_add]
          _ = 94636235 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 150202183) ^ 873268 = 28522195 := by
        calc
          (3 : ZMod 150202183) ^ 873268 = (3 : ZMod 150202183) ^ (436634 + 436634) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 436634 * (3 : ZMod 150202183) ^ 436634 := by rw [pow_add]
          _ = 28522195 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 150202183) ^ 1746537 = 20372862 := by
        calc
          (3 : ZMod 150202183) ^ 1746537 = (3 : ZMod 150202183) ^ (873268 + 873268 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 873268 * (3 : ZMod 150202183) ^ 873268) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 20372862 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 150202183) ^ 3493074 = 114191510 := by
        calc
          (3 : ZMod 150202183) ^ 3493074 = (3 : ZMod 150202183) ^ (1746537 + 1746537) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 1746537 * (3 : ZMod 150202183) ^ 1746537 := by rw [pow_add]
          _ = 114191510 := by rw [factor_4_20]; decide
      change (3 : ZMod 150202183) ^ 3493074 ≠ 1
      rw [factor_4_21]
      decide
    ·
      have factor_5_0 : (3 : ZMod 150202183) ^ 1 = 3 := by norm_num
      have factor_5_1 : (3 : ZMod 150202183) ^ 3 = 27 := by
        calc
          (3 : ZMod 150202183) ^ 3 = (3 : ZMod 150202183) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 1 * (3 : ZMod 150202183) ^ 1) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_5_0]; decide
      have factor_5_2 : (3 : ZMod 150202183) ^ 7 = 2187 := by
        calc
          (3 : ZMod 150202183) ^ 7 = (3 : ZMod 150202183) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 3 * (3 : ZMod 150202183) ^ 3) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_5_1]; decide
      have factor_5_3 : (3 : ZMod 150202183) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 150202183) ^ 15 = (3 : ZMod 150202183) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 7 * (3 : ZMod 150202183) ^ 7) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_5_2]; decide
      have factor_5_4 : (3 : ZMod 150202183) ^ 31 = 113378890 := by
        calc
          (3 : ZMod 150202183) ^ 31 = (3 : ZMod 150202183) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 15 * (3 : ZMod 150202183) ^ 15) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 113378890 := by rw [factor_5_3]; decide
      have factor_5_5 : (3 : ZMod 150202183) ^ 62 = 44063676 := by
        calc
          (3 : ZMod 150202183) ^ 62 = (3 : ZMod 150202183) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 31 * (3 : ZMod 150202183) ^ 31 := by rw [pow_add]
          _ = 44063676 := by rw [factor_5_4]; decide
      have factor_5_6 : (3 : ZMod 150202183) ^ 124 = 98608418 := by
        calc
          (3 : ZMod 150202183) ^ 124 = (3 : ZMod 150202183) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 62 * (3 : ZMod 150202183) ^ 62 := by rw [pow_add]
          _ = 98608418 := by rw [factor_5_5]; decide
      have factor_5_7 : (3 : ZMod 150202183) ^ 248 = 4662416 := by
        calc
          (3 : ZMod 150202183) ^ 248 = (3 : ZMod 150202183) ^ (124 + 124) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 124 * (3 : ZMod 150202183) ^ 124 := by rw [pow_add]
          _ = 4662416 := by rw [factor_5_6]; decide
      have factor_5_8 : (3 : ZMod 150202183) ^ 497 = 35662777 := by
        calc
          (3 : ZMod 150202183) ^ 497 = (3 : ZMod 150202183) ^ (248 + 248 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 248 * (3 : ZMod 150202183) ^ 248) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 35662777 := by rw [factor_5_7]; decide
      have factor_5_9 : (3 : ZMod 150202183) ^ 995 = 99943948 := by
        calc
          (3 : ZMod 150202183) ^ 995 = (3 : ZMod 150202183) ^ (497 + 497 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 497 * (3 : ZMod 150202183) ^ 497) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 99943948 := by rw [factor_5_8]; decide
      have factor_5_10 : (3 : ZMod 150202183) ^ 1991 = 13425726 := by
        calc
          (3 : ZMod 150202183) ^ 1991 = (3 : ZMod 150202183) ^ (995 + 995 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 995 * (3 : ZMod 150202183) ^ 995) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 13425726 := by rw [factor_5_9]; decide
      have factor_5_11 : (3 : ZMod 150202183) ^ 3982 = 139120109 := by
        calc
          (3 : ZMod 150202183) ^ 3982 = (3 : ZMod 150202183) ^ (1991 + 1991) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 1991 * (3 : ZMod 150202183) ^ 1991 := by rw [pow_add]
          _ = 139120109 := by rw [factor_5_10]; decide
      have factor_5_12 : (3 : ZMod 150202183) ^ 7965 = 149656408 := by
        calc
          (3 : ZMod 150202183) ^ 7965 = (3 : ZMod 150202183) ^ (3982 + 3982 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 3982 * (3 : ZMod 150202183) ^ 3982) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 149656408 := by rw [factor_5_11]; decide
      have factor_5_13 : (3 : ZMod 150202183) ^ 15931 = 58265208 := by
        calc
          (3 : ZMod 150202183) ^ 15931 = (3 : ZMod 150202183) ^ (7965 + 7965 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 7965 * (3 : ZMod 150202183) ^ 7965) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 58265208 := by rw [factor_5_12]; decide
      have factor_5_14 : (3 : ZMod 150202183) ^ 31863 = 61890807 := by
        calc
          (3 : ZMod 150202183) ^ 31863 = (3 : ZMod 150202183) ^ (15931 + 15931 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = ((3 : ZMod 150202183) ^ 15931 * (3 : ZMod 150202183) ^ 15931) * (3 : ZMod 150202183) := by rw [pow_succ, pow_add]
          _ = 61890807 := by rw [factor_5_13]; decide
      have factor_5_15 : (3 : ZMod 150202183) ^ 63726 = 149016034 := by
        calc
          (3 : ZMod 150202183) ^ 63726 = (3 : ZMod 150202183) ^ (31863 + 31863) :=
            congrArg (fun n : ℕ => (3 : ZMod 150202183) ^ n) (by norm_num)
          _ = (3 : ZMod 150202183) ^ 31863 * (3 : ZMod 150202183) ^ 31863 := by rw [pow_add]
          _ = 149016034 := by rw [factor_5_14]; decide
      change (3 : ZMod 150202183) ^ 63726 ≠ 1
      rw [factor_5_15]
      decide

#print axioms prime_lucas_150202183

end TotientTailPeriodKiller
end Erdos249257
