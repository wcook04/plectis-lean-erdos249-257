import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_88891459 : Nat.Prime 88891459 := by
  apply lucas_primality 88891459 (2 : ZMod 88891459)
  ·
      have fermat_0 : (2 : ZMod 88891459) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 88891459) ^ 2 = 4 := by
        calc
          (2 : ZMod 88891459) ^ 2 = (2 : ZMod 88891459) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1 * (2 : ZMod 88891459) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 88891459) ^ 5 = 32 := by
        calc
          (2 : ZMod 88891459) ^ 5 = (2 : ZMod 88891459) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 2 * (2 : ZMod 88891459) ^ 2) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 88891459) ^ 10 = 1024 := by
        calc
          (2 : ZMod 88891459) ^ 10 = (2 : ZMod 88891459) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 5 * (2 : ZMod 88891459) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 88891459) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 88891459) ^ 21 = (2 : ZMod 88891459) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 10 * (2 : ZMod 88891459) ^ 10) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 88891459) ^ 42 = 52685620 := by
        calc
          (2 : ZMod 88891459) ^ 42 = (2 : ZMod 88891459) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 21 * (2 : ZMod 88891459) ^ 21 := by rw [pow_add]
          _ = 52685620 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 88891459) ^ 84 = 76833360 := by
        calc
          (2 : ZMod 88891459) ^ 84 = (2 : ZMod 88891459) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 42 * (2 : ZMod 88891459) ^ 42 := by rw [pow_add]
          _ = 76833360 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 88891459) ^ 169 = 73022116 := by
        calc
          (2 : ZMod 88891459) ^ 169 = (2 : ZMod 88891459) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 84 * (2 : ZMod 88891459) ^ 84) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 73022116 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 88891459) ^ 339 = 20764825 := by
        calc
          (2 : ZMod 88891459) ^ 339 = (2 : ZMod 88891459) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 169 * (2 : ZMod 88891459) ^ 169) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 20764825 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 88891459) ^ 678 = 68449176 := by
        calc
          (2 : ZMod 88891459) ^ 678 = (2 : ZMod 88891459) ^ (339 + 339) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 339 * (2 : ZMod 88891459) ^ 339 := by rw [pow_add]
          _ = 68449176 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 88891459) ^ 1356 = 7478861 := by
        calc
          (2 : ZMod 88891459) ^ 1356 = (2 : ZMod 88891459) ^ (678 + 678) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 678 * (2 : ZMod 88891459) ^ 678 := by rw [pow_add]
          _ = 7478861 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 88891459) ^ 2712 = 11327833 := by
        calc
          (2 : ZMod 88891459) ^ 2712 = (2 : ZMod 88891459) ^ (1356 + 1356) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1356 * (2 : ZMod 88891459) ^ 1356 := by rw [pow_add]
          _ = 11327833 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 88891459) ^ 5425 = 2975370 := by
        calc
          (2 : ZMod 88891459) ^ 5425 = (2 : ZMod 88891459) ^ (2712 + 2712 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 2712 * (2 : ZMod 88891459) ^ 2712) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 2975370 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 88891459) ^ 10851 = 74687262 := by
        calc
          (2 : ZMod 88891459) ^ 10851 = (2 : ZMod 88891459) ^ (5425 + 5425 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 5425 * (2 : ZMod 88891459) ^ 5425) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 74687262 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 88891459) ^ 21702 = 45636034 := by
        calc
          (2 : ZMod 88891459) ^ 21702 = (2 : ZMod 88891459) ^ (10851 + 10851) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 10851 * (2 : ZMod 88891459) ^ 10851 := by rw [pow_add]
          _ = 45636034 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 88891459) ^ 43404 = 6060584 := by
        calc
          (2 : ZMod 88891459) ^ 43404 = (2 : ZMod 88891459) ^ (21702 + 21702) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 21702 * (2 : ZMod 88891459) ^ 21702 := by rw [pow_add]
          _ = 6060584 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 88891459) ^ 86808 = 16430584 := by
        calc
          (2 : ZMod 88891459) ^ 86808 = (2 : ZMod 88891459) ^ (43404 + 43404) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 43404 * (2 : ZMod 88891459) ^ 43404 := by rw [pow_add]
          _ = 16430584 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 88891459) ^ 173616 = 18466384 := by
        calc
          (2 : ZMod 88891459) ^ 173616 = (2 : ZMod 88891459) ^ (86808 + 86808) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 86808 * (2 : ZMod 88891459) ^ 86808 := by rw [pow_add]
          _ = 18466384 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 88891459) ^ 347232 = 56299017 := by
        calc
          (2 : ZMod 88891459) ^ 347232 = (2 : ZMod 88891459) ^ (173616 + 173616) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 173616 * (2 : ZMod 88891459) ^ 173616 := by rw [pow_add]
          _ = 56299017 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 88891459) ^ 694464 = 28948465 := by
        calc
          (2 : ZMod 88891459) ^ 694464 = (2 : ZMod 88891459) ^ (347232 + 347232) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 347232 * (2 : ZMod 88891459) ^ 347232 := by rw [pow_add]
          _ = 28948465 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 88891459) ^ 1388929 = 37326151 := by
        calc
          (2 : ZMod 88891459) ^ 1388929 = (2 : ZMod 88891459) ^ (694464 + 694464 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 694464 * (2 : ZMod 88891459) ^ 694464) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 37326151 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 88891459) ^ 2777858 = 21357875 := by
        calc
          (2 : ZMod 88891459) ^ 2777858 = (2 : ZMod 88891459) ^ (1388929 + 1388929) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1388929 * (2 : ZMod 88891459) ^ 1388929 := by rw [pow_add]
          _ = 21357875 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 88891459) ^ 5555716 = 35635783 := by
        calc
          (2 : ZMod 88891459) ^ 5555716 = (2 : ZMod 88891459) ^ (2777858 + 2777858) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 2777858 * (2 : ZMod 88891459) ^ 2777858 := by rw [pow_add]
          _ = 35635783 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 88891459) ^ 11111432 = 46587172 := by
        calc
          (2 : ZMod 88891459) ^ 11111432 = (2 : ZMod 88891459) ^ (5555716 + 5555716) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 5555716 * (2 : ZMod 88891459) ^ 5555716 := by rw [pow_add]
          _ = 46587172 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 88891459) ^ 22222864 = 65616779 := by
        calc
          (2 : ZMod 88891459) ^ 22222864 = (2 : ZMod 88891459) ^ (11111432 + 11111432) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 11111432 * (2 : ZMod 88891459) ^ 11111432 := by rw [pow_add]
          _ = 65616779 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 88891459) ^ 44445729 = 88891458 := by
        calc
          (2 : ZMod 88891459) ^ 44445729 = (2 : ZMod 88891459) ^ (22222864 + 22222864 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 22222864 * (2 : ZMod 88891459) ^ 22222864) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 88891458 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 88891459) ^ 88891458 = 1 := by
        calc
          (2 : ZMod 88891459) ^ 88891458 = (2 : ZMod 88891459) ^ (44445729 + 44445729) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 44445729 * (2 : ZMod 88891459) ^ 44445729 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (644141, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (644141, 1)] : List FactorBlock).map factorBlockValue).prod = 88891459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 88891459) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 88891459) ^ 2 = 4 := by
        calc
          (2 : ZMod 88891459) ^ 2 = (2 : ZMod 88891459) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1 * (2 : ZMod 88891459) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 88891459) ^ 5 = 32 := by
        calc
          (2 : ZMod 88891459) ^ 5 = (2 : ZMod 88891459) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 2 * (2 : ZMod 88891459) ^ 2) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 88891459) ^ 10 = 1024 := by
        calc
          (2 : ZMod 88891459) ^ 10 = (2 : ZMod 88891459) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 5 * (2 : ZMod 88891459) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 88891459) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 88891459) ^ 21 = (2 : ZMod 88891459) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 10 * (2 : ZMod 88891459) ^ 10) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 88891459) ^ 42 = 52685620 := by
        calc
          (2 : ZMod 88891459) ^ 42 = (2 : ZMod 88891459) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 21 * (2 : ZMod 88891459) ^ 21 := by rw [pow_add]
          _ = 52685620 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 88891459) ^ 84 = 76833360 := by
        calc
          (2 : ZMod 88891459) ^ 84 = (2 : ZMod 88891459) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 42 * (2 : ZMod 88891459) ^ 42 := by rw [pow_add]
          _ = 76833360 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 88891459) ^ 169 = 73022116 := by
        calc
          (2 : ZMod 88891459) ^ 169 = (2 : ZMod 88891459) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 84 * (2 : ZMod 88891459) ^ 84) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 73022116 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 88891459) ^ 339 = 20764825 := by
        calc
          (2 : ZMod 88891459) ^ 339 = (2 : ZMod 88891459) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 169 * (2 : ZMod 88891459) ^ 169) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 20764825 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 88891459) ^ 678 = 68449176 := by
        calc
          (2 : ZMod 88891459) ^ 678 = (2 : ZMod 88891459) ^ (339 + 339) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 339 * (2 : ZMod 88891459) ^ 339 := by rw [pow_add]
          _ = 68449176 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 88891459) ^ 1356 = 7478861 := by
        calc
          (2 : ZMod 88891459) ^ 1356 = (2 : ZMod 88891459) ^ (678 + 678) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 678 * (2 : ZMod 88891459) ^ 678 := by rw [pow_add]
          _ = 7478861 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 88891459) ^ 2712 = 11327833 := by
        calc
          (2 : ZMod 88891459) ^ 2712 = (2 : ZMod 88891459) ^ (1356 + 1356) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1356 * (2 : ZMod 88891459) ^ 1356 := by rw [pow_add]
          _ = 11327833 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 88891459) ^ 5425 = 2975370 := by
        calc
          (2 : ZMod 88891459) ^ 5425 = (2 : ZMod 88891459) ^ (2712 + 2712 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 2712 * (2 : ZMod 88891459) ^ 2712) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 2975370 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 88891459) ^ 10851 = 74687262 := by
        calc
          (2 : ZMod 88891459) ^ 10851 = (2 : ZMod 88891459) ^ (5425 + 5425 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 5425 * (2 : ZMod 88891459) ^ 5425) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 74687262 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 88891459) ^ 21702 = 45636034 := by
        calc
          (2 : ZMod 88891459) ^ 21702 = (2 : ZMod 88891459) ^ (10851 + 10851) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 10851 * (2 : ZMod 88891459) ^ 10851 := by rw [pow_add]
          _ = 45636034 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 88891459) ^ 43404 = 6060584 := by
        calc
          (2 : ZMod 88891459) ^ 43404 = (2 : ZMod 88891459) ^ (21702 + 21702) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 21702 * (2 : ZMod 88891459) ^ 21702 := by rw [pow_add]
          _ = 6060584 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 88891459) ^ 86808 = 16430584 := by
        calc
          (2 : ZMod 88891459) ^ 86808 = (2 : ZMod 88891459) ^ (43404 + 43404) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 43404 * (2 : ZMod 88891459) ^ 43404 := by rw [pow_add]
          _ = 16430584 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 88891459) ^ 173616 = 18466384 := by
        calc
          (2 : ZMod 88891459) ^ 173616 = (2 : ZMod 88891459) ^ (86808 + 86808) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 86808 * (2 : ZMod 88891459) ^ 86808 := by rw [pow_add]
          _ = 18466384 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 88891459) ^ 347232 = 56299017 := by
        calc
          (2 : ZMod 88891459) ^ 347232 = (2 : ZMod 88891459) ^ (173616 + 173616) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 173616 * (2 : ZMod 88891459) ^ 173616 := by rw [pow_add]
          _ = 56299017 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 88891459) ^ 694464 = 28948465 := by
        calc
          (2 : ZMod 88891459) ^ 694464 = (2 : ZMod 88891459) ^ (347232 + 347232) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 347232 * (2 : ZMod 88891459) ^ 347232 := by rw [pow_add]
          _ = 28948465 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 88891459) ^ 1388929 = 37326151 := by
        calc
          (2 : ZMod 88891459) ^ 1388929 = (2 : ZMod 88891459) ^ (694464 + 694464 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 694464 * (2 : ZMod 88891459) ^ 694464) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 37326151 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 88891459) ^ 2777858 = 21357875 := by
        calc
          (2 : ZMod 88891459) ^ 2777858 = (2 : ZMod 88891459) ^ (1388929 + 1388929) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1388929 * (2 : ZMod 88891459) ^ 1388929 := by rw [pow_add]
          _ = 21357875 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 88891459) ^ 5555716 = 35635783 := by
        calc
          (2 : ZMod 88891459) ^ 5555716 = (2 : ZMod 88891459) ^ (2777858 + 2777858) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 2777858 * (2 : ZMod 88891459) ^ 2777858 := by rw [pow_add]
          _ = 35635783 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 88891459) ^ 11111432 = 46587172 := by
        calc
          (2 : ZMod 88891459) ^ 11111432 = (2 : ZMod 88891459) ^ (5555716 + 5555716) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 5555716 * (2 : ZMod 88891459) ^ 5555716 := by rw [pow_add]
          _ = 46587172 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 88891459) ^ 22222864 = 65616779 := by
        calc
          (2 : ZMod 88891459) ^ 22222864 = (2 : ZMod 88891459) ^ (11111432 + 11111432) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 11111432 * (2 : ZMod 88891459) ^ 11111432 := by rw [pow_add]
          _ = 65616779 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 88891459) ^ 44445729 = 88891458 := by
        calc
          (2 : ZMod 88891459) ^ 44445729 = (2 : ZMod 88891459) ^ (22222864 + 22222864 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 22222864 * (2 : ZMod 88891459) ^ 22222864) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 88891458 := by rw [factor_0_24]; decide
      change (2 : ZMod 88891459) ^ 44445729 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 88891459) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 88891459) ^ 3 = 8 := by
        calc
          (2 : ZMod 88891459) ^ 3 = (2 : ZMod 88891459) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 1 * (2 : ZMod 88891459) ^ 1) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 88891459) ^ 7 = 128 := by
        calc
          (2 : ZMod 88891459) ^ 7 = (2 : ZMod 88891459) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 3 * (2 : ZMod 88891459) ^ 3) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 88891459) ^ 14 = 16384 := by
        calc
          (2 : ZMod 88891459) ^ 14 = (2 : ZMod 88891459) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 7 * (2 : ZMod 88891459) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 88891459) ^ 28 = 1761079 := by
        calc
          (2 : ZMod 88891459) ^ 28 = (2 : ZMod 88891459) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 14 * (2 : ZMod 88891459) ^ 14 := by rw [pow_add]
          _ = 1761079 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 88891459) ^ 56 = 65131190 := by
        calc
          (2 : ZMod 88891459) ^ 56 = (2 : ZMod 88891459) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 28 * (2 : ZMod 88891459) ^ 28 := by rw [pow_add]
          _ = 65131190 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 88891459) ^ 113 = 31423378 := by
        calc
          (2 : ZMod 88891459) ^ 113 = (2 : ZMod 88891459) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 56 * (2 : ZMod 88891459) ^ 56) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 31423378 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 88891459) ^ 226 = 46602675 := by
        calc
          (2 : ZMod 88891459) ^ 226 = (2 : ZMod 88891459) ^ (113 + 113) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 113 * (2 : ZMod 88891459) ^ 113 := by rw [pow_add]
          _ = 46602675 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 88891459) ^ 452 = 34931693 := by
        calc
          (2 : ZMod 88891459) ^ 452 = (2 : ZMod 88891459) ^ (226 + 226) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 226 * (2 : ZMod 88891459) ^ 226 := by rw [pow_add]
          _ = 34931693 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 88891459) ^ 904 = 73418382 := by
        calc
          (2 : ZMod 88891459) ^ 904 = (2 : ZMod 88891459) ^ (452 + 452) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 452 * (2 : ZMod 88891459) ^ 452 := by rw [pow_add]
          _ = 73418382 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 88891459) ^ 1808 = 34075902 := by
        calc
          (2 : ZMod 88891459) ^ 1808 = (2 : ZMod 88891459) ^ (904 + 904) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 904 * (2 : ZMod 88891459) ^ 904 := by rw [pow_add]
          _ = 34075902 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 88891459) ^ 3617 = 26556872 := by
        calc
          (2 : ZMod 88891459) ^ 3617 = (2 : ZMod 88891459) ^ (1808 + 1808 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 1808 * (2 : ZMod 88891459) ^ 1808) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 26556872 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 88891459) ^ 7234 = 36866073 := by
        calc
          (2 : ZMod 88891459) ^ 7234 = (2 : ZMod 88891459) ^ (3617 + 3617) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 3617 * (2 : ZMod 88891459) ^ 3617 := by rw [pow_add]
          _ = 36866073 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 88891459) ^ 14468 = 42688944 := by
        calc
          (2 : ZMod 88891459) ^ 14468 = (2 : ZMod 88891459) ^ (7234 + 7234) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 7234 * (2 : ZMod 88891459) ^ 7234 := by rw [pow_add]
          _ = 42688944 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 88891459) ^ 28936 = 6059395 := by
        calc
          (2 : ZMod 88891459) ^ 28936 = (2 : ZMod 88891459) ^ (14468 + 14468) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 14468 * (2 : ZMod 88891459) ^ 14468 := by rw [pow_add]
          _ = 6059395 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 88891459) ^ 57872 = 6191911 := by
        calc
          (2 : ZMod 88891459) ^ 57872 = (2 : ZMod 88891459) ^ (28936 + 28936) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 28936 * (2 : ZMod 88891459) ^ 28936 := by rw [pow_add]
          _ = 6191911 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 88891459) ^ 115744 = 75542090 := by
        calc
          (2 : ZMod 88891459) ^ 115744 = (2 : ZMod 88891459) ^ (57872 + 57872) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 57872 * (2 : ZMod 88891459) ^ 57872 := by rw [pow_add]
          _ = 75542090 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 88891459) ^ 231488 = 55810616 := by
        calc
          (2 : ZMod 88891459) ^ 231488 = (2 : ZMod 88891459) ^ (115744 + 115744) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 115744 * (2 : ZMod 88891459) ^ 115744 := by rw [pow_add]
          _ = 55810616 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 88891459) ^ 462976 = 44081862 := by
        calc
          (2 : ZMod 88891459) ^ 462976 = (2 : ZMod 88891459) ^ (231488 + 231488) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 231488 * (2 : ZMod 88891459) ^ 231488 := by rw [pow_add]
          _ = 44081862 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 88891459) ^ 925952 = 62397970 := by
        calc
          (2 : ZMod 88891459) ^ 925952 = (2 : ZMod 88891459) ^ (462976 + 462976) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 462976 * (2 : ZMod 88891459) ^ 462976 := by rw [pow_add]
          _ = 62397970 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 88891459) ^ 1851905 = 86108806 := by
        calc
          (2 : ZMod 88891459) ^ 1851905 = (2 : ZMod 88891459) ^ (925952 + 925952 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 925952 * (2 : ZMod 88891459) ^ 925952) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 86108806 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 88891459) ^ 3703810 = 507837 := by
        calc
          (2 : ZMod 88891459) ^ 3703810 = (2 : ZMod 88891459) ^ (1851905 + 1851905) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1851905 * (2 : ZMod 88891459) ^ 1851905 := by rw [pow_add]
          _ = 507837 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 88891459) ^ 7407621 = 48592020 := by
        calc
          (2 : ZMod 88891459) ^ 7407621 = (2 : ZMod 88891459) ^ (3703810 + 3703810 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 3703810 * (2 : ZMod 88891459) ^ 3703810) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 48592020 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 88891459) ^ 14815243 = 11250933 := by
        calc
          (2 : ZMod 88891459) ^ 14815243 = (2 : ZMod 88891459) ^ (7407621 + 7407621 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 7407621 * (2 : ZMod 88891459) ^ 7407621) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 11250933 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 88891459) ^ 29630486 = 11250932 := by
        calc
          (2 : ZMod 88891459) ^ 29630486 = (2 : ZMod 88891459) ^ (14815243 + 14815243) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 14815243 * (2 : ZMod 88891459) ^ 14815243 := by rw [pow_add]
          _ = 11250932 := by rw [factor_1_23]; decide
      change (2 : ZMod 88891459) ^ 29630486 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (2 : ZMod 88891459) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 88891459) ^ 3 = 8 := by
        calc
          (2 : ZMod 88891459) ^ 3 = (2 : ZMod 88891459) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 1 * (2 : ZMod 88891459) ^ 1) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 88891459) ^ 7 = 128 := by
        calc
          (2 : ZMod 88891459) ^ 7 = (2 : ZMod 88891459) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 3 * (2 : ZMod 88891459) ^ 3) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 88891459) ^ 14 = 16384 := by
        calc
          (2 : ZMod 88891459) ^ 14 = (2 : ZMod 88891459) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 7 * (2 : ZMod 88891459) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 88891459) ^ 29 = 3522158 := by
        calc
          (2 : ZMod 88891459) ^ 29 = (2 : ZMod 88891459) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 14 * (2 : ZMod 88891459) ^ 14) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 3522158 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 88891459) ^ 58 = 82741842 := by
        calc
          (2 : ZMod 88891459) ^ 58 = (2 : ZMod 88891459) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 29 * (2 : ZMod 88891459) ^ 29 := by rw [pow_add]
          _ = 82741842 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 88891459) ^ 117 = 58316753 := by
        calc
          (2 : ZMod 88891459) ^ 117 = (2 : ZMod 88891459) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 58 * (2 : ZMod 88891459) ^ 58) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 58316753 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 88891459) ^ 235 = 37658588 := by
        calc
          (2 : ZMod 88891459) ^ 235 = (2 : ZMod 88891459) ^ (117 + 117 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 117 * (2 : ZMod 88891459) ^ 117) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 37658588 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 88891459) ^ 471 = 49053273 := by
        calc
          (2 : ZMod 88891459) ^ 471 = (2 : ZMod 88891459) ^ (235 + 235 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 235 * (2 : ZMod 88891459) ^ 235) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 49053273 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 88891459) ^ 943 = 42154623 := by
        calc
          (2 : ZMod 88891459) ^ 943 = (2 : ZMod 88891459) ^ (471 + 471 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 471 * (2 : ZMod 88891459) ^ 471) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 42154623 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 88891459) ^ 1887 = 34452137 := by
        calc
          (2 : ZMod 88891459) ^ 1887 = (2 : ZMod 88891459) ^ (943 + 943 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 943 * (2 : ZMod 88891459) ^ 943) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 34452137 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 88891459) ^ 3774 = 47914487 := by
        calc
          (2 : ZMod 88891459) ^ 3774 = (2 : ZMod 88891459) ^ (1887 + 1887) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1887 * (2 : ZMod 88891459) ^ 1887 := by rw [pow_add]
          _ = 47914487 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 88891459) ^ 7548 = 41817890 := by
        calc
          (2 : ZMod 88891459) ^ 7548 = (2 : ZMod 88891459) ^ (3774 + 3774) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 3774 * (2 : ZMod 88891459) ^ 3774 := by rw [pow_add]
          _ = 41817890 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 88891459) ^ 15097 = 59336420 := by
        calc
          (2 : ZMod 88891459) ^ 15097 = (2 : ZMod 88891459) ^ (7548 + 7548 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 7548 * (2 : ZMod 88891459) ^ 7548) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 59336420 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 88891459) ^ 30194 = 52630875 := by
        calc
          (2 : ZMod 88891459) ^ 30194 = (2 : ZMod 88891459) ^ (15097 + 15097) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 15097 * (2 : ZMod 88891459) ^ 15097 := by rw [pow_add]
          _ = 52630875 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 88891459) ^ 60388 = 25345325 := by
        calc
          (2 : ZMod 88891459) ^ 60388 = (2 : ZMod 88891459) ^ (30194 + 30194) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 30194 * (2 : ZMod 88891459) ^ 30194 := by rw [pow_add]
          _ = 25345325 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 88891459) ^ 120776 = 81676832 := by
        calc
          (2 : ZMod 88891459) ^ 120776 = (2 : ZMod 88891459) ^ (60388 + 60388) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 60388 * (2 : ZMod 88891459) ^ 60388 := by rw [pow_add]
          _ = 81676832 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 88891459) ^ 241552 = 4474384 := by
        calc
          (2 : ZMod 88891459) ^ 241552 = (2 : ZMod 88891459) ^ (120776 + 120776) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 120776 * (2 : ZMod 88891459) ^ 120776 := by rw [pow_add]
          _ = 4474384 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 88891459) ^ 483105 = 44458411 := by
        calc
          (2 : ZMod 88891459) ^ 483105 = (2 : ZMod 88891459) ^ (241552 + 241552 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 241552 * (2 : ZMod 88891459) ^ 241552) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 44458411 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 88891459) ^ 966211 = 10520778 := by
        calc
          (2 : ZMod 88891459) ^ 966211 = (2 : ZMod 88891459) ^ (483105 + 483105 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 483105 * (2 : ZMod 88891459) ^ 483105) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 10520778 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 88891459) ^ 1932423 = 27786148 := by
        calc
          (2 : ZMod 88891459) ^ 1932423 = (2 : ZMod 88891459) ^ (966211 + 966211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 966211 * (2 : ZMod 88891459) ^ 966211) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 27786148 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 88891459) ^ 3864846 = 53440880 := by
        calc
          (2 : ZMod 88891459) ^ 3864846 = (2 : ZMod 88891459) ^ (1932423 + 1932423) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1932423 * (2 : ZMod 88891459) ^ 1932423 := by rw [pow_add]
          _ = 53440880 := by rw [factor_2_20]; decide
      change (2 : ZMod 88891459) ^ 3864846 ≠ 1
      rw [factor_2_21]
      decide
    ·
      have factor_3_0 : (2 : ZMod 88891459) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 88891459) ^ 2 = 4 := by
        calc
          (2 : ZMod 88891459) ^ 2 = (2 : ZMod 88891459) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 1 * (2 : ZMod 88891459) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 88891459) ^ 4 = 16 := by
        calc
          (2 : ZMod 88891459) ^ 4 = (2 : ZMod 88891459) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 2 * (2 : ZMod 88891459) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 88891459) ^ 8 = 256 := by
        calc
          (2 : ZMod 88891459) ^ 8 = (2 : ZMod 88891459) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 4 * (2 : ZMod 88891459) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 88891459) ^ 17 = 131072 := by
        calc
          (2 : ZMod 88891459) ^ 17 = (2 : ZMod 88891459) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 8 * (2 : ZMod 88891459) ^ 8) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 88891459) ^ 34 = 23817597 := by
        calc
          (2 : ZMod 88891459) ^ 34 = (2 : ZMod 88891459) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 17 * (2 : ZMod 88891459) ^ 17 := by rw [pow_add]
          _ = 23817597 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 88891459) ^ 69 = 28171562 := by
        calc
          (2 : ZMod 88891459) ^ 69 = (2 : ZMod 88891459) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = ((2 : ZMod 88891459) ^ 34 * (2 : ZMod 88891459) ^ 34) * (2 : ZMod 88891459) := by rw [pow_succ, pow_add]
          _ = 28171562 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 88891459) ^ 138 = 3608781 := by
        calc
          (2 : ZMod 88891459) ^ 138 = (2 : ZMod 88891459) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (2 : ZMod 88891459) ^ n) (by norm_num)
          _ = (2 : ZMod 88891459) ^ 69 * (2 : ZMod 88891459) ^ 69 := by rw [pow_add]
          _ = 3608781 := by rw [factor_3_6]; decide
      change (2 : ZMod 88891459) ^ 138 ≠ 1
      rw [factor_3_7]
      decide

#print axioms prime_lucas_88891459

end TotientTailPeriodKiller
end Erdos249257
