import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_46078157 : Nat.Prime 46078157 := by
  apply lucas_primality 46078157 (2 : ZMod 46078157)
  ·
      have fermat_0 : (2 : ZMod 46078157) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 46078157) ^ 2 = 4 := by
        calc
          (2 : ZMod 46078157) ^ 2 = (2 : ZMod 46078157) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 1 * (2 : ZMod 46078157) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 46078157) ^ 5 = 32 := by
        calc
          (2 : ZMod 46078157) ^ 5 = (2 : ZMod 46078157) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 2 * (2 : ZMod 46078157) ^ 2) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 46078157) ^ 10 = 1024 := by
        calc
          (2 : ZMod 46078157) ^ 10 = (2 : ZMod 46078157) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 5 * (2 : ZMod 46078157) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 46078157) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 46078157) ^ 21 = (2 : ZMod 46078157) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 10 * (2 : ZMod 46078157) ^ 10) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 46078157) ^ 43 = 3241693 := by
        calc
          (2 : ZMod 46078157) ^ 43 = (2 : ZMod 46078157) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 21 * (2 : ZMod 46078157) ^ 21) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 3241693 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 46078157) ^ 87 = 24119815 := by
        calc
          (2 : ZMod 46078157) ^ 87 = (2 : ZMod 46078157) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 43 * (2 : ZMod 46078157) ^ 43) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 24119815 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 46078157) ^ 175 = 27556671 := by
        calc
          (2 : ZMod 46078157) ^ 175 = (2 : ZMod 46078157) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 87 * (2 : ZMod 46078157) ^ 87) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 27556671 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 46078157) ^ 351 = 31450352 := by
        calc
          (2 : ZMod 46078157) ^ 351 = (2 : ZMod 46078157) ^ (175 + 175 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 175 * (2 : ZMod 46078157) ^ 175) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 31450352 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 46078157) ^ 703 = 4477390 := by
        calc
          (2 : ZMod 46078157) ^ 703 = (2 : ZMod 46078157) ^ (351 + 351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 351 * (2 : ZMod 46078157) ^ 351) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 4477390 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 46078157) ^ 1406 = 27836895 := by
        calc
          (2 : ZMod 46078157) ^ 1406 = (2 : ZMod 46078157) ^ (703 + 703) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 703 * (2 : ZMod 46078157) ^ 703 := by rw [pow_add]
          _ = 27836895 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 46078157) ^ 2812 = 43224585 := by
        calc
          (2 : ZMod 46078157) ^ 2812 = (2 : ZMod 46078157) ^ (1406 + 1406) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 1406 * (2 : ZMod 46078157) ^ 1406 := by rw [pow_add]
          _ = 43224585 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 46078157) ^ 5624 = 33410458 := by
        calc
          (2 : ZMod 46078157) ^ 5624 = (2 : ZMod 46078157) ^ (2812 + 2812) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 2812 * (2 : ZMod 46078157) ^ 2812 := by rw [pow_add]
          _ = 33410458 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 46078157) ^ 11249 = 12836966 := by
        calc
          (2 : ZMod 46078157) ^ 11249 = (2 : ZMod 46078157) ^ (5624 + 5624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 5624 * (2 : ZMod 46078157) ^ 5624) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 12836966 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 46078157) ^ 22499 = 37961259 := by
        calc
          (2 : ZMod 46078157) ^ 22499 = (2 : ZMod 46078157) ^ (11249 + 11249 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 11249 * (2 : ZMod 46078157) ^ 11249) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 37961259 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 46078157) ^ 44998 = 9762780 := by
        calc
          (2 : ZMod 46078157) ^ 44998 = (2 : ZMod 46078157) ^ (22499 + 22499) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 22499 * (2 : ZMod 46078157) ^ 22499 := by rw [pow_add]
          _ = 9762780 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 46078157) ^ 89996 = 34980726 := by
        calc
          (2 : ZMod 46078157) ^ 89996 = (2 : ZMod 46078157) ^ (44998 + 44998) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 44998 * (2 : ZMod 46078157) ^ 44998 := by rw [pow_add]
          _ = 34980726 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 46078157) ^ 179992 = 22820332 := by
        calc
          (2 : ZMod 46078157) ^ 179992 = (2 : ZMod 46078157) ^ (89996 + 89996) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 89996 * (2 : ZMod 46078157) ^ 89996 := by rw [pow_add]
          _ = 22820332 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 46078157) ^ 359985 = 18769514 := by
        calc
          (2 : ZMod 46078157) ^ 359985 = (2 : ZMod 46078157) ^ (179992 + 179992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 179992 * (2 : ZMod 46078157) ^ 179992) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 18769514 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 46078157) ^ 719971 = 10993446 := by
        calc
          (2 : ZMod 46078157) ^ 719971 = (2 : ZMod 46078157) ^ (359985 + 359985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 359985 * (2 : ZMod 46078157) ^ 359985) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 10993446 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 46078157) ^ 1439942 = 37336408 := by
        calc
          (2 : ZMod 46078157) ^ 1439942 = (2 : ZMod 46078157) ^ (719971 + 719971) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 719971 * (2 : ZMod 46078157) ^ 719971 := by rw [pow_add]
          _ = 37336408 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 46078157) ^ 2879884 = 40414979 := by
        calc
          (2 : ZMod 46078157) ^ 2879884 = (2 : ZMod 46078157) ^ (1439942 + 1439942) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 1439942 * (2 : ZMod 46078157) ^ 1439942 := by rw [pow_add]
          _ = 40414979 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 46078157) ^ 5759769 = 25589361 := by
        calc
          (2 : ZMod 46078157) ^ 5759769 = (2 : ZMod 46078157) ^ (2879884 + 2879884 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 2879884 * (2 : ZMod 46078157) ^ 2879884) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 25589361 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 46078157) ^ 11519539 = 40977591 := by
        calc
          (2 : ZMod 46078157) ^ 11519539 = (2 : ZMod 46078157) ^ (5759769 + 5759769 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 5759769 * (2 : ZMod 46078157) ^ 5759769) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 40977591 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 46078157) ^ 23039078 = 46078156 := by
        calc
          (2 : ZMod 46078157) ^ 23039078 = (2 : ZMod 46078157) ^ (11519539 + 11519539) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 11519539 * (2 : ZMod 46078157) ^ 11519539 := by rw [pow_add]
          _ = 46078156 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 46078157) ^ 46078156 = 1 := by
        calc
          (2 : ZMod 46078157) ^ 46078156 = (2 : ZMod 46078157) ^ (23039078 + 23039078) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 23039078 * (2 : ZMod 46078157) ^ 23039078 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11519539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11519539, 1)] : List FactorBlock).map factorBlockValue).prod = 46078157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 46078157) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 46078157) ^ 2 = 4 := by
        calc
          (2 : ZMod 46078157) ^ 2 = (2 : ZMod 46078157) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 1 * (2 : ZMod 46078157) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 46078157) ^ 5 = 32 := by
        calc
          (2 : ZMod 46078157) ^ 5 = (2 : ZMod 46078157) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 2 * (2 : ZMod 46078157) ^ 2) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 46078157) ^ 10 = 1024 := by
        calc
          (2 : ZMod 46078157) ^ 10 = (2 : ZMod 46078157) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 5 * (2 : ZMod 46078157) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 46078157) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 46078157) ^ 21 = (2 : ZMod 46078157) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 10 * (2 : ZMod 46078157) ^ 10) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 46078157) ^ 43 = 3241693 := by
        calc
          (2 : ZMod 46078157) ^ 43 = (2 : ZMod 46078157) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 21 * (2 : ZMod 46078157) ^ 21) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 3241693 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 46078157) ^ 87 = 24119815 := by
        calc
          (2 : ZMod 46078157) ^ 87 = (2 : ZMod 46078157) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 43 * (2 : ZMod 46078157) ^ 43) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 24119815 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 46078157) ^ 175 = 27556671 := by
        calc
          (2 : ZMod 46078157) ^ 175 = (2 : ZMod 46078157) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 87 * (2 : ZMod 46078157) ^ 87) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 27556671 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 46078157) ^ 351 = 31450352 := by
        calc
          (2 : ZMod 46078157) ^ 351 = (2 : ZMod 46078157) ^ (175 + 175 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 175 * (2 : ZMod 46078157) ^ 175) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 31450352 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 46078157) ^ 703 = 4477390 := by
        calc
          (2 : ZMod 46078157) ^ 703 = (2 : ZMod 46078157) ^ (351 + 351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 351 * (2 : ZMod 46078157) ^ 351) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 4477390 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 46078157) ^ 1406 = 27836895 := by
        calc
          (2 : ZMod 46078157) ^ 1406 = (2 : ZMod 46078157) ^ (703 + 703) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 703 * (2 : ZMod 46078157) ^ 703 := by rw [pow_add]
          _ = 27836895 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 46078157) ^ 2812 = 43224585 := by
        calc
          (2 : ZMod 46078157) ^ 2812 = (2 : ZMod 46078157) ^ (1406 + 1406) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 1406 * (2 : ZMod 46078157) ^ 1406 := by rw [pow_add]
          _ = 43224585 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 46078157) ^ 5624 = 33410458 := by
        calc
          (2 : ZMod 46078157) ^ 5624 = (2 : ZMod 46078157) ^ (2812 + 2812) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 2812 * (2 : ZMod 46078157) ^ 2812 := by rw [pow_add]
          _ = 33410458 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 46078157) ^ 11249 = 12836966 := by
        calc
          (2 : ZMod 46078157) ^ 11249 = (2 : ZMod 46078157) ^ (5624 + 5624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 5624 * (2 : ZMod 46078157) ^ 5624) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 12836966 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 46078157) ^ 22499 = 37961259 := by
        calc
          (2 : ZMod 46078157) ^ 22499 = (2 : ZMod 46078157) ^ (11249 + 11249 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 11249 * (2 : ZMod 46078157) ^ 11249) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 37961259 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 46078157) ^ 44998 = 9762780 := by
        calc
          (2 : ZMod 46078157) ^ 44998 = (2 : ZMod 46078157) ^ (22499 + 22499) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 22499 * (2 : ZMod 46078157) ^ 22499 := by rw [pow_add]
          _ = 9762780 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 46078157) ^ 89996 = 34980726 := by
        calc
          (2 : ZMod 46078157) ^ 89996 = (2 : ZMod 46078157) ^ (44998 + 44998) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 44998 * (2 : ZMod 46078157) ^ 44998 := by rw [pow_add]
          _ = 34980726 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 46078157) ^ 179992 = 22820332 := by
        calc
          (2 : ZMod 46078157) ^ 179992 = (2 : ZMod 46078157) ^ (89996 + 89996) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 89996 * (2 : ZMod 46078157) ^ 89996 := by rw [pow_add]
          _ = 22820332 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 46078157) ^ 359985 = 18769514 := by
        calc
          (2 : ZMod 46078157) ^ 359985 = (2 : ZMod 46078157) ^ (179992 + 179992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 179992 * (2 : ZMod 46078157) ^ 179992) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 18769514 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 46078157) ^ 719971 = 10993446 := by
        calc
          (2 : ZMod 46078157) ^ 719971 = (2 : ZMod 46078157) ^ (359985 + 359985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 359985 * (2 : ZMod 46078157) ^ 359985) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 10993446 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 46078157) ^ 1439942 = 37336408 := by
        calc
          (2 : ZMod 46078157) ^ 1439942 = (2 : ZMod 46078157) ^ (719971 + 719971) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 719971 * (2 : ZMod 46078157) ^ 719971 := by rw [pow_add]
          _ = 37336408 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 46078157) ^ 2879884 = 40414979 := by
        calc
          (2 : ZMod 46078157) ^ 2879884 = (2 : ZMod 46078157) ^ (1439942 + 1439942) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 1439942 * (2 : ZMod 46078157) ^ 1439942 := by rw [pow_add]
          _ = 40414979 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 46078157) ^ 5759769 = 25589361 := by
        calc
          (2 : ZMod 46078157) ^ 5759769 = (2 : ZMod 46078157) ^ (2879884 + 2879884 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 2879884 * (2 : ZMod 46078157) ^ 2879884) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 25589361 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 46078157) ^ 11519539 = 40977591 := by
        calc
          (2 : ZMod 46078157) ^ 11519539 = (2 : ZMod 46078157) ^ (5759769 + 5759769 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = ((2 : ZMod 46078157) ^ 5759769 * (2 : ZMod 46078157) ^ 5759769) * (2 : ZMod 46078157) := by rw [pow_succ, pow_add]
          _ = 40977591 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 46078157) ^ 23039078 = 46078156 := by
        calc
          (2 : ZMod 46078157) ^ 23039078 = (2 : ZMod 46078157) ^ (11519539 + 11519539) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 11519539 * (2 : ZMod 46078157) ^ 11519539 := by rw [pow_add]
          _ = 46078156 := by rw [factor_0_23]; decide
      change (2 : ZMod 46078157) ^ 23039078 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 46078157) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 46078157) ^ 2 = 4 := by
        calc
          (2 : ZMod 46078157) ^ 2 = (2 : ZMod 46078157) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 1 * (2 : ZMod 46078157) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 46078157) ^ 4 = 16 := by
        calc
          (2 : ZMod 46078157) ^ 4 = (2 : ZMod 46078157) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 46078157) ^ n) (by norm_num)
          _ = (2 : ZMod 46078157) ^ 2 * (2 : ZMod 46078157) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      change (2 : ZMod 46078157) ^ 4 ≠ 1
      rw [factor_1_2]
      decide

#print axioms prime_lucas_46078157

end TotientTailPeriodKiller
end Erdos249257
