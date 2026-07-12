import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_248669381 : Nat.Prime 248669381 := by
  apply lucas_primality 248669381 (2 : ZMod 248669381)
  ·
      have fermat_0 : (2 : ZMod 248669381) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 248669381) ^ 3 = 8 := by
        calc
          (2 : ZMod 248669381) ^ 3 = (2 : ZMod 248669381) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 1 * (2 : ZMod 248669381) ^ 1) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 248669381) ^ 7 = 128 := by
        calc
          (2 : ZMod 248669381) ^ 7 = (2 : ZMod 248669381) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 3 * (2 : ZMod 248669381) ^ 3) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 248669381) ^ 14 = 16384 := by
        calc
          (2 : ZMod 248669381) ^ 14 = (2 : ZMod 248669381) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 7 * (2 : ZMod 248669381) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 248669381) ^ 29 = 39532150 := by
        calc
          (2 : ZMod 248669381) ^ 29 = (2 : ZMod 248669381) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 14 * (2 : ZMod 248669381) ^ 14) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 39532150 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 248669381) ^ 59 = 118175894 := by
        calc
          (2 : ZMod 248669381) ^ 59 = (2 : ZMod 248669381) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 29 * (2 : ZMod 248669381) ^ 29) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 118175894 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 248669381) ^ 118 = 176799613 := by
        calc
          (2 : ZMod 248669381) ^ 118 = (2 : ZMod 248669381) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 59 * (2 : ZMod 248669381) ^ 59 := by rw [pow_add]
          _ = 176799613 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 248669381) ^ 237 = 53931447 := by
        calc
          (2 : ZMod 248669381) ^ 237 = (2 : ZMod 248669381) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 118 * (2 : ZMod 248669381) ^ 118) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 53931447 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 248669381) ^ 474 = 22215730 := by
        calc
          (2 : ZMod 248669381) ^ 474 = (2 : ZMod 248669381) ^ (237 + 237) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 237 * (2 : ZMod 248669381) ^ 237 := by rw [pow_add]
          _ = 22215730 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 248669381) ^ 948 = 62913342 := by
        calc
          (2 : ZMod 248669381) ^ 948 = (2 : ZMod 248669381) ^ (474 + 474) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 474 * (2 : ZMod 248669381) ^ 474 := by rw [pow_add]
          _ = 62913342 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 248669381) ^ 1897 = 71403683 := by
        calc
          (2 : ZMod 248669381) ^ 1897 = (2 : ZMod 248669381) ^ (948 + 948 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 948 * (2 : ZMod 248669381) ^ 948) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 71403683 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 248669381) ^ 3794 = 220464819 := by
        calc
          (2 : ZMod 248669381) ^ 3794 = (2 : ZMod 248669381) ^ (1897 + 1897) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 1897 * (2 : ZMod 248669381) ^ 1897 := by rw [pow_add]
          _ = 220464819 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 248669381) ^ 7588 = 237752129 := by
        calc
          (2 : ZMod 248669381) ^ 7588 = (2 : ZMod 248669381) ^ (3794 + 3794) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 3794 * (2 : ZMod 248669381) ^ 3794 := by rw [pow_add]
          _ = 237752129 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 248669381) ^ 15177 = 54522075 := by
        calc
          (2 : ZMod 248669381) ^ 15177 = (2 : ZMod 248669381) ^ (7588 + 7588 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 7588 * (2 : ZMod 248669381) ^ 7588) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 54522075 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 248669381) ^ 30355 = 185625845 := by
        calc
          (2 : ZMod 248669381) ^ 30355 = (2 : ZMod 248669381) ^ (15177 + 15177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 15177 * (2 : ZMod 248669381) ^ 15177) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 185625845 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 248669381) ^ 60710 = 238811438 := by
        calc
          (2 : ZMod 248669381) ^ 60710 = (2 : ZMod 248669381) ^ (30355 + 30355) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 30355 * (2 : ZMod 248669381) ^ 30355 := by rw [pow_add]
          _ = 238811438 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 248669381) ^ 121420 = 40773973 := by
        calc
          (2 : ZMod 248669381) ^ 121420 = (2 : ZMod 248669381) ^ (60710 + 60710) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 60710 * (2 : ZMod 248669381) ^ 60710 := by rw [pow_add]
          _ = 40773973 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 248669381) ^ 242841 = 108236015 := by
        calc
          (2 : ZMod 248669381) ^ 242841 = (2 : ZMod 248669381) ^ (121420 + 121420 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 121420 * (2 : ZMod 248669381) ^ 121420) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 108236015 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 248669381) ^ 485682 = 83098659 := by
        calc
          (2 : ZMod 248669381) ^ 485682 = (2 : ZMod 248669381) ^ (242841 + 242841) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 242841 * (2 : ZMod 248669381) ^ 242841 := by rw [pow_add]
          _ = 83098659 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 248669381) ^ 971364 = 52325931 := by
        calc
          (2 : ZMod 248669381) ^ 971364 = (2 : ZMod 248669381) ^ (485682 + 485682) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 485682 * (2 : ZMod 248669381) ^ 485682 := by rw [pow_add]
          _ = 52325931 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 248669381) ^ 1942729 = 228405511 := by
        calc
          (2 : ZMod 248669381) ^ 1942729 = (2 : ZMod 248669381) ^ (971364 + 971364 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 971364 * (2 : ZMod 248669381) ^ 971364) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 228405511 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 248669381) ^ 3885459 = 71136487 := by
        calc
          (2 : ZMod 248669381) ^ 3885459 = (2 : ZMod 248669381) ^ (1942729 + 1942729 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 1942729 * (2 : ZMod 248669381) ^ 1942729) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 71136487 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 248669381) ^ 7770918 = 10926078 := by
        calc
          (2 : ZMod 248669381) ^ 7770918 = (2 : ZMod 248669381) ^ (3885459 + 3885459) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 3885459 * (2 : ZMod 248669381) ^ 3885459 := by rw [pow_add]
          _ = 10926078 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 248669381) ^ 15541836 = 222056033 := by
        calc
          (2 : ZMod 248669381) ^ 15541836 = (2 : ZMod 248669381) ^ (7770918 + 7770918) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 7770918 * (2 : ZMod 248669381) ^ 7770918 := by rw [pow_add]
          _ = 222056033 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 248669381) ^ 31083672 = 214029664 := by
        calc
          (2 : ZMod 248669381) ^ 31083672 = (2 : ZMod 248669381) ^ (15541836 + 15541836) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 15541836 * (2 : ZMod 248669381) ^ 15541836 := by rw [pow_add]
          _ = 214029664 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 248669381) ^ 62167345 = 69279433 := by
        calc
          (2 : ZMod 248669381) ^ 62167345 = (2 : ZMod 248669381) ^ (31083672 + 31083672 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 31083672 * (2 : ZMod 248669381) ^ 31083672) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 69279433 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 248669381) ^ 124334690 = 248669380 := by
        calc
          (2 : ZMod 248669381) ^ 124334690 = (2 : ZMod 248669381) ^ (62167345 + 62167345) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 62167345 * (2 : ZMod 248669381) ^ 62167345 := by rw [pow_add]
          _ = 248669380 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 248669381) ^ 248669380 = 1 := by
        calc
          (2 : ZMod 248669381) ^ 248669380 = (2 : ZMod 248669381) ^ (124334690 + 124334690) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 124334690 * (2 : ZMod 248669381) ^ 124334690 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (311, 1), (39979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (311, 1), (39979, 1)] : List FactorBlock).map factorBlockValue).prod = 248669381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 248669381) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 248669381) ^ 3 = 8 := by
        calc
          (2 : ZMod 248669381) ^ 3 = (2 : ZMod 248669381) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 1 * (2 : ZMod 248669381) ^ 1) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 248669381) ^ 7 = 128 := by
        calc
          (2 : ZMod 248669381) ^ 7 = (2 : ZMod 248669381) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 3 * (2 : ZMod 248669381) ^ 3) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 248669381) ^ 14 = 16384 := by
        calc
          (2 : ZMod 248669381) ^ 14 = (2 : ZMod 248669381) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 7 * (2 : ZMod 248669381) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 248669381) ^ 29 = 39532150 := by
        calc
          (2 : ZMod 248669381) ^ 29 = (2 : ZMod 248669381) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 14 * (2 : ZMod 248669381) ^ 14) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 39532150 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 248669381) ^ 59 = 118175894 := by
        calc
          (2 : ZMod 248669381) ^ 59 = (2 : ZMod 248669381) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 29 * (2 : ZMod 248669381) ^ 29) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 118175894 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 248669381) ^ 118 = 176799613 := by
        calc
          (2 : ZMod 248669381) ^ 118 = (2 : ZMod 248669381) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 59 * (2 : ZMod 248669381) ^ 59 := by rw [pow_add]
          _ = 176799613 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 248669381) ^ 237 = 53931447 := by
        calc
          (2 : ZMod 248669381) ^ 237 = (2 : ZMod 248669381) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 118 * (2 : ZMod 248669381) ^ 118) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 53931447 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 248669381) ^ 474 = 22215730 := by
        calc
          (2 : ZMod 248669381) ^ 474 = (2 : ZMod 248669381) ^ (237 + 237) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 237 * (2 : ZMod 248669381) ^ 237 := by rw [pow_add]
          _ = 22215730 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 248669381) ^ 948 = 62913342 := by
        calc
          (2 : ZMod 248669381) ^ 948 = (2 : ZMod 248669381) ^ (474 + 474) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 474 * (2 : ZMod 248669381) ^ 474 := by rw [pow_add]
          _ = 62913342 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 248669381) ^ 1897 = 71403683 := by
        calc
          (2 : ZMod 248669381) ^ 1897 = (2 : ZMod 248669381) ^ (948 + 948 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 948 * (2 : ZMod 248669381) ^ 948) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 71403683 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 248669381) ^ 3794 = 220464819 := by
        calc
          (2 : ZMod 248669381) ^ 3794 = (2 : ZMod 248669381) ^ (1897 + 1897) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 1897 * (2 : ZMod 248669381) ^ 1897 := by rw [pow_add]
          _ = 220464819 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 248669381) ^ 7588 = 237752129 := by
        calc
          (2 : ZMod 248669381) ^ 7588 = (2 : ZMod 248669381) ^ (3794 + 3794) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 3794 * (2 : ZMod 248669381) ^ 3794 := by rw [pow_add]
          _ = 237752129 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 248669381) ^ 15177 = 54522075 := by
        calc
          (2 : ZMod 248669381) ^ 15177 = (2 : ZMod 248669381) ^ (7588 + 7588 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 7588 * (2 : ZMod 248669381) ^ 7588) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 54522075 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 248669381) ^ 30355 = 185625845 := by
        calc
          (2 : ZMod 248669381) ^ 30355 = (2 : ZMod 248669381) ^ (15177 + 15177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 15177 * (2 : ZMod 248669381) ^ 15177) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 185625845 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 248669381) ^ 60710 = 238811438 := by
        calc
          (2 : ZMod 248669381) ^ 60710 = (2 : ZMod 248669381) ^ (30355 + 30355) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 30355 * (2 : ZMod 248669381) ^ 30355 := by rw [pow_add]
          _ = 238811438 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 248669381) ^ 121420 = 40773973 := by
        calc
          (2 : ZMod 248669381) ^ 121420 = (2 : ZMod 248669381) ^ (60710 + 60710) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 60710 * (2 : ZMod 248669381) ^ 60710 := by rw [pow_add]
          _ = 40773973 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 248669381) ^ 242841 = 108236015 := by
        calc
          (2 : ZMod 248669381) ^ 242841 = (2 : ZMod 248669381) ^ (121420 + 121420 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 121420 * (2 : ZMod 248669381) ^ 121420) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 108236015 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 248669381) ^ 485682 = 83098659 := by
        calc
          (2 : ZMod 248669381) ^ 485682 = (2 : ZMod 248669381) ^ (242841 + 242841) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 242841 * (2 : ZMod 248669381) ^ 242841 := by rw [pow_add]
          _ = 83098659 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 248669381) ^ 971364 = 52325931 := by
        calc
          (2 : ZMod 248669381) ^ 971364 = (2 : ZMod 248669381) ^ (485682 + 485682) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 485682 * (2 : ZMod 248669381) ^ 485682 := by rw [pow_add]
          _ = 52325931 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 248669381) ^ 1942729 = 228405511 := by
        calc
          (2 : ZMod 248669381) ^ 1942729 = (2 : ZMod 248669381) ^ (971364 + 971364 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 971364 * (2 : ZMod 248669381) ^ 971364) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 228405511 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 248669381) ^ 3885459 = 71136487 := by
        calc
          (2 : ZMod 248669381) ^ 3885459 = (2 : ZMod 248669381) ^ (1942729 + 1942729 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 1942729 * (2 : ZMod 248669381) ^ 1942729) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 71136487 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 248669381) ^ 7770918 = 10926078 := by
        calc
          (2 : ZMod 248669381) ^ 7770918 = (2 : ZMod 248669381) ^ (3885459 + 3885459) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 3885459 * (2 : ZMod 248669381) ^ 3885459 := by rw [pow_add]
          _ = 10926078 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 248669381) ^ 15541836 = 222056033 := by
        calc
          (2 : ZMod 248669381) ^ 15541836 = (2 : ZMod 248669381) ^ (7770918 + 7770918) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 7770918 * (2 : ZMod 248669381) ^ 7770918 := by rw [pow_add]
          _ = 222056033 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 248669381) ^ 31083672 = 214029664 := by
        calc
          (2 : ZMod 248669381) ^ 31083672 = (2 : ZMod 248669381) ^ (15541836 + 15541836) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 15541836 * (2 : ZMod 248669381) ^ 15541836 := by rw [pow_add]
          _ = 214029664 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 248669381) ^ 62167345 = 69279433 := by
        calc
          (2 : ZMod 248669381) ^ 62167345 = (2 : ZMod 248669381) ^ (31083672 + 31083672 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 31083672 * (2 : ZMod 248669381) ^ 31083672) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 69279433 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 248669381) ^ 124334690 = 248669380 := by
        calc
          (2 : ZMod 248669381) ^ 124334690 = (2 : ZMod 248669381) ^ (62167345 + 62167345) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 62167345 * (2 : ZMod 248669381) ^ 62167345 := by rw [pow_add]
          _ = 248669380 := by rw [factor_0_25]; decide
      change (2 : ZMod 248669381) ^ 124334690 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (2 : ZMod 248669381) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 248669381) ^ 2 = 4 := by
        calc
          (2 : ZMod 248669381) ^ 2 = (2 : ZMod 248669381) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 1 * (2 : ZMod 248669381) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 248669381) ^ 5 = 32 := by
        calc
          (2 : ZMod 248669381) ^ 5 = (2 : ZMod 248669381) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 2 * (2 : ZMod 248669381) ^ 2) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 248669381) ^ 11 = 2048 := by
        calc
          (2 : ZMod 248669381) ^ 11 = (2 : ZMod 248669381) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 5 * (2 : ZMod 248669381) ^ 5) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 248669381) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 248669381) ^ 23 = (2 : ZMod 248669381) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 11 * (2 : ZMod 248669381) ^ 11) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 248669381) ^ 47 = 68145806 := by
        calc
          (2 : ZMod 248669381) ^ 47 = (2 : ZMod 248669381) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 23 * (2 : ZMod 248669381) ^ 23) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 68145806 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 248669381) ^ 94 = 167760217 := by
        calc
          (2 : ZMod 248669381) ^ 94 = (2 : ZMod 248669381) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 47 * (2 : ZMod 248669381) ^ 47 := by rw [pow_add]
          _ = 167760217 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 248669381) ^ 189 = 241152479 := by
        calc
          (2 : ZMod 248669381) ^ 189 = (2 : ZMod 248669381) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 94 * (2 : ZMod 248669381) ^ 94) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 241152479 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 248669381) ^ 379 = 79829139 := by
        calc
          (2 : ZMod 248669381) ^ 379 = (2 : ZMod 248669381) ^ (189 + 189 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 189 * (2 : ZMod 248669381) ^ 189) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 79829139 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 248669381) ^ 758 = 176146456 := by
        calc
          (2 : ZMod 248669381) ^ 758 = (2 : ZMod 248669381) ^ (379 + 379) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 379 * (2 : ZMod 248669381) ^ 379 := by rw [pow_add]
          _ = 176146456 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 248669381) ^ 1517 = 59402643 := by
        calc
          (2 : ZMod 248669381) ^ 1517 = (2 : ZMod 248669381) ^ (758 + 758 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 758 * (2 : ZMod 248669381) ^ 758) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 59402643 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 248669381) ^ 3035 = 51446972 := by
        calc
          (2 : ZMod 248669381) ^ 3035 = (2 : ZMod 248669381) ^ (1517 + 1517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 1517 * (2 : ZMod 248669381) ^ 1517) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 51446972 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 248669381) ^ 6071 = 80880538 := by
        calc
          (2 : ZMod 248669381) ^ 6071 = (2 : ZMod 248669381) ^ (3035 + 3035 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 3035 * (2 : ZMod 248669381) ^ 3035) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 80880538 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 248669381) ^ 12142 = 71453222 := by
        calc
          (2 : ZMod 248669381) ^ 12142 = (2 : ZMod 248669381) ^ (6071 + 6071) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 6071 * (2 : ZMod 248669381) ^ 6071 := by rw [pow_add]
          _ = 71453222 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 248669381) ^ 24284 = 78098354 := by
        calc
          (2 : ZMod 248669381) ^ 24284 = (2 : ZMod 248669381) ^ (12142 + 12142) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 12142 * (2 : ZMod 248669381) ^ 12142 := by rw [pow_add]
          _ = 78098354 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 248669381) ^ 48568 = 18447175 := by
        calc
          (2 : ZMod 248669381) ^ 48568 = (2 : ZMod 248669381) ^ (24284 + 24284) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 24284 * (2 : ZMod 248669381) ^ 24284 := by rw [pow_add]
          _ = 18447175 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 248669381) ^ 97136 = 185647269 := by
        calc
          (2 : ZMod 248669381) ^ 97136 = (2 : ZMod 248669381) ^ (48568 + 48568) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 48568 * (2 : ZMod 248669381) ^ 48568 := by rw [pow_add]
          _ = 185647269 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 248669381) ^ 194272 = 206515727 := by
        calc
          (2 : ZMod 248669381) ^ 194272 = (2 : ZMod 248669381) ^ (97136 + 97136) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 97136 * (2 : ZMod 248669381) ^ 97136 := by rw [pow_add]
          _ = 206515727 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 248669381) ^ 388545 = 145848122 := by
        calc
          (2 : ZMod 248669381) ^ 388545 = (2 : ZMod 248669381) ^ (194272 + 194272 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 194272 * (2 : ZMod 248669381) ^ 194272) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 145848122 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 248669381) ^ 777091 = 235551721 := by
        calc
          (2 : ZMod 248669381) ^ 777091 = (2 : ZMod 248669381) ^ (388545 + 388545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 388545 * (2 : ZMod 248669381) ^ 388545) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 235551721 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 248669381) ^ 1554183 = 17916250 := by
        calc
          (2 : ZMod 248669381) ^ 1554183 = (2 : ZMod 248669381) ^ (777091 + 777091 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 777091 * (2 : ZMod 248669381) ^ 777091) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 17916250 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 248669381) ^ 3108367 = 6593063 := by
        calc
          (2 : ZMod 248669381) ^ 3108367 = (2 : ZMod 248669381) ^ (1554183 + 1554183 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 1554183 * (2 : ZMod 248669381) ^ 1554183) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 6593063 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 248669381) ^ 6216734 = 77245645 := by
        calc
          (2 : ZMod 248669381) ^ 6216734 = (2 : ZMod 248669381) ^ (3108367 + 3108367) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 3108367 * (2 : ZMod 248669381) ^ 3108367 := by rw [pow_add]
          _ = 77245645 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 248669381) ^ 12433469 = 223929405 := by
        calc
          (2 : ZMod 248669381) ^ 12433469 = (2 : ZMod 248669381) ^ (6216734 + 6216734 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 6216734 * (2 : ZMod 248669381) ^ 6216734) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 223929405 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 248669381) ^ 24866938 = 52846130 := by
        calc
          (2 : ZMod 248669381) ^ 24866938 = (2 : ZMod 248669381) ^ (12433469 + 12433469) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 12433469 * (2 : ZMod 248669381) ^ 12433469 := by rw [pow_add]
          _ = 52846130 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 248669381) ^ 49733876 = 142975632 := by
        calc
          (2 : ZMod 248669381) ^ 49733876 = (2 : ZMod 248669381) ^ (24866938 + 24866938) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 24866938 * (2 : ZMod 248669381) ^ 24866938 := by rw [pow_add]
          _ = 142975632 := by rw [factor_1_24]; decide
      change (2 : ZMod 248669381) ^ 49733876 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (2 : ZMod 248669381) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 248669381) ^ 3 = 8 := by
        calc
          (2 : ZMod 248669381) ^ 3 = (2 : ZMod 248669381) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 1 * (2 : ZMod 248669381) ^ 1) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 248669381) ^ 6 = 64 := by
        calc
          (2 : ZMod 248669381) ^ 6 = (2 : ZMod 248669381) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 3 * (2 : ZMod 248669381) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 248669381) ^ 12 = 4096 := by
        calc
          (2 : ZMod 248669381) ^ 12 = (2 : ZMod 248669381) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 6 * (2 : ZMod 248669381) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 248669381) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 248669381) ^ 24 = (2 : ZMod 248669381) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 12 * (2 : ZMod 248669381) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 248669381) ^ 48 = 136291612 := by
        calc
          (2 : ZMod 248669381) ^ 48 = (2 : ZMod 248669381) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 24 * (2 : ZMod 248669381) ^ 24 := by rw [pow_add]
          _ = 136291612 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 248669381) ^ 97 = 98734831 := by
        calc
          (2 : ZMod 248669381) ^ 97 = (2 : ZMod 248669381) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 48 * (2 : ZMod 248669381) ^ 48) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 98734831 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 248669381) ^ 195 = 16257034 := by
        calc
          (2 : ZMod 248669381) ^ 195 = (2 : ZMod 248669381) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 97 * (2 : ZMod 248669381) ^ 97) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 16257034 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 248669381) ^ 390 = 114293355 := by
        calc
          (2 : ZMod 248669381) ^ 390 = (2 : ZMod 248669381) ^ (195 + 195) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 195 * (2 : ZMod 248669381) ^ 195 := by rw [pow_add]
          _ = 114293355 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 248669381) ^ 780 = 133872764 := by
        calc
          (2 : ZMod 248669381) ^ 780 = (2 : ZMod 248669381) ^ (390 + 390) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 390 * (2 : ZMod 248669381) ^ 390 := by rw [pow_add]
          _ = 133872764 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 248669381) ^ 1561 = 171125462 := by
        calc
          (2 : ZMod 248669381) ^ 1561 = (2 : ZMod 248669381) ^ (780 + 780 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 780 * (2 : ZMod 248669381) ^ 780) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 171125462 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 248669381) ^ 3123 = 232830223 := by
        calc
          (2 : ZMod 248669381) ^ 3123 = (2 : ZMod 248669381) ^ (1561 + 1561 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 1561 * (2 : ZMod 248669381) ^ 1561) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 232830223 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 248669381) ^ 6246 = 117698779 := by
        calc
          (2 : ZMod 248669381) ^ 6246 = (2 : ZMod 248669381) ^ (3123 + 3123) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 3123 * (2 : ZMod 248669381) ^ 3123 := by rw [pow_add]
          _ = 117698779 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 248669381) ^ 12493 = 29876347 := by
        calc
          (2 : ZMod 248669381) ^ 12493 = (2 : ZMod 248669381) ^ (6246 + 6246 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 6246 * (2 : ZMod 248669381) ^ 6246) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 29876347 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 248669381) ^ 24986 = 102328100 := by
        calc
          (2 : ZMod 248669381) ^ 24986 = (2 : ZMod 248669381) ^ (12493 + 12493) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 12493 * (2 : ZMod 248669381) ^ 12493 := by rw [pow_add]
          _ = 102328100 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 248669381) ^ 49973 = 5401259 := by
        calc
          (2 : ZMod 248669381) ^ 49973 = (2 : ZMod 248669381) ^ (24986 + 24986 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 24986 * (2 : ZMod 248669381) ^ 24986) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 5401259 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 248669381) ^ 99947 = 160020465 := by
        calc
          (2 : ZMod 248669381) ^ 99947 = (2 : ZMod 248669381) ^ (49973 + 49973 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 49973 * (2 : ZMod 248669381) ^ 49973) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 160020465 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 248669381) ^ 199895 = 239954281 := by
        calc
          (2 : ZMod 248669381) ^ 199895 = (2 : ZMod 248669381) ^ (99947 + 99947 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 99947 * (2 : ZMod 248669381) ^ 99947) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 239954281 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 248669381) ^ 399790 = 138285503 := by
        calc
          (2 : ZMod 248669381) ^ 399790 = (2 : ZMod 248669381) ^ (199895 + 199895) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 199895 * (2 : ZMod 248669381) ^ 199895 := by rw [pow_add]
          _ = 138285503 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 248669381) ^ 799580 = 37493065 := by
        calc
          (2 : ZMod 248669381) ^ 799580 = (2 : ZMod 248669381) ^ (399790 + 399790) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 399790 * (2 : ZMod 248669381) ^ 399790 := by rw [pow_add]
          _ = 37493065 := by rw [factor_2_18]; decide
      change (2 : ZMod 248669381) ^ 799580 ≠ 1
      rw [factor_2_19]
      decide
    ·
      have factor_3_0 : (2 : ZMod 248669381) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 248669381) ^ 3 = 8 := by
        calc
          (2 : ZMod 248669381) ^ 3 = (2 : ZMod 248669381) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 1 * (2 : ZMod 248669381) ^ 1) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 248669381) ^ 6 = 64 := by
        calc
          (2 : ZMod 248669381) ^ 6 = (2 : ZMod 248669381) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 3 * (2 : ZMod 248669381) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 248669381) ^ 12 = 4096 := by
        calc
          (2 : ZMod 248669381) ^ 12 = (2 : ZMod 248669381) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 6 * (2 : ZMod 248669381) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 248669381) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 248669381) ^ 24 = (2 : ZMod 248669381) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 12 * (2 : ZMod 248669381) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 248669381) ^ 48 = 136291612 := by
        calc
          (2 : ZMod 248669381) ^ 48 = (2 : ZMod 248669381) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 24 * (2 : ZMod 248669381) ^ 24 := by rw [pow_add]
          _ = 136291612 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 248669381) ^ 97 = 98734831 := by
        calc
          (2 : ZMod 248669381) ^ 97 = (2 : ZMod 248669381) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 48 * (2 : ZMod 248669381) ^ 48) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 98734831 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 248669381) ^ 194 = 8128517 := by
        calc
          (2 : ZMod 248669381) ^ 194 = (2 : ZMod 248669381) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 97 * (2 : ZMod 248669381) ^ 97 := by rw [pow_add]
          _ = 8128517 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 248669381) ^ 388 = 90740684 := by
        calc
          (2 : ZMod 248669381) ^ 388 = (2 : ZMod 248669381) ^ (194 + 194) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 194 * (2 : ZMod 248669381) ^ 194 := by rw [pow_add]
          _ = 90740684 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 248669381) ^ 777 = 141068786 := by
        calc
          (2 : ZMod 248669381) ^ 777 = (2 : ZMod 248669381) ^ (388 + 388 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 388 * (2 : ZMod 248669381) ^ 388) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 141068786 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 248669381) ^ 1555 = 134779444 := by
        calc
          (2 : ZMod 248669381) ^ 1555 = (2 : ZMod 248669381) ^ (777 + 777 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = ((2 : ZMod 248669381) ^ 777 * (2 : ZMod 248669381) ^ 777) * (2 : ZMod 248669381) := by rw [pow_succ, pow_add]
          _ = 134779444 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 248669381) ^ 3110 = 64047431 := by
        calc
          (2 : ZMod 248669381) ^ 3110 = (2 : ZMod 248669381) ^ (1555 + 1555) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 1555 * (2 : ZMod 248669381) ^ 1555 := by rw [pow_add]
          _ = 64047431 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 248669381) ^ 6220 = 182471328 := by
        calc
          (2 : ZMod 248669381) ^ 6220 = (2 : ZMod 248669381) ^ (3110 + 3110) :=
            congrArg (fun n : ℕ => (2 : ZMod 248669381) ^ n) (by norm_num)
          _ = (2 : ZMod 248669381) ^ 3110 * (2 : ZMod 248669381) ^ 3110 := by rw [pow_add]
          _ = 182471328 := by rw [factor_3_11]; decide
      change (2 : ZMod 248669381) ^ 6220 ≠ 1
      rw [factor_3_12]
      decide

#print axioms prime_lucas_248669381

end TotientTailPeriodKiller
end Erdos249257
