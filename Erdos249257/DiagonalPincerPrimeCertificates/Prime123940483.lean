import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_123940483 : Nat.Prime 123940483 := by
  apply lucas_primality 123940483 (2 : ZMod 123940483)
  ·
      have fermat_0 : (2 : ZMod 123940483) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 123940483) ^ 3 = 8 := by
        calc
          (2 : ZMod 123940483) ^ 3 = (2 : ZMod 123940483) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 1 * (2 : ZMod 123940483) ^ 1) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 123940483) ^ 7 = 128 := by
        calc
          (2 : ZMod 123940483) ^ 7 = (2 : ZMod 123940483) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 3 * (2 : ZMod 123940483) ^ 3) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 123940483) ^ 14 = 16384 := by
        calc
          (2 : ZMod 123940483) ^ 14 = (2 : ZMod 123940483) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 7 * (2 : ZMod 123940483) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 123940483) ^ 29 = 41108980 := by
        calc
          (2 : ZMod 123940483) ^ 29 = (2 : ZMod 123940483) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 14 * (2 : ZMod 123940483) ^ 14) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 41108980 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 123940483) ^ 59 = 88797206 := by
        calc
          (2 : ZMod 123940483) ^ 59 = (2 : ZMod 123940483) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 29 * (2 : ZMod 123940483) ^ 29) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 88797206 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 123940483) ^ 118 = 108990383 := by
        calc
          (2 : ZMod 123940483) ^ 118 = (2 : ZMod 123940483) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 59 * (2 : ZMod 123940483) ^ 59 := by rw [pow_add]
          _ = 108990383 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 123940483) ^ 236 = 22742093 := by
        calc
          (2 : ZMod 123940483) ^ 236 = (2 : ZMod 123940483) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 118 * (2 : ZMod 123940483) ^ 118 := by rw [pow_add]
          _ = 22742093 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 123940483) ^ 472 = 26045030 := by
        calc
          (2 : ZMod 123940483) ^ 472 = (2 : ZMod 123940483) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 236 * (2 : ZMod 123940483) ^ 236 := by rw [pow_add]
          _ = 26045030 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 123940483) ^ 945 = 69089043 := by
        calc
          (2 : ZMod 123940483) ^ 945 = (2 : ZMod 123940483) ^ (472 + 472 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 472 * (2 : ZMod 123940483) ^ 472) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 69089043 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 123940483) ^ 1891 = 46720619 := by
        calc
          (2 : ZMod 123940483) ^ 1891 = (2 : ZMod 123940483) ^ (945 + 945 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 945 * (2 : ZMod 123940483) ^ 945) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 46720619 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 123940483) ^ 3782 = 1838931 := by
        calc
          (2 : ZMod 123940483) ^ 3782 = (2 : ZMod 123940483) ^ (1891 + 1891) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 1891 * (2 : ZMod 123940483) ^ 1891 := by rw [pow_add]
          _ = 1838931 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 123940483) ^ 7564 = 75084589 := by
        calc
          (2 : ZMod 123940483) ^ 7564 = (2 : ZMod 123940483) ^ (3782 + 3782) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 3782 * (2 : ZMod 123940483) ^ 3782 := by rw [pow_add]
          _ = 75084589 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 123940483) ^ 15129 = 12320888 := by
        calc
          (2 : ZMod 123940483) ^ 15129 = (2 : ZMod 123940483) ^ (7564 + 7564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 7564 * (2 : ZMod 123940483) ^ 7564) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 12320888 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 123940483) ^ 30258 = 118422899 := by
        calc
          (2 : ZMod 123940483) ^ 30258 = (2 : ZMod 123940483) ^ (15129 + 15129) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 15129 * (2 : ZMod 123940483) ^ 15129 := by rw [pow_add]
          _ = 118422899 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 123940483) ^ 60517 = 92894083 := by
        calc
          (2 : ZMod 123940483) ^ 60517 = (2 : ZMod 123940483) ^ (30258 + 30258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 30258 * (2 : ZMod 123940483) ^ 30258) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 92894083 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 123940483) ^ 121035 = 27386300 := by
        calc
          (2 : ZMod 123940483) ^ 121035 = (2 : ZMod 123940483) ^ (60517 + 60517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 60517 * (2 : ZMod 123940483) ^ 60517) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 27386300 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 123940483) ^ 242071 = 33858995 := by
        calc
          (2 : ZMod 123940483) ^ 242071 = (2 : ZMod 123940483) ^ (121035 + 121035 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 121035 * (2 : ZMod 123940483) ^ 121035) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 33858995 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 123940483) ^ 484142 = 46030060 := by
        calc
          (2 : ZMod 123940483) ^ 484142 = (2 : ZMod 123940483) ^ (242071 + 242071) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 242071 * (2 : ZMod 123940483) ^ 242071 := by rw [pow_add]
          _ = 46030060 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 123940483) ^ 968285 = 49127254 := by
        calc
          (2 : ZMod 123940483) ^ 968285 = (2 : ZMod 123940483) ^ (484142 + 484142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 484142 * (2 : ZMod 123940483) ^ 484142) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 49127254 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 123940483) ^ 1936570 = 9264700 := by
        calc
          (2 : ZMod 123940483) ^ 1936570 = (2 : ZMod 123940483) ^ (968285 + 968285) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 968285 * (2 : ZMod 123940483) ^ 968285 := by rw [pow_add]
          _ = 9264700 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 123940483) ^ 3873140 = 56409799 := by
        calc
          (2 : ZMod 123940483) ^ 3873140 = (2 : ZMod 123940483) ^ (1936570 + 1936570) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 1936570 * (2 : ZMod 123940483) ^ 1936570 := by rw [pow_add]
          _ = 56409799 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 123940483) ^ 7746280 = 111010781 := by
        calc
          (2 : ZMod 123940483) ^ 7746280 = (2 : ZMod 123940483) ^ (3873140 + 3873140) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 3873140 * (2 : ZMod 123940483) ^ 3873140 := by rw [pow_add]
          _ = 111010781 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 123940483) ^ 15492560 = 73314254 := by
        calc
          (2 : ZMod 123940483) ^ 15492560 = (2 : ZMod 123940483) ^ (7746280 + 7746280) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 7746280 * (2 : ZMod 123940483) ^ 7746280 := by rw [pow_add]
          _ = 73314254 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 123940483) ^ 30985120 = 114669758 := by
        calc
          (2 : ZMod 123940483) ^ 30985120 = (2 : ZMod 123940483) ^ (15492560 + 15492560) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 15492560 * (2 : ZMod 123940483) ^ 15492560 := by rw [pow_add]
          _ = 114669758 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 123940483) ^ 61970241 = 123940482 := by
        calc
          (2 : ZMod 123940483) ^ 61970241 = (2 : ZMod 123940483) ^ (30985120 + 30985120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 30985120 * (2 : ZMod 123940483) ^ 30985120) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 123940482 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 123940483) ^ 123940482 = 1 := by
        calc
          (2 : ZMod 123940483) ^ 123940482 = (2 : ZMod 123940483) ^ (61970241 + 61970241) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 61970241 * (2 : ZMod 123940483) ^ 61970241 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (509, 1), (40583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (509, 1), (40583, 1)] : List FactorBlock).map factorBlockValue).prod = 123940483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 123940483) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 123940483) ^ 3 = 8 := by
        calc
          (2 : ZMod 123940483) ^ 3 = (2 : ZMod 123940483) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 1 * (2 : ZMod 123940483) ^ 1) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 123940483) ^ 7 = 128 := by
        calc
          (2 : ZMod 123940483) ^ 7 = (2 : ZMod 123940483) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 3 * (2 : ZMod 123940483) ^ 3) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 123940483) ^ 14 = 16384 := by
        calc
          (2 : ZMod 123940483) ^ 14 = (2 : ZMod 123940483) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 7 * (2 : ZMod 123940483) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 123940483) ^ 29 = 41108980 := by
        calc
          (2 : ZMod 123940483) ^ 29 = (2 : ZMod 123940483) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 14 * (2 : ZMod 123940483) ^ 14) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 41108980 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 123940483) ^ 59 = 88797206 := by
        calc
          (2 : ZMod 123940483) ^ 59 = (2 : ZMod 123940483) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 29 * (2 : ZMod 123940483) ^ 29) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 88797206 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 123940483) ^ 118 = 108990383 := by
        calc
          (2 : ZMod 123940483) ^ 118 = (2 : ZMod 123940483) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 59 * (2 : ZMod 123940483) ^ 59 := by rw [pow_add]
          _ = 108990383 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 123940483) ^ 236 = 22742093 := by
        calc
          (2 : ZMod 123940483) ^ 236 = (2 : ZMod 123940483) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 118 * (2 : ZMod 123940483) ^ 118 := by rw [pow_add]
          _ = 22742093 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 123940483) ^ 472 = 26045030 := by
        calc
          (2 : ZMod 123940483) ^ 472 = (2 : ZMod 123940483) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 236 * (2 : ZMod 123940483) ^ 236 := by rw [pow_add]
          _ = 26045030 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 123940483) ^ 945 = 69089043 := by
        calc
          (2 : ZMod 123940483) ^ 945 = (2 : ZMod 123940483) ^ (472 + 472 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 472 * (2 : ZMod 123940483) ^ 472) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 69089043 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 123940483) ^ 1891 = 46720619 := by
        calc
          (2 : ZMod 123940483) ^ 1891 = (2 : ZMod 123940483) ^ (945 + 945 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 945 * (2 : ZMod 123940483) ^ 945) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 46720619 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 123940483) ^ 3782 = 1838931 := by
        calc
          (2 : ZMod 123940483) ^ 3782 = (2 : ZMod 123940483) ^ (1891 + 1891) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 1891 * (2 : ZMod 123940483) ^ 1891 := by rw [pow_add]
          _ = 1838931 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 123940483) ^ 7564 = 75084589 := by
        calc
          (2 : ZMod 123940483) ^ 7564 = (2 : ZMod 123940483) ^ (3782 + 3782) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 3782 * (2 : ZMod 123940483) ^ 3782 := by rw [pow_add]
          _ = 75084589 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 123940483) ^ 15129 = 12320888 := by
        calc
          (2 : ZMod 123940483) ^ 15129 = (2 : ZMod 123940483) ^ (7564 + 7564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 7564 * (2 : ZMod 123940483) ^ 7564) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 12320888 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 123940483) ^ 30258 = 118422899 := by
        calc
          (2 : ZMod 123940483) ^ 30258 = (2 : ZMod 123940483) ^ (15129 + 15129) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 15129 * (2 : ZMod 123940483) ^ 15129 := by rw [pow_add]
          _ = 118422899 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 123940483) ^ 60517 = 92894083 := by
        calc
          (2 : ZMod 123940483) ^ 60517 = (2 : ZMod 123940483) ^ (30258 + 30258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 30258 * (2 : ZMod 123940483) ^ 30258) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 92894083 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 123940483) ^ 121035 = 27386300 := by
        calc
          (2 : ZMod 123940483) ^ 121035 = (2 : ZMod 123940483) ^ (60517 + 60517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 60517 * (2 : ZMod 123940483) ^ 60517) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 27386300 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 123940483) ^ 242071 = 33858995 := by
        calc
          (2 : ZMod 123940483) ^ 242071 = (2 : ZMod 123940483) ^ (121035 + 121035 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 121035 * (2 : ZMod 123940483) ^ 121035) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 33858995 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 123940483) ^ 484142 = 46030060 := by
        calc
          (2 : ZMod 123940483) ^ 484142 = (2 : ZMod 123940483) ^ (242071 + 242071) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 242071 * (2 : ZMod 123940483) ^ 242071 := by rw [pow_add]
          _ = 46030060 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 123940483) ^ 968285 = 49127254 := by
        calc
          (2 : ZMod 123940483) ^ 968285 = (2 : ZMod 123940483) ^ (484142 + 484142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 484142 * (2 : ZMod 123940483) ^ 484142) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 49127254 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 123940483) ^ 1936570 = 9264700 := by
        calc
          (2 : ZMod 123940483) ^ 1936570 = (2 : ZMod 123940483) ^ (968285 + 968285) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 968285 * (2 : ZMod 123940483) ^ 968285 := by rw [pow_add]
          _ = 9264700 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 123940483) ^ 3873140 = 56409799 := by
        calc
          (2 : ZMod 123940483) ^ 3873140 = (2 : ZMod 123940483) ^ (1936570 + 1936570) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 1936570 * (2 : ZMod 123940483) ^ 1936570 := by rw [pow_add]
          _ = 56409799 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 123940483) ^ 7746280 = 111010781 := by
        calc
          (2 : ZMod 123940483) ^ 7746280 = (2 : ZMod 123940483) ^ (3873140 + 3873140) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 3873140 * (2 : ZMod 123940483) ^ 3873140 := by rw [pow_add]
          _ = 111010781 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 123940483) ^ 15492560 = 73314254 := by
        calc
          (2 : ZMod 123940483) ^ 15492560 = (2 : ZMod 123940483) ^ (7746280 + 7746280) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 7746280 * (2 : ZMod 123940483) ^ 7746280 := by rw [pow_add]
          _ = 73314254 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 123940483) ^ 30985120 = 114669758 := by
        calc
          (2 : ZMod 123940483) ^ 30985120 = (2 : ZMod 123940483) ^ (15492560 + 15492560) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 15492560 * (2 : ZMod 123940483) ^ 15492560 := by rw [pow_add]
          _ = 114669758 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 123940483) ^ 61970241 = 123940482 := by
        calc
          (2 : ZMod 123940483) ^ 61970241 = (2 : ZMod 123940483) ^ (30985120 + 30985120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 30985120 * (2 : ZMod 123940483) ^ 30985120) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 123940482 := by rw [factor_0_24]; decide
      change (2 : ZMod 123940483) ^ 61970241 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (2 : ZMod 123940483) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 123940483) ^ 2 = 4 := by
        calc
          (2 : ZMod 123940483) ^ 2 = (2 : ZMod 123940483) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 1 * (2 : ZMod 123940483) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 123940483) ^ 4 = 16 := by
        calc
          (2 : ZMod 123940483) ^ 4 = (2 : ZMod 123940483) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 2 * (2 : ZMod 123940483) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 123940483) ^ 9 = 512 := by
        calc
          (2 : ZMod 123940483) ^ 9 = (2 : ZMod 123940483) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 4 * (2 : ZMod 123940483) ^ 4) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 123940483) ^ 19 = 524288 := by
        calc
          (2 : ZMod 123940483) ^ 19 = (2 : ZMod 123940483) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 9 * (2 : ZMod 123940483) ^ 9) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 123940483) ^ 39 = 79771783 := by
        calc
          (2 : ZMod 123940483) ^ 39 = (2 : ZMod 123940483) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 19 * (2 : ZMod 123940483) ^ 19) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 79771783 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 123940483) ^ 78 = 41671970 := by
        calc
          (2 : ZMod 123940483) ^ 78 = (2 : ZMod 123940483) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 39 * (2 : ZMod 123940483) ^ 39 := by rw [pow_add]
          _ = 41671970 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 123940483) ^ 157 = 94757090 := by
        calc
          (2 : ZMod 123940483) ^ 157 = (2 : ZMod 123940483) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 78 * (2 : ZMod 123940483) ^ 78) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 94757090 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 123940483) ^ 315 = 24971570 := by
        calc
          (2 : ZMod 123940483) ^ 315 = (2 : ZMod 123940483) ^ (157 + 157 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 157 * (2 : ZMod 123940483) ^ 157) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 24971570 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 123940483) ^ 630 = 34956660 := by
        calc
          (2 : ZMod 123940483) ^ 630 = (2 : ZMod 123940483) ^ (315 + 315) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 315 * (2 : ZMod 123940483) ^ 315 := by rw [pow_add]
          _ = 34956660 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 123940483) ^ 1260 = 63087421 := by
        calc
          (2 : ZMod 123940483) ^ 1260 = (2 : ZMod 123940483) ^ (630 + 630) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 630 * (2 : ZMod 123940483) ^ 630 := by rw [pow_add]
          _ = 63087421 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 123940483) ^ 2521 = 80713062 := by
        calc
          (2 : ZMod 123940483) ^ 2521 = (2 : ZMod 123940483) ^ (1260 + 1260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 1260 * (2 : ZMod 123940483) ^ 1260) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 80713062 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 123940483) ^ 5043 = 81078296 := by
        calc
          (2 : ZMod 123940483) ^ 5043 = (2 : ZMod 123940483) ^ (2521 + 2521 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 2521 * (2 : ZMod 123940483) ^ 2521) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 81078296 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 123940483) ^ 10086 = 21604595 := by
        calc
          (2 : ZMod 123940483) ^ 10086 = (2 : ZMod 123940483) ^ (5043 + 5043) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 5043 * (2 : ZMod 123940483) ^ 5043 := by rw [pow_add]
          _ = 21604595 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 123940483) ^ 20172 = 29481338 := by
        calc
          (2 : ZMod 123940483) ^ 20172 = (2 : ZMod 123940483) ^ (10086 + 10086) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 10086 * (2 : ZMod 123940483) ^ 10086 := by rw [pow_add]
          _ = 29481338 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 123940483) ^ 40345 = 90416044 := by
        calc
          (2 : ZMod 123940483) ^ 40345 = (2 : ZMod 123940483) ^ (20172 + 20172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 20172 * (2 : ZMod 123940483) ^ 20172) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 90416044 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 123940483) ^ 80690 = 48337626 := by
        calc
          (2 : ZMod 123940483) ^ 80690 = (2 : ZMod 123940483) ^ (40345 + 40345) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 40345 * (2 : ZMod 123940483) ^ 40345 := by rw [pow_add]
          _ = 48337626 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 123940483) ^ 161380 = 101799876 := by
        calc
          (2 : ZMod 123940483) ^ 161380 = (2 : ZMod 123940483) ^ (80690 + 80690) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 80690 * (2 : ZMod 123940483) ^ 80690 := by rw [pow_add]
          _ = 101799876 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 123940483) ^ 322761 = 109076882 := by
        calc
          (2 : ZMod 123940483) ^ 322761 = (2 : ZMod 123940483) ^ (161380 + 161380 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 161380 * (2 : ZMod 123940483) ^ 161380) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 109076882 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 123940483) ^ 645523 = 118038633 := by
        calc
          (2 : ZMod 123940483) ^ 645523 = (2 : ZMod 123940483) ^ (322761 + 322761 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 322761 * (2 : ZMod 123940483) ^ 322761) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 118038633 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 123940483) ^ 1291046 = 95842112 := by
        calc
          (2 : ZMod 123940483) ^ 1291046 = (2 : ZMod 123940483) ^ (645523 + 645523) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 645523 * (2 : ZMod 123940483) ^ 645523 := by rw [pow_add]
          _ = 95842112 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 123940483) ^ 2582093 = 77130593 := by
        calc
          (2 : ZMod 123940483) ^ 2582093 = (2 : ZMod 123940483) ^ (1291046 + 1291046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 1291046 * (2 : ZMod 123940483) ^ 1291046) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 77130593 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 123940483) ^ 5164186 = 65389609 := by
        calc
          (2 : ZMod 123940483) ^ 5164186 = (2 : ZMod 123940483) ^ (2582093 + 2582093) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 2582093 * (2 : ZMod 123940483) ^ 2582093 := by rw [pow_add]
          _ = 65389609 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 123940483) ^ 10328373 = 111361778 := by
        calc
          (2 : ZMod 123940483) ^ 10328373 = (2 : ZMod 123940483) ^ (5164186 + 5164186 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 5164186 * (2 : ZMod 123940483) ^ 5164186) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 111361778 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 123940483) ^ 20656747 = 71067824 := by
        calc
          (2 : ZMod 123940483) ^ 20656747 = (2 : ZMod 123940483) ^ (10328373 + 10328373 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 10328373 * (2 : ZMod 123940483) ^ 10328373) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 71067824 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 123940483) ^ 41313494 = 71067823 := by
        calc
          (2 : ZMod 123940483) ^ 41313494 = (2 : ZMod 123940483) ^ (20656747 + 20656747) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 20656747 * (2 : ZMod 123940483) ^ 20656747 := by rw [pow_add]
          _ = 71067823 := by rw [factor_1_24]; decide
      change (2 : ZMod 123940483) ^ 41313494 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (2 : ZMod 123940483) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 123940483) ^ 3 = 8 := by
        calc
          (2 : ZMod 123940483) ^ 3 = (2 : ZMod 123940483) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 1 * (2 : ZMod 123940483) ^ 1) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 123940483) ^ 7 = 128 := by
        calc
          (2 : ZMod 123940483) ^ 7 = (2 : ZMod 123940483) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 3 * (2 : ZMod 123940483) ^ 3) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 123940483) ^ 14 = 16384 := by
        calc
          (2 : ZMod 123940483) ^ 14 = (2 : ZMod 123940483) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 7 * (2 : ZMod 123940483) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 123940483) ^ 29 = 41108980 := by
        calc
          (2 : ZMod 123940483) ^ 29 = (2 : ZMod 123940483) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 14 * (2 : ZMod 123940483) ^ 14) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 41108980 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 123940483) ^ 59 = 88797206 := by
        calc
          (2 : ZMod 123940483) ^ 59 = (2 : ZMod 123940483) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 29 * (2 : ZMod 123940483) ^ 29) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 88797206 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 123940483) ^ 118 = 108990383 := by
        calc
          (2 : ZMod 123940483) ^ 118 = (2 : ZMod 123940483) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 59 * (2 : ZMod 123940483) ^ 59 := by rw [pow_add]
          _ = 108990383 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 123940483) ^ 237 = 45484186 := by
        calc
          (2 : ZMod 123940483) ^ 237 = (2 : ZMod 123940483) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 118 * (2 : ZMod 123940483) ^ 118) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 45484186 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 123940483) ^ 475 = 84419757 := by
        calc
          (2 : ZMod 123940483) ^ 475 = (2 : ZMod 123940483) ^ (237 + 237 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 237 * (2 : ZMod 123940483) ^ 237) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 84419757 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 123940483) ^ 951 = 83781847 := by
        calc
          (2 : ZMod 123940483) ^ 951 = (2 : ZMod 123940483) ^ (475 + 475 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 475 * (2 : ZMod 123940483) ^ 475) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 83781847 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 123940483) ^ 1902 = 1774836 := by
        calc
          (2 : ZMod 123940483) ^ 1902 = (2 : ZMod 123940483) ^ (951 + 951) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 951 * (2 : ZMod 123940483) ^ 951 := by rw [pow_add]
          _ = 1774836 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 123940483) ^ 3804 = 95451451 := by
        calc
          (2 : ZMod 123940483) ^ 3804 = (2 : ZMod 123940483) ^ (1902 + 1902) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 1902 * (2 : ZMod 123940483) ^ 1902 := by rw [pow_add]
          _ = 95451451 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 123940483) ^ 7609 = 19397735 := by
        calc
          (2 : ZMod 123940483) ^ 7609 = (2 : ZMod 123940483) ^ (3804 + 3804 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 3804 * (2 : ZMod 123940483) ^ 3804) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 19397735 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 123940483) ^ 15218 = 95326178 := by
        calc
          (2 : ZMod 123940483) ^ 15218 = (2 : ZMod 123940483) ^ (7609 + 7609) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 7609 * (2 : ZMod 123940483) ^ 7609 := by rw [pow_add]
          _ = 95326178 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 123940483) ^ 30437 = 86355115 := by
        calc
          (2 : ZMod 123940483) ^ 30437 = (2 : ZMod 123940483) ^ (15218 + 15218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 15218 * (2 : ZMod 123940483) ^ 15218) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 86355115 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 123940483) ^ 60874 = 19855037 := by
        calc
          (2 : ZMod 123940483) ^ 60874 = (2 : ZMod 123940483) ^ (30437 + 30437) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 30437 * (2 : ZMod 123940483) ^ 30437 := by rw [pow_add]
          _ = 19855037 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 123940483) ^ 121749 = 84747898 := by
        calc
          (2 : ZMod 123940483) ^ 121749 = (2 : ZMod 123940483) ^ (60874 + 60874 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 60874 * (2 : ZMod 123940483) ^ 60874) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 84747898 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 123940483) ^ 243498 = 111993031 := by
        calc
          (2 : ZMod 123940483) ^ 243498 = (2 : ZMod 123940483) ^ (121749 + 121749) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 121749 * (2 : ZMod 123940483) ^ 121749 := by rw [pow_add]
          _ = 111993031 := by rw [factor_2_16]; decide
      change (2 : ZMod 123940483) ^ 243498 ≠ 1
      rw [factor_2_17]
      decide
    ·
      have factor_3_0 : (2 : ZMod 123940483) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 123940483) ^ 2 = 4 := by
        calc
          (2 : ZMod 123940483) ^ 2 = (2 : ZMod 123940483) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 1 * (2 : ZMod 123940483) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 123940483) ^ 5 = 32 := by
        calc
          (2 : ZMod 123940483) ^ 5 = (2 : ZMod 123940483) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 2 * (2 : ZMod 123940483) ^ 2) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 123940483) ^ 11 = 2048 := by
        calc
          (2 : ZMod 123940483) ^ 11 = (2 : ZMod 123940483) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 5 * (2 : ZMod 123940483) ^ 5) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 123940483) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 123940483) ^ 23 = (2 : ZMod 123940483) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 11 * (2 : ZMod 123940483) ^ 11) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 123940483) ^ 47 = 95337236 := by
        calc
          (2 : ZMod 123940483) ^ 47 = (2 : ZMod 123940483) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 23 * (2 : ZMod 123940483) ^ 23) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 95337236 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 123940483) ^ 95 = 95306513 := by
        calc
          (2 : ZMod 123940483) ^ 95 = (2 : ZMod 123940483) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 47 * (2 : ZMod 123940483) ^ 47) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 95306513 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 123940483) ^ 190 = 17128102 := by
        calc
          (2 : ZMod 123940483) ^ 190 = (2 : ZMod 123940483) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 95 * (2 : ZMod 123940483) ^ 95 := by rw [pow_add]
          _ = 17128102 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 123940483) ^ 381 = 90246100 := by
        calc
          (2 : ZMod 123940483) ^ 381 = (2 : ZMod 123940483) ^ (190 + 190 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 190 * (2 : ZMod 123940483) ^ 190) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 90246100 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 123940483) ^ 763 = 26891934 := by
        calc
          (2 : ZMod 123940483) ^ 763 = (2 : ZMod 123940483) ^ (381 + 381 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 381 * (2 : ZMod 123940483) ^ 381) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 26891934 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 123940483) ^ 1527 = 7960156 := by
        calc
          (2 : ZMod 123940483) ^ 1527 = (2 : ZMod 123940483) ^ (763 + 763 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = ((2 : ZMod 123940483) ^ 763 * (2 : ZMod 123940483) ^ 763) * (2 : ZMod 123940483) := by rw [pow_succ, pow_add]
          _ = 7960156 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 123940483) ^ 3054 = 7372518 := by
        calc
          (2 : ZMod 123940483) ^ 3054 = (2 : ZMod 123940483) ^ (1527 + 1527) :=
            congrArg (fun n : ℕ => (2 : ZMod 123940483) ^ n) (by norm_num)
          _ = (2 : ZMod 123940483) ^ 1527 * (2 : ZMod 123940483) ^ 1527 := by rw [pow_add]
          _ = 7372518 := by rw [factor_3_10]; decide
      change (2 : ZMod 123940483) ^ 3054 ≠ 1
      rw [factor_3_11]
      decide

#print axioms prime_lucas_123940483

end TotientTailPeriodKiller
end Erdos249257
