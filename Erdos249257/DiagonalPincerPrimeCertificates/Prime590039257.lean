import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_590039257 : Nat.Prime 590039257 := by
  apply lucas_primality 590039257 (5 : ZMod 590039257)
  ·
      have fermat_0 : (5 : ZMod 590039257) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 590039257) ^ 2 = 25 := by
        calc
          (5 : ZMod 590039257) ^ 2 = (5 : ZMod 590039257) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 1 * (5 : ZMod 590039257) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 590039257) ^ 4 = 625 := by
        calc
          (5 : ZMod 590039257) ^ 4 = (5 : ZMod 590039257) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 2 * (5 : ZMod 590039257) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 590039257) ^ 8 = 390625 := by
        calc
          (5 : ZMod 590039257) ^ 8 = (5 : ZMod 590039257) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 4 * (5 : ZMod 590039257) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 590039257) ^ 17 = 18693824 := by
        calc
          (5 : ZMod 590039257) ^ 17 = (5 : ZMod 590039257) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 8 * (5 : ZMod 590039257) ^ 8) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 18693824 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 590039257) ^ 35 = 226175640 := by
        calc
          (5 : ZMod 590039257) ^ 35 = (5 : ZMod 590039257) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 17 * (5 : ZMod 590039257) ^ 17) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 226175640 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 590039257) ^ 70 = 142951019 := by
        calc
          (5 : ZMod 590039257) ^ 70 = (5 : ZMod 590039257) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 35 * (5 : ZMod 590039257) ^ 35 := by rw [pow_add]
          _ = 142951019 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 590039257) ^ 140 = 214543915 := by
        calc
          (5 : ZMod 590039257) ^ 140 = (5 : ZMod 590039257) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 70 * (5 : ZMod 590039257) ^ 70 := by rw [pow_add]
          _ = 214543915 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 590039257) ^ 281 = 211878224 := by
        calc
          (5 : ZMod 590039257) ^ 281 = (5 : ZMod 590039257) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 140 * (5 : ZMod 590039257) ^ 140) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 211878224 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 590039257) ^ 562 = 186798136 := by
        calc
          (5 : ZMod 590039257) ^ 562 = (5 : ZMod 590039257) ^ (281 + 281) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 281 * (5 : ZMod 590039257) ^ 281 := by rw [pow_add]
          _ = 186798136 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 590039257) ^ 1125 = 248915726 := by
        calc
          (5 : ZMod 590039257) ^ 1125 = (5 : ZMod 590039257) ^ (562 + 562 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 562 * (5 : ZMod 590039257) ^ 562) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 248915726 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 590039257) ^ 2250 = 458017752 := by
        calc
          (5 : ZMod 590039257) ^ 2250 = (5 : ZMod 590039257) ^ (1125 + 1125) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 1125 * (5 : ZMod 590039257) ^ 1125 := by rw [pow_add]
          _ = 458017752 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 590039257) ^ 4501 = 140669483 := by
        calc
          (5 : ZMod 590039257) ^ 4501 = (5 : ZMod 590039257) ^ (2250 + 2250 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 2250 * (5 : ZMod 590039257) ^ 2250) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 140669483 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 590039257) ^ 9003 = 498300122 := by
        calc
          (5 : ZMod 590039257) ^ 9003 = (5 : ZMod 590039257) ^ (4501 + 4501 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 4501 * (5 : ZMod 590039257) ^ 4501) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 498300122 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 590039257) ^ 18006 = 285423707 := by
        calc
          (5 : ZMod 590039257) ^ 18006 = (5 : ZMod 590039257) ^ (9003 + 9003) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 9003 * (5 : ZMod 590039257) ^ 9003 := by rw [pow_add]
          _ = 285423707 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 590039257) ^ 36013 = 177384640 := by
        calc
          (5 : ZMod 590039257) ^ 36013 = (5 : ZMod 590039257) ^ (18006 + 18006 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 18006 * (5 : ZMod 590039257) ^ 18006) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 177384640 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 590039257) ^ 72026 = 290811698 := by
        calc
          (5 : ZMod 590039257) ^ 72026 = (5 : ZMod 590039257) ^ (36013 + 36013) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 36013 * (5 : ZMod 590039257) ^ 36013 := by rw [pow_add]
          _ = 290811698 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 590039257) ^ 144052 = 43519703 := by
        calc
          (5 : ZMod 590039257) ^ 144052 = (5 : ZMod 590039257) ^ (72026 + 72026) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 72026 * (5 : ZMod 590039257) ^ 72026 := by rw [pow_add]
          _ = 43519703 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 590039257) ^ 288105 = 81643942 := by
        calc
          (5 : ZMod 590039257) ^ 288105 = (5 : ZMod 590039257) ^ (144052 + 144052 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 144052 * (5 : ZMod 590039257) ^ 144052) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 81643942 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 590039257) ^ 576210 = 185005407 := by
        calc
          (5 : ZMod 590039257) ^ 576210 = (5 : ZMod 590039257) ^ (288105 + 288105) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 288105 * (5 : ZMod 590039257) ^ 288105 := by rw [pow_add]
          _ = 185005407 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 590039257) ^ 1152420 = 448983364 := by
        calc
          (5 : ZMod 590039257) ^ 1152420 = (5 : ZMod 590039257) ^ (576210 + 576210) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 576210 * (5 : ZMod 590039257) ^ 576210 := by rw [pow_add]
          _ = 448983364 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 590039257) ^ 2304840 = 421354347 := by
        calc
          (5 : ZMod 590039257) ^ 2304840 = (5 : ZMod 590039257) ^ (1152420 + 1152420) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 1152420 * (5 : ZMod 590039257) ^ 1152420 := by rw [pow_add]
          _ = 421354347 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 590039257) ^ 4609681 = 319176132 := by
        calc
          (5 : ZMod 590039257) ^ 4609681 = (5 : ZMod 590039257) ^ (2304840 + 2304840 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 2304840 * (5 : ZMod 590039257) ^ 2304840) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 319176132 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 590039257) ^ 9219363 = 397435475 := by
        calc
          (5 : ZMod 590039257) ^ 9219363 = (5 : ZMod 590039257) ^ (4609681 + 4609681 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 4609681 * (5 : ZMod 590039257) ^ 4609681) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 397435475 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 590039257) ^ 18438726 = 323278204 := by
        calc
          (5 : ZMod 590039257) ^ 18438726 = (5 : ZMod 590039257) ^ (9219363 + 9219363) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 9219363 * (5 : ZMod 590039257) ^ 9219363 := by rw [pow_add]
          _ = 323278204 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 590039257) ^ 36877453 = 420860658 := by
        calc
          (5 : ZMod 590039257) ^ 36877453 = (5 : ZMod 590039257) ^ (18438726 + 18438726 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 18438726 * (5 : ZMod 590039257) ^ 18438726) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 420860658 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 590039257) ^ 73754907 = 330411160 := by
        calc
          (5 : ZMod 590039257) ^ 73754907 = (5 : ZMod 590039257) ^ (36877453 + 36877453 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 36877453 * (5 : ZMod 590039257) ^ 36877453) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 330411160 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 590039257) ^ 147509814 = 237997284 := by
        calc
          (5 : ZMod 590039257) ^ 147509814 = (5 : ZMod 590039257) ^ (73754907 + 73754907) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 73754907 * (5 : ZMod 590039257) ^ 73754907 := by rw [pow_add]
          _ = 237997284 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 590039257) ^ 295019628 = 590039256 := by
        calc
          (5 : ZMod 590039257) ^ 295019628 = (5 : ZMod 590039257) ^ (147509814 + 147509814) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 147509814 * (5 : ZMod 590039257) ^ 147509814 := by rw [pow_add]
          _ = 590039256 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 590039257) ^ 590039256 = 1 := by
        calc
          (5 : ZMod 590039257) ^ 590039256 = (5 : ZMod 590039257) ^ (295019628 + 295019628) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 295019628 * (5 : ZMod 590039257) ^ 295019628 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (24584969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (24584969, 1)] : List FactorBlock).map factorBlockValue).prod = 590039257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 590039257) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 590039257) ^ 2 = 25 := by
        calc
          (5 : ZMod 590039257) ^ 2 = (5 : ZMod 590039257) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 1 * (5 : ZMod 590039257) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 590039257) ^ 4 = 625 := by
        calc
          (5 : ZMod 590039257) ^ 4 = (5 : ZMod 590039257) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 2 * (5 : ZMod 590039257) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 590039257) ^ 8 = 390625 := by
        calc
          (5 : ZMod 590039257) ^ 8 = (5 : ZMod 590039257) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 4 * (5 : ZMod 590039257) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 590039257) ^ 17 = 18693824 := by
        calc
          (5 : ZMod 590039257) ^ 17 = (5 : ZMod 590039257) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 8 * (5 : ZMod 590039257) ^ 8) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 18693824 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 590039257) ^ 35 = 226175640 := by
        calc
          (5 : ZMod 590039257) ^ 35 = (5 : ZMod 590039257) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 17 * (5 : ZMod 590039257) ^ 17) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 226175640 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 590039257) ^ 70 = 142951019 := by
        calc
          (5 : ZMod 590039257) ^ 70 = (5 : ZMod 590039257) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 35 * (5 : ZMod 590039257) ^ 35 := by rw [pow_add]
          _ = 142951019 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 590039257) ^ 140 = 214543915 := by
        calc
          (5 : ZMod 590039257) ^ 140 = (5 : ZMod 590039257) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 70 * (5 : ZMod 590039257) ^ 70 := by rw [pow_add]
          _ = 214543915 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 590039257) ^ 281 = 211878224 := by
        calc
          (5 : ZMod 590039257) ^ 281 = (5 : ZMod 590039257) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 140 * (5 : ZMod 590039257) ^ 140) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 211878224 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 590039257) ^ 562 = 186798136 := by
        calc
          (5 : ZMod 590039257) ^ 562 = (5 : ZMod 590039257) ^ (281 + 281) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 281 * (5 : ZMod 590039257) ^ 281 := by rw [pow_add]
          _ = 186798136 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 590039257) ^ 1125 = 248915726 := by
        calc
          (5 : ZMod 590039257) ^ 1125 = (5 : ZMod 590039257) ^ (562 + 562 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 562 * (5 : ZMod 590039257) ^ 562) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 248915726 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 590039257) ^ 2250 = 458017752 := by
        calc
          (5 : ZMod 590039257) ^ 2250 = (5 : ZMod 590039257) ^ (1125 + 1125) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 1125 * (5 : ZMod 590039257) ^ 1125 := by rw [pow_add]
          _ = 458017752 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 590039257) ^ 4501 = 140669483 := by
        calc
          (5 : ZMod 590039257) ^ 4501 = (5 : ZMod 590039257) ^ (2250 + 2250 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 2250 * (5 : ZMod 590039257) ^ 2250) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 140669483 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 590039257) ^ 9003 = 498300122 := by
        calc
          (5 : ZMod 590039257) ^ 9003 = (5 : ZMod 590039257) ^ (4501 + 4501 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 4501 * (5 : ZMod 590039257) ^ 4501) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 498300122 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 590039257) ^ 18006 = 285423707 := by
        calc
          (5 : ZMod 590039257) ^ 18006 = (5 : ZMod 590039257) ^ (9003 + 9003) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 9003 * (5 : ZMod 590039257) ^ 9003 := by rw [pow_add]
          _ = 285423707 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 590039257) ^ 36013 = 177384640 := by
        calc
          (5 : ZMod 590039257) ^ 36013 = (5 : ZMod 590039257) ^ (18006 + 18006 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 18006 * (5 : ZMod 590039257) ^ 18006) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 177384640 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 590039257) ^ 72026 = 290811698 := by
        calc
          (5 : ZMod 590039257) ^ 72026 = (5 : ZMod 590039257) ^ (36013 + 36013) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 36013 * (5 : ZMod 590039257) ^ 36013 := by rw [pow_add]
          _ = 290811698 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 590039257) ^ 144052 = 43519703 := by
        calc
          (5 : ZMod 590039257) ^ 144052 = (5 : ZMod 590039257) ^ (72026 + 72026) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 72026 * (5 : ZMod 590039257) ^ 72026 := by rw [pow_add]
          _ = 43519703 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 590039257) ^ 288105 = 81643942 := by
        calc
          (5 : ZMod 590039257) ^ 288105 = (5 : ZMod 590039257) ^ (144052 + 144052 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 144052 * (5 : ZMod 590039257) ^ 144052) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 81643942 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 590039257) ^ 576210 = 185005407 := by
        calc
          (5 : ZMod 590039257) ^ 576210 = (5 : ZMod 590039257) ^ (288105 + 288105) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 288105 * (5 : ZMod 590039257) ^ 288105 := by rw [pow_add]
          _ = 185005407 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 590039257) ^ 1152420 = 448983364 := by
        calc
          (5 : ZMod 590039257) ^ 1152420 = (5 : ZMod 590039257) ^ (576210 + 576210) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 576210 * (5 : ZMod 590039257) ^ 576210 := by rw [pow_add]
          _ = 448983364 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 590039257) ^ 2304840 = 421354347 := by
        calc
          (5 : ZMod 590039257) ^ 2304840 = (5 : ZMod 590039257) ^ (1152420 + 1152420) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 1152420 * (5 : ZMod 590039257) ^ 1152420 := by rw [pow_add]
          _ = 421354347 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 590039257) ^ 4609681 = 319176132 := by
        calc
          (5 : ZMod 590039257) ^ 4609681 = (5 : ZMod 590039257) ^ (2304840 + 2304840 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 2304840 * (5 : ZMod 590039257) ^ 2304840) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 319176132 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 590039257) ^ 9219363 = 397435475 := by
        calc
          (5 : ZMod 590039257) ^ 9219363 = (5 : ZMod 590039257) ^ (4609681 + 4609681 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 4609681 * (5 : ZMod 590039257) ^ 4609681) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 397435475 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 590039257) ^ 18438726 = 323278204 := by
        calc
          (5 : ZMod 590039257) ^ 18438726 = (5 : ZMod 590039257) ^ (9219363 + 9219363) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 9219363 * (5 : ZMod 590039257) ^ 9219363 := by rw [pow_add]
          _ = 323278204 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 590039257) ^ 36877453 = 420860658 := by
        calc
          (5 : ZMod 590039257) ^ 36877453 = (5 : ZMod 590039257) ^ (18438726 + 18438726 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 18438726 * (5 : ZMod 590039257) ^ 18438726) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 420860658 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 590039257) ^ 73754907 = 330411160 := by
        calc
          (5 : ZMod 590039257) ^ 73754907 = (5 : ZMod 590039257) ^ (36877453 + 36877453 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 36877453 * (5 : ZMod 590039257) ^ 36877453) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 330411160 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 590039257) ^ 147509814 = 237997284 := by
        calc
          (5 : ZMod 590039257) ^ 147509814 = (5 : ZMod 590039257) ^ (73754907 + 73754907) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 73754907 * (5 : ZMod 590039257) ^ 73754907 := by rw [pow_add]
          _ = 237997284 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 590039257) ^ 295019628 = 590039256 := by
        calc
          (5 : ZMod 590039257) ^ 295019628 = (5 : ZMod 590039257) ^ (147509814 + 147509814) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 147509814 * (5 : ZMod 590039257) ^ 147509814 := by rw [pow_add]
          _ = 590039256 := by rw [factor_0_27]; decide
      change (5 : ZMod 590039257) ^ 295019628 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (5 : ZMod 590039257) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 590039257) ^ 2 = 25 := by
        calc
          (5 : ZMod 590039257) ^ 2 = (5 : ZMod 590039257) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 1 * (5 : ZMod 590039257) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 590039257) ^ 5 = 3125 := by
        calc
          (5 : ZMod 590039257) ^ 5 = (5 : ZMod 590039257) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 2 * (5 : ZMod 590039257) ^ 2) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 590039257) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 590039257) ^ 11 = (5 : ZMod 590039257) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 5 * (5 : ZMod 590039257) ^ 5) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 590039257) ^ 23 = 21567785 := by
        calc
          (5 : ZMod 590039257) ^ 23 = (5 : ZMod 590039257) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 11 * (5 : ZMod 590039257) ^ 11) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 21567785 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 590039257) ^ 46 = 100765135 := by
        calc
          (5 : ZMod 590039257) ^ 46 = (5 : ZMod 590039257) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 23 * (5 : ZMod 590039257) ^ 23 := by rw [pow_add]
          _ = 100765135 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 590039257) ^ 93 = 583446016 := by
        calc
          (5 : ZMod 590039257) ^ 93 = (5 : ZMod 590039257) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 46 * (5 : ZMod 590039257) ^ 46) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 583446016 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 590039257) ^ 187 = 193240801 := by
        calc
          (5 : ZMod 590039257) ^ 187 = (5 : ZMod 590039257) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 93 * (5 : ZMod 590039257) ^ 93) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 193240801 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 590039257) ^ 375 = 32706324 := by
        calc
          (5 : ZMod 590039257) ^ 375 = (5 : ZMod 590039257) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 187 * (5 : ZMod 590039257) ^ 187) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 32706324 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 590039257) ^ 750 = 219164424 := by
        calc
          (5 : ZMod 590039257) ^ 750 = (5 : ZMod 590039257) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 375 * (5 : ZMod 590039257) ^ 375 := by rw [pow_add]
          _ = 219164424 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 590039257) ^ 1500 = 401378365 := by
        calc
          (5 : ZMod 590039257) ^ 1500 = (5 : ZMod 590039257) ^ (750 + 750) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 750 * (5 : ZMod 590039257) ^ 750 := by rw [pow_add]
          _ = 401378365 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 590039257) ^ 3001 = 443125427 := by
        calc
          (5 : ZMod 590039257) ^ 3001 = (5 : ZMod 590039257) ^ (1500 + 1500 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 1500 * (5 : ZMod 590039257) ^ 1500) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 443125427 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 590039257) ^ 6002 = 251735709 := by
        calc
          (5 : ZMod 590039257) ^ 6002 = (5 : ZMod 590039257) ^ (3001 + 3001) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 3001 * (5 : ZMod 590039257) ^ 3001 := by rw [pow_add]
          _ = 251735709 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 590039257) ^ 12004 = 170632210 := by
        calc
          (5 : ZMod 590039257) ^ 12004 = (5 : ZMod 590039257) ^ (6002 + 6002) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 6002 * (5 : ZMod 590039257) ^ 6002 := by rw [pow_add]
          _ = 170632210 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 590039257) ^ 24008 = 251887467 := by
        calc
          (5 : ZMod 590039257) ^ 24008 = (5 : ZMod 590039257) ^ (12004 + 12004) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 12004 * (5 : ZMod 590039257) ^ 12004 := by rw [pow_add]
          _ = 251887467 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 590039257) ^ 48017 = 257689470 := by
        calc
          (5 : ZMod 590039257) ^ 48017 = (5 : ZMod 590039257) ^ (24008 + 24008 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 24008 * (5 : ZMod 590039257) ^ 24008) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 257689470 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 590039257) ^ 96035 = 149424380 := by
        calc
          (5 : ZMod 590039257) ^ 96035 = (5 : ZMod 590039257) ^ (48017 + 48017 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 48017 * (5 : ZMod 590039257) ^ 48017) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 149424380 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 590039257) ^ 192070 = 496288764 := by
        calc
          (5 : ZMod 590039257) ^ 192070 = (5 : ZMod 590039257) ^ (96035 + 96035) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 96035 * (5 : ZMod 590039257) ^ 96035 := by rw [pow_add]
          _ = 496288764 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 590039257) ^ 384140 = 380142632 := by
        calc
          (5 : ZMod 590039257) ^ 384140 = (5 : ZMod 590039257) ^ (192070 + 192070) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 192070 * (5 : ZMod 590039257) ^ 192070 := by rw [pow_add]
          _ = 380142632 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 590039257) ^ 768280 = 405217314 := by
        calc
          (5 : ZMod 590039257) ^ 768280 = (5 : ZMod 590039257) ^ (384140 + 384140) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 384140 * (5 : ZMod 590039257) ^ 384140 := by rw [pow_add]
          _ = 405217314 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 590039257) ^ 1536560 = 238283908 := by
        calc
          (5 : ZMod 590039257) ^ 1536560 = (5 : ZMod 590039257) ^ (768280 + 768280) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 768280 * (5 : ZMod 590039257) ^ 768280 := by rw [pow_add]
          _ = 238283908 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 590039257) ^ 3073121 = 68674809 := by
        calc
          (5 : ZMod 590039257) ^ 3073121 = (5 : ZMod 590039257) ^ (1536560 + 1536560 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 1536560 * (5 : ZMod 590039257) ^ 1536560) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 68674809 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 590039257) ^ 6146242 = 176962692 := by
        calc
          (5 : ZMod 590039257) ^ 6146242 = (5 : ZMod 590039257) ^ (3073121 + 3073121) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 3073121 * (5 : ZMod 590039257) ^ 3073121 := by rw [pow_add]
          _ = 176962692 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 590039257) ^ 12292484 = 90492762 := by
        calc
          (5 : ZMod 590039257) ^ 12292484 = (5 : ZMod 590039257) ^ (6146242 + 6146242) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 6146242 * (5 : ZMod 590039257) ^ 6146242 := by rw [pow_add]
          _ = 90492762 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 590039257) ^ 24584969 = 93915217 := by
        calc
          (5 : ZMod 590039257) ^ 24584969 = (5 : ZMod 590039257) ^ (12292484 + 12292484 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 12292484 * (5 : ZMod 590039257) ^ 12292484) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 93915217 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 590039257) ^ 49169938 = 89803928 := by
        calc
          (5 : ZMod 590039257) ^ 49169938 = (5 : ZMod 590039257) ^ (24584969 + 24584969) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 24584969 * (5 : ZMod 590039257) ^ 24584969 := by rw [pow_add]
          _ = 89803928 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 590039257) ^ 98339876 = 413664634 := by
        calc
          (5 : ZMod 590039257) ^ 98339876 = (5 : ZMod 590039257) ^ (49169938 + 49169938) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 49169938 * (5 : ZMod 590039257) ^ 49169938 := by rw [pow_add]
          _ = 413664634 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 590039257) ^ 196679752 = 413664633 := by
        calc
          (5 : ZMod 590039257) ^ 196679752 = (5 : ZMod 590039257) ^ (98339876 + 98339876) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 98339876 * (5 : ZMod 590039257) ^ 98339876 := by rw [pow_add]
          _ = 413664633 := by rw [factor_1_26]; decide
      change (5 : ZMod 590039257) ^ 196679752 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (5 : ZMod 590039257) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 590039257) ^ 3 = 125 := by
        calc
          (5 : ZMod 590039257) ^ 3 = (5 : ZMod 590039257) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = ((5 : ZMod 590039257) ^ 1 * (5 : ZMod 590039257) ^ 1) * (5 : ZMod 590039257) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 590039257) ^ 6 = 15625 := by
        calc
          (5 : ZMod 590039257) ^ 6 = (5 : ZMod 590039257) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 3 * (5 : ZMod 590039257) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 590039257) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 590039257) ^ 12 = (5 : ZMod 590039257) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 6 * (5 : ZMod 590039257) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 590039257) ^ 24 = 107838925 := by
        calc
          (5 : ZMod 590039257) ^ 24 = (5 : ZMod 590039257) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 590039257) ^ n) (by norm_num)
          _ = (5 : ZMod 590039257) ^ 12 * (5 : ZMod 590039257) ^ 12 := by rw [pow_add]
          _ = 107838925 := by rw [factor_2_3]; decide
      change (5 : ZMod 590039257) ^ 24 ≠ 1
      rw [factor_2_4]
      decide

#print axioms prime_lucas_590039257

end TotientTailPeriodKiller
end Erdos249257
