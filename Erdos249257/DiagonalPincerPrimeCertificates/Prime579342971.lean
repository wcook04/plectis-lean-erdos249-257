import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_579342971 : Nat.Prime 579342971 := by
  apply lucas_primality 579342971 (2 : ZMod 579342971)
  ·
      have fermat_0 : (2 : ZMod 579342971) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 579342971) ^ 2 = 4 := by
        calc
          (2 : ZMod 579342971) ^ 2 = (2 : ZMod 579342971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 1 * (2 : ZMod 579342971) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 579342971) ^ 4 = 16 := by
        calc
          (2 : ZMod 579342971) ^ 4 = (2 : ZMod 579342971) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 2 * (2 : ZMod 579342971) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 579342971) ^ 8 = 256 := by
        calc
          (2 : ZMod 579342971) ^ 8 = (2 : ZMod 579342971) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 4 * (2 : ZMod 579342971) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 579342971) ^ 17 = 131072 := by
        calc
          (2 : ZMod 579342971) ^ 17 = (2 : ZMod 579342971) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 8 * (2 : ZMod 579342971) ^ 8) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 579342971) ^ 34 = 378923025 := by
        calc
          (2 : ZMod 579342971) ^ 34 = (2 : ZMod 579342971) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 17 * (2 : ZMod 579342971) ^ 17 := by rw [pow_add]
          _ = 378923025 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 579342971) ^ 69 = 421690730 := by
        calc
          (2 : ZMod 579342971) ^ 69 = (2 : ZMod 579342971) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 34 * (2 : ZMod 579342971) ^ 34) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 421690730 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 579342971) ^ 138 = 247511874 := by
        calc
          (2 : ZMod 579342971) ^ 138 = (2 : ZMod 579342971) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 69 * (2 : ZMod 579342971) ^ 69 := by rw [pow_add]
          _ = 247511874 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 579342971) ^ 276 = 61494110 := by
        calc
          (2 : ZMod 579342971) ^ 276 = (2 : ZMod 579342971) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 138 * (2 : ZMod 579342971) ^ 138 := by rw [pow_add]
          _ = 61494110 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 579342971) ^ 552 = 467087785 := by
        calc
          (2 : ZMod 579342971) ^ 552 = (2 : ZMod 579342971) ^ (276 + 276) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 276 * (2 : ZMod 579342971) ^ 276 := by rw [pow_add]
          _ = 467087785 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 579342971) ^ 1105 = 202085957 := by
        calc
          (2 : ZMod 579342971) ^ 1105 = (2 : ZMod 579342971) ^ (552 + 552 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 552 * (2 : ZMod 579342971) ^ 552) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 202085957 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 579342971) ^ 2210 = 412049276 := by
        calc
          (2 : ZMod 579342971) ^ 2210 = (2 : ZMod 579342971) ^ (1105 + 1105) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 1105 * (2 : ZMod 579342971) ^ 1105 := by rw [pow_add]
          _ = 412049276 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 579342971) ^ 4420 = 321030032 := by
        calc
          (2 : ZMod 579342971) ^ 4420 = (2 : ZMod 579342971) ^ (2210 + 2210) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 2210 * (2 : ZMod 579342971) ^ 2210 := by rw [pow_add]
          _ = 321030032 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 579342971) ^ 8840 = 363428077 := by
        calc
          (2 : ZMod 579342971) ^ 8840 = (2 : ZMod 579342971) ^ (4420 + 4420) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 4420 * (2 : ZMod 579342971) ^ 4420 := by rw [pow_add]
          _ = 363428077 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 579342971) ^ 17680 = 381442818 := by
        calc
          (2 : ZMod 579342971) ^ 17680 = (2 : ZMod 579342971) ^ (8840 + 8840) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 8840 * (2 : ZMod 579342971) ^ 8840 := by rw [pow_add]
          _ = 381442818 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 579342971) ^ 35360 = 481763721 := by
        calc
          (2 : ZMod 579342971) ^ 35360 = (2 : ZMod 579342971) ^ (17680 + 17680) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 17680 * (2 : ZMod 579342971) ^ 17680 := by rw [pow_add]
          _ = 481763721 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 579342971) ^ 70720 = 318050911 := by
        calc
          (2 : ZMod 579342971) ^ 70720 = (2 : ZMod 579342971) ^ (35360 + 35360) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 35360 * (2 : ZMod 579342971) ^ 35360 := by rw [pow_add]
          _ = 318050911 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 579342971) ^ 141441 = 112213113 := by
        calc
          (2 : ZMod 579342971) ^ 141441 = (2 : ZMod 579342971) ^ (70720 + 70720 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 70720 * (2 : ZMod 579342971) ^ 70720) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 112213113 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 579342971) ^ 282882 = 205740908 := by
        calc
          (2 : ZMod 579342971) ^ 282882 = (2 : ZMod 579342971) ^ (141441 + 141441) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 141441 * (2 : ZMod 579342971) ^ 141441 := by rw [pow_add]
          _ = 205740908 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 579342971) ^ 565764 = 145422788 := by
        calc
          (2 : ZMod 579342971) ^ 565764 = (2 : ZMod 579342971) ^ (282882 + 282882) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 282882 * (2 : ZMod 579342971) ^ 282882 := by rw [pow_add]
          _ = 145422788 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 579342971) ^ 1131529 = 188204962 := by
        calc
          (2 : ZMod 579342971) ^ 1131529 = (2 : ZMod 579342971) ^ (565764 + 565764 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 565764 * (2 : ZMod 579342971) ^ 565764) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 188204962 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 579342971) ^ 2263058 = 263180359 := by
        calc
          (2 : ZMod 579342971) ^ 2263058 = (2 : ZMod 579342971) ^ (1131529 + 1131529) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 1131529 * (2 : ZMod 579342971) ^ 1131529 := by rw [pow_add]
          _ = 263180359 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 579342971) ^ 4526116 = 351612518 := by
        calc
          (2 : ZMod 579342971) ^ 4526116 = (2 : ZMod 579342971) ^ (2263058 + 2263058) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 2263058 * (2 : ZMod 579342971) ^ 2263058 := by rw [pow_add]
          _ = 351612518 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 579342971) ^ 9052233 = 136682873 := by
        calc
          (2 : ZMod 579342971) ^ 9052233 = (2 : ZMod 579342971) ^ (4526116 + 4526116 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 4526116 * (2 : ZMod 579342971) ^ 4526116) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 136682873 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 579342971) ^ 18104467 = 576912743 := by
        calc
          (2 : ZMod 579342971) ^ 18104467 = (2 : ZMod 579342971) ^ (9052233 + 9052233 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 9052233 * (2 : ZMod 579342971) ^ 9052233) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 576912743 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 579342971) ^ 36208935 = 371771220 := by
        calc
          (2 : ZMod 579342971) ^ 36208935 = (2 : ZMod 579342971) ^ (18104467 + 18104467 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 18104467 * (2 : ZMod 579342971) ^ 18104467) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 371771220 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 579342971) ^ 72417871 = 348727524 := by
        calc
          (2 : ZMod 579342971) ^ 72417871 = (2 : ZMod 579342971) ^ (36208935 + 36208935 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 36208935 * (2 : ZMod 579342971) ^ 36208935) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 348727524 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 579342971) ^ 144835742 = 109877775 := by
        calc
          (2 : ZMod 579342971) ^ 144835742 = (2 : ZMod 579342971) ^ (72417871 + 72417871) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 72417871 * (2 : ZMod 579342971) ^ 72417871 := by rw [pow_add]
          _ = 109877775 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 579342971) ^ 289671485 = 579342970 := by
        calc
          (2 : ZMod 579342971) ^ 289671485 = (2 : ZMod 579342971) ^ (144835742 + 144835742 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 144835742 * (2 : ZMod 579342971) ^ 144835742) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 579342970 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 579342971) ^ 579342970 = 1 := by
        calc
          (2 : ZMod 579342971) ^ 579342970 = (2 : ZMod 579342971) ^ (289671485 + 289671485) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 289671485 * (2 : ZMod 579342971) ^ 289671485 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (67, 1), (864691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (67, 1), (864691, 1)] : List FactorBlock).map factorBlockValue).prod = 579342971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 579342971) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 579342971) ^ 2 = 4 := by
        calc
          (2 : ZMod 579342971) ^ 2 = (2 : ZMod 579342971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 1 * (2 : ZMod 579342971) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 579342971) ^ 4 = 16 := by
        calc
          (2 : ZMod 579342971) ^ 4 = (2 : ZMod 579342971) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 2 * (2 : ZMod 579342971) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 579342971) ^ 8 = 256 := by
        calc
          (2 : ZMod 579342971) ^ 8 = (2 : ZMod 579342971) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 4 * (2 : ZMod 579342971) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 579342971) ^ 17 = 131072 := by
        calc
          (2 : ZMod 579342971) ^ 17 = (2 : ZMod 579342971) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 8 * (2 : ZMod 579342971) ^ 8) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 579342971) ^ 34 = 378923025 := by
        calc
          (2 : ZMod 579342971) ^ 34 = (2 : ZMod 579342971) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 17 * (2 : ZMod 579342971) ^ 17 := by rw [pow_add]
          _ = 378923025 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 579342971) ^ 69 = 421690730 := by
        calc
          (2 : ZMod 579342971) ^ 69 = (2 : ZMod 579342971) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 34 * (2 : ZMod 579342971) ^ 34) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 421690730 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 579342971) ^ 138 = 247511874 := by
        calc
          (2 : ZMod 579342971) ^ 138 = (2 : ZMod 579342971) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 69 * (2 : ZMod 579342971) ^ 69 := by rw [pow_add]
          _ = 247511874 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 579342971) ^ 276 = 61494110 := by
        calc
          (2 : ZMod 579342971) ^ 276 = (2 : ZMod 579342971) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 138 * (2 : ZMod 579342971) ^ 138 := by rw [pow_add]
          _ = 61494110 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 579342971) ^ 552 = 467087785 := by
        calc
          (2 : ZMod 579342971) ^ 552 = (2 : ZMod 579342971) ^ (276 + 276) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 276 * (2 : ZMod 579342971) ^ 276 := by rw [pow_add]
          _ = 467087785 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 579342971) ^ 1105 = 202085957 := by
        calc
          (2 : ZMod 579342971) ^ 1105 = (2 : ZMod 579342971) ^ (552 + 552 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 552 * (2 : ZMod 579342971) ^ 552) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 202085957 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 579342971) ^ 2210 = 412049276 := by
        calc
          (2 : ZMod 579342971) ^ 2210 = (2 : ZMod 579342971) ^ (1105 + 1105) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 1105 * (2 : ZMod 579342971) ^ 1105 := by rw [pow_add]
          _ = 412049276 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 579342971) ^ 4420 = 321030032 := by
        calc
          (2 : ZMod 579342971) ^ 4420 = (2 : ZMod 579342971) ^ (2210 + 2210) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 2210 * (2 : ZMod 579342971) ^ 2210 := by rw [pow_add]
          _ = 321030032 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 579342971) ^ 8840 = 363428077 := by
        calc
          (2 : ZMod 579342971) ^ 8840 = (2 : ZMod 579342971) ^ (4420 + 4420) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 4420 * (2 : ZMod 579342971) ^ 4420 := by rw [pow_add]
          _ = 363428077 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 579342971) ^ 17680 = 381442818 := by
        calc
          (2 : ZMod 579342971) ^ 17680 = (2 : ZMod 579342971) ^ (8840 + 8840) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 8840 * (2 : ZMod 579342971) ^ 8840 := by rw [pow_add]
          _ = 381442818 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 579342971) ^ 35360 = 481763721 := by
        calc
          (2 : ZMod 579342971) ^ 35360 = (2 : ZMod 579342971) ^ (17680 + 17680) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 17680 * (2 : ZMod 579342971) ^ 17680 := by rw [pow_add]
          _ = 481763721 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 579342971) ^ 70720 = 318050911 := by
        calc
          (2 : ZMod 579342971) ^ 70720 = (2 : ZMod 579342971) ^ (35360 + 35360) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 35360 * (2 : ZMod 579342971) ^ 35360 := by rw [pow_add]
          _ = 318050911 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 579342971) ^ 141441 = 112213113 := by
        calc
          (2 : ZMod 579342971) ^ 141441 = (2 : ZMod 579342971) ^ (70720 + 70720 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 70720 * (2 : ZMod 579342971) ^ 70720) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 112213113 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 579342971) ^ 282882 = 205740908 := by
        calc
          (2 : ZMod 579342971) ^ 282882 = (2 : ZMod 579342971) ^ (141441 + 141441) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 141441 * (2 : ZMod 579342971) ^ 141441 := by rw [pow_add]
          _ = 205740908 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 579342971) ^ 565764 = 145422788 := by
        calc
          (2 : ZMod 579342971) ^ 565764 = (2 : ZMod 579342971) ^ (282882 + 282882) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 282882 * (2 : ZMod 579342971) ^ 282882 := by rw [pow_add]
          _ = 145422788 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 579342971) ^ 1131529 = 188204962 := by
        calc
          (2 : ZMod 579342971) ^ 1131529 = (2 : ZMod 579342971) ^ (565764 + 565764 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 565764 * (2 : ZMod 579342971) ^ 565764) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 188204962 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 579342971) ^ 2263058 = 263180359 := by
        calc
          (2 : ZMod 579342971) ^ 2263058 = (2 : ZMod 579342971) ^ (1131529 + 1131529) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 1131529 * (2 : ZMod 579342971) ^ 1131529 := by rw [pow_add]
          _ = 263180359 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 579342971) ^ 4526116 = 351612518 := by
        calc
          (2 : ZMod 579342971) ^ 4526116 = (2 : ZMod 579342971) ^ (2263058 + 2263058) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 2263058 * (2 : ZMod 579342971) ^ 2263058 := by rw [pow_add]
          _ = 351612518 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 579342971) ^ 9052233 = 136682873 := by
        calc
          (2 : ZMod 579342971) ^ 9052233 = (2 : ZMod 579342971) ^ (4526116 + 4526116 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 4526116 * (2 : ZMod 579342971) ^ 4526116) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 136682873 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 579342971) ^ 18104467 = 576912743 := by
        calc
          (2 : ZMod 579342971) ^ 18104467 = (2 : ZMod 579342971) ^ (9052233 + 9052233 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 9052233 * (2 : ZMod 579342971) ^ 9052233) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 576912743 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 579342971) ^ 36208935 = 371771220 := by
        calc
          (2 : ZMod 579342971) ^ 36208935 = (2 : ZMod 579342971) ^ (18104467 + 18104467 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 18104467 * (2 : ZMod 579342971) ^ 18104467) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 371771220 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 579342971) ^ 72417871 = 348727524 := by
        calc
          (2 : ZMod 579342971) ^ 72417871 = (2 : ZMod 579342971) ^ (36208935 + 36208935 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 36208935 * (2 : ZMod 579342971) ^ 36208935) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 348727524 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 579342971) ^ 144835742 = 109877775 := by
        calc
          (2 : ZMod 579342971) ^ 144835742 = (2 : ZMod 579342971) ^ (72417871 + 72417871) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 72417871 * (2 : ZMod 579342971) ^ 72417871 := by rw [pow_add]
          _ = 109877775 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 579342971) ^ 289671485 = 579342970 := by
        calc
          (2 : ZMod 579342971) ^ 289671485 = (2 : ZMod 579342971) ^ (144835742 + 144835742 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 144835742 * (2 : ZMod 579342971) ^ 144835742) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 579342970 := by rw [factor_0_27]; decide
      change (2 : ZMod 579342971) ^ 289671485 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 579342971) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 579342971) ^ 3 = 8 := by
        calc
          (2 : ZMod 579342971) ^ 3 = (2 : ZMod 579342971) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 1 * (2 : ZMod 579342971) ^ 1) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 579342971) ^ 6 = 64 := by
        calc
          (2 : ZMod 579342971) ^ 6 = (2 : ZMod 579342971) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 3 * (2 : ZMod 579342971) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 579342971) ^ 13 = 8192 := by
        calc
          (2 : ZMod 579342971) ^ 13 = (2 : ZMod 579342971) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 6 * (2 : ZMod 579342971) ^ 6) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 579342971) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 579342971) ^ 27 = (2 : ZMod 579342971) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 13 * (2 : ZMod 579342971) ^ 13) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 579342971) ^ 55 = 496837795 := by
        calc
          (2 : ZMod 579342971) ^ 55 = (2 : ZMod 579342971) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 27 * (2 : ZMod 579342971) ^ 27) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 496837795 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 579342971) ^ 110 = 277804160 := by
        calc
          (2 : ZMod 579342971) ^ 110 = (2 : ZMod 579342971) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 55 * (2 : ZMod 579342971) ^ 55 := by rw [pow_add]
          _ = 277804160 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 579342971) ^ 221 = 415047693 := by
        calc
          (2 : ZMod 579342971) ^ 221 = (2 : ZMod 579342971) ^ (110 + 110 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 110 * (2 : ZMod 579342971) ^ 110) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 415047693 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 579342971) ^ 442 = 64427825 := by
        calc
          (2 : ZMod 579342971) ^ 442 = (2 : ZMod 579342971) ^ (221 + 221) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 221 * (2 : ZMod 579342971) ^ 221 := by rw [pow_add]
          _ = 64427825 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 579342971) ^ 884 = 332482218 := by
        calc
          (2 : ZMod 579342971) ^ 884 = (2 : ZMod 579342971) ^ (442 + 442) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 442 * (2 : ZMod 579342971) ^ 442 := by rw [pow_add]
          _ = 332482218 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 579342971) ^ 1768 = 521148147 := by
        calc
          (2 : ZMod 579342971) ^ 1768 = (2 : ZMod 579342971) ^ (884 + 884) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 884 * (2 : ZMod 579342971) ^ 884 := by rw [pow_add]
          _ = 521148147 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 579342971) ^ 3536 = 143278884 := by
        calc
          (2 : ZMod 579342971) ^ 3536 = (2 : ZMod 579342971) ^ (1768 + 1768) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 1768 * (2 : ZMod 579342971) ^ 1768 := by rw [pow_add]
          _ = 143278884 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 579342971) ^ 7072 = 19221466 := by
        calc
          (2 : ZMod 579342971) ^ 7072 = (2 : ZMod 579342971) ^ (3536 + 3536) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 3536 * (2 : ZMod 579342971) ^ 3536 := by rw [pow_add]
          _ = 19221466 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 579342971) ^ 14144 = 362293326 := by
        calc
          (2 : ZMod 579342971) ^ 14144 = (2 : ZMod 579342971) ^ (7072 + 7072) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 7072 * (2 : ZMod 579342971) ^ 7072 := by rw [pow_add]
          _ = 362293326 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 579342971) ^ 28288 = 153224825 := by
        calc
          (2 : ZMod 579342971) ^ 28288 = (2 : ZMod 579342971) ^ (14144 + 14144) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 14144 * (2 : ZMod 579342971) ^ 14144 := by rw [pow_add]
          _ = 153224825 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 579342971) ^ 56576 = 325625262 := by
        calc
          (2 : ZMod 579342971) ^ 56576 = (2 : ZMod 579342971) ^ (28288 + 28288) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 28288 * (2 : ZMod 579342971) ^ 28288 := by rw [pow_add]
          _ = 325625262 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 579342971) ^ 113152 = 122486699 := by
        calc
          (2 : ZMod 579342971) ^ 113152 = (2 : ZMod 579342971) ^ (56576 + 56576) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 56576 * (2 : ZMod 579342971) ^ 56576 := by rw [pow_add]
          _ = 122486699 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 579342971) ^ 226305 = 528301798 := by
        calc
          (2 : ZMod 579342971) ^ 226305 = (2 : ZMod 579342971) ^ (113152 + 113152 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 113152 * (2 : ZMod 579342971) ^ 113152) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 528301798 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 579342971) ^ 452611 = 564727418 := by
        calc
          (2 : ZMod 579342971) ^ 452611 = (2 : ZMod 579342971) ^ (226305 + 226305 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 226305 * (2 : ZMod 579342971) ^ 226305) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 564727418 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 579342971) ^ 905223 = 415829262 := by
        calc
          (2 : ZMod 579342971) ^ 905223 = (2 : ZMod 579342971) ^ (452611 + 452611 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 452611 * (2 : ZMod 579342971) ^ 452611) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 415829262 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 579342971) ^ 1810446 = 461047407 := by
        calc
          (2 : ZMod 579342971) ^ 1810446 = (2 : ZMod 579342971) ^ (905223 + 905223) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 905223 * (2 : ZMod 579342971) ^ 905223 := by rw [pow_add]
          _ = 461047407 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 579342971) ^ 3620893 = 306106255 := by
        calc
          (2 : ZMod 579342971) ^ 3620893 = (2 : ZMod 579342971) ^ (1810446 + 1810446 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 1810446 * (2 : ZMod 579342971) ^ 1810446) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 306106255 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 579342971) ^ 7241787 = 447485535 := by
        calc
          (2 : ZMod 579342971) ^ 7241787 = (2 : ZMod 579342971) ^ (3620893 + 3620893 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 3620893 * (2 : ZMod 579342971) ^ 3620893) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 447485535 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 579342971) ^ 14483574 = 189782147 := by
        calc
          (2 : ZMod 579342971) ^ 14483574 = (2 : ZMod 579342971) ^ (7241787 + 7241787) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 7241787 * (2 : ZMod 579342971) ^ 7241787 := by rw [pow_add]
          _ = 189782147 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 579342971) ^ 28967148 = 357670104 := by
        calc
          (2 : ZMod 579342971) ^ 28967148 = (2 : ZMod 579342971) ^ (14483574 + 14483574) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 14483574 * (2 : ZMod 579342971) ^ 14483574 := by rw [pow_add]
          _ = 357670104 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 579342971) ^ 57934297 = 234528168 := by
        calc
          (2 : ZMod 579342971) ^ 57934297 = (2 : ZMod 579342971) ^ (28967148 + 28967148 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 28967148 * (2 : ZMod 579342971) ^ 28967148) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 234528168 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 579342971) ^ 115868594 = 324056240 := by
        calc
          (2 : ZMod 579342971) ^ 115868594 = (2 : ZMod 579342971) ^ (57934297 + 57934297) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 57934297 * (2 : ZMod 579342971) ^ 57934297 := by rw [pow_add]
          _ = 324056240 := by rw [factor_1_25]; decide
      change (2 : ZMod 579342971) ^ 115868594 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (2 : ZMod 579342971) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 579342971) ^ 2 = 4 := by
        calc
          (2 : ZMod 579342971) ^ 2 = (2 : ZMod 579342971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 1 * (2 : ZMod 579342971) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 579342971) ^ 4 = 16 := by
        calc
          (2 : ZMod 579342971) ^ 4 = (2 : ZMod 579342971) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 2 * (2 : ZMod 579342971) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 579342971) ^ 8 = 256 := by
        calc
          (2 : ZMod 579342971) ^ 8 = (2 : ZMod 579342971) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 4 * (2 : ZMod 579342971) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 579342971) ^ 16 = 65536 := by
        calc
          (2 : ZMod 579342971) ^ 16 = (2 : ZMod 579342971) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 8 * (2 : ZMod 579342971) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 579342971) ^ 32 = 239566499 := by
        calc
          (2 : ZMod 579342971) ^ 32 = (2 : ZMod 579342971) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 16 * (2 : ZMod 579342971) ^ 16 := by rw [pow_add]
          _ = 239566499 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 579342971) ^ 65 = 98773542 := by
        calc
          (2 : ZMod 579342971) ^ 65 = (2 : ZMod 579342971) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 32 * (2 : ZMod 579342971) ^ 32) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 98773542 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 579342971) ^ 131 = 409284213 := by
        calc
          (2 : ZMod 579342971) ^ 131 = (2 : ZMod 579342971) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 65 * (2 : ZMod 579342971) ^ 65) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 409284213 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 579342971) ^ 263 = 240316029 := by
        calc
          (2 : ZMod 579342971) ^ 263 = (2 : ZMod 579342971) ^ (131 + 131 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 131 * (2 : ZMod 579342971) ^ 131) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 240316029 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 579342971) ^ 527 = 316734638 := by
        calc
          (2 : ZMod 579342971) ^ 527 = (2 : ZMod 579342971) ^ (263 + 263 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 263 * (2 : ZMod 579342971) ^ 263) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 316734638 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 579342971) ^ 1055 = 8639497 := by
        calc
          (2 : ZMod 579342971) ^ 1055 = (2 : ZMod 579342971) ^ (527 + 527 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 527 * (2 : ZMod 579342971) ^ 527) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 8639497 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 579342971) ^ 2111 = 196116564 := by
        calc
          (2 : ZMod 579342971) ^ 2111 = (2 : ZMod 579342971) ^ (1055 + 1055 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 1055 * (2 : ZMod 579342971) ^ 1055) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 196116564 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 579342971) ^ 4222 = 479676364 := by
        calc
          (2 : ZMod 579342971) ^ 4222 = (2 : ZMod 579342971) ^ (2111 + 2111) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 2111 * (2 : ZMod 579342971) ^ 2111 := by rw [pow_add]
          _ = 479676364 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 579342971) ^ 8444 = 10494348 := by
        calc
          (2 : ZMod 579342971) ^ 8444 = (2 : ZMod 579342971) ^ (4222 + 4222) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 4222 * (2 : ZMod 579342971) ^ 4222 := by rw [pow_add]
          _ = 10494348 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 579342971) ^ 16888 = 558529888 := by
        calc
          (2 : ZMod 579342971) ^ 16888 = (2 : ZMod 579342971) ^ (8444 + 8444) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 8444 * (2 : ZMod 579342971) ^ 8444 := by rw [pow_add]
          _ = 558529888 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 579342971) ^ 33776 = 415060653 := by
        calc
          (2 : ZMod 579342971) ^ 33776 = (2 : ZMod 579342971) ^ (16888 + 16888) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 16888 * (2 : ZMod 579342971) ^ 16888 := by rw [pow_add]
          _ = 415060653 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 579342971) ^ 67553 = 318584001 := by
        calc
          (2 : ZMod 579342971) ^ 67553 = (2 : ZMod 579342971) ^ (33776 + 33776 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 33776 * (2 : ZMod 579342971) ^ 33776) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 318584001 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 579342971) ^ 135107 = 28378137 := by
        calc
          (2 : ZMod 579342971) ^ 135107 = (2 : ZMod 579342971) ^ (67553 + 67553 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 67553 * (2 : ZMod 579342971) ^ 67553) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 28378137 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 579342971) ^ 270215 = 132074728 := by
        calc
          (2 : ZMod 579342971) ^ 270215 = (2 : ZMod 579342971) ^ (135107 + 135107 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 135107 * (2 : ZMod 579342971) ^ 135107) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 132074728 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 579342971) ^ 540431 = 436353606 := by
        calc
          (2 : ZMod 579342971) ^ 540431 = (2 : ZMod 579342971) ^ (270215 + 270215 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 270215 * (2 : ZMod 579342971) ^ 270215) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 436353606 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 579342971) ^ 1080863 = 296255048 := by
        calc
          (2 : ZMod 579342971) ^ 1080863 = (2 : ZMod 579342971) ^ (540431 + 540431 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 540431 * (2 : ZMod 579342971) ^ 540431) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 296255048 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 579342971) ^ 2161727 = 370646539 := by
        calc
          (2 : ZMod 579342971) ^ 2161727 = (2 : ZMod 579342971) ^ (1080863 + 1080863 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 1080863 * (2 : ZMod 579342971) ^ 1080863) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 370646539 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 579342971) ^ 4323455 = 16245773 := by
        calc
          (2 : ZMod 579342971) ^ 4323455 = (2 : ZMod 579342971) ^ (2161727 + 2161727 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 2161727 * (2 : ZMod 579342971) ^ 2161727) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 16245773 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 579342971) ^ 8646910 = 235841740 := by
        calc
          (2 : ZMod 579342971) ^ 8646910 = (2 : ZMod 579342971) ^ (4323455 + 4323455) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 4323455 * (2 : ZMod 579342971) ^ 4323455 := by rw [pow_add]
          _ = 235841740 := by rw [factor_2_22]; decide
      change (2 : ZMod 579342971) ^ 8646910 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (2 : ZMod 579342971) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 579342971) ^ 2 = 4 := by
        calc
          (2 : ZMod 579342971) ^ 2 = (2 : ZMod 579342971) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 1 * (2 : ZMod 579342971) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 579342971) ^ 5 = 32 := by
        calc
          (2 : ZMod 579342971) ^ 5 = (2 : ZMod 579342971) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 2 * (2 : ZMod 579342971) ^ 2) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 579342971) ^ 10 = 1024 := by
        calc
          (2 : ZMod 579342971) ^ 10 = (2 : ZMod 579342971) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 5 * (2 : ZMod 579342971) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 579342971) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 579342971) ^ 20 = (2 : ZMod 579342971) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 10 * (2 : ZMod 579342971) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 579342971) ^ 41 = 416680607 := by
        calc
          (2 : ZMod 579342971) ^ 41 = (2 : ZMod 579342971) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 20 * (2 : ZMod 579342971) ^ 20) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 416680607 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 579342971) ^ 83 = 315991145 := by
        calc
          (2 : ZMod 579342971) ^ 83 = (2 : ZMod 579342971) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 41 * (2 : ZMod 579342971) ^ 41) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 315991145 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 579342971) ^ 167 = 350412372 := by
        calc
          (2 : ZMod 579342971) ^ 167 = (2 : ZMod 579342971) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 83 * (2 : ZMod 579342971) ^ 83) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 350412372 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 579342971) ^ 335 = 208663202 := by
        calc
          (2 : ZMod 579342971) ^ 335 = (2 : ZMod 579342971) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = ((2 : ZMod 579342971) ^ 167 * (2 : ZMod 579342971) ^ 167) * (2 : ZMod 579342971) := by rw [pow_succ, pow_add]
          _ = 208663202 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 579342971) ^ 670 = 328539321 := by
        calc
          (2 : ZMod 579342971) ^ 670 = (2 : ZMod 579342971) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (2 : ZMod 579342971) ^ n) (by norm_num)
          _ = (2 : ZMod 579342971) ^ 335 * (2 : ZMod 579342971) ^ 335 := by rw [pow_add]
          _ = 328539321 := by rw [factor_3_8]; decide
      change (2 : ZMod 579342971) ^ 670 ≠ 1
      rw [factor_3_9]
      decide

#print axioms prime_lucas_579342971

end TotientTailPeriodKiller
end Erdos249257
