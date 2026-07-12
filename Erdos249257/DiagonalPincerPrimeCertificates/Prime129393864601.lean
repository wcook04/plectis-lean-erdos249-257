import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_129393864601 : Nat.Prime 129393864601 := by
  apply lucas_primality 129393864601 (59 : ZMod 129393864601)
  ·
      have fermat_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have fermat_1 : (59 : ZMod 129393864601) ^ 3 = 205379 := by
        calc
          (59 : ZMod 129393864601) ^ 3 = (59 : ZMod 129393864601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 205379 := by rw [fermat_0]; decide
      have fermat_2 : (59 : ZMod 129393864601) ^ 7 = 30168057400 := by
        calc
          (59 : ZMod 129393864601) ^ 7 = (59 : ZMod 129393864601) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 3 * (59 : ZMod 129393864601) ^ 3) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 30168057400 := by rw [fermat_1]; decide
      have fermat_3 : (59 : ZMod 129393864601) ^ 15 = 120007604034 := by
        calc
          (59 : ZMod 129393864601) ^ 15 = (59 : ZMod 129393864601) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 7 * (59 : ZMod 129393864601) ^ 7) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 120007604034 := by rw [fermat_2]; decide
      have fermat_4 : (59 : ZMod 129393864601) ^ 30 = 105232025999 := by
        calc
          (59 : ZMod 129393864601) ^ 30 = (59 : ZMod 129393864601) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 15 * (59 : ZMod 129393864601) ^ 15 := by rw [pow_add]
          _ = 105232025999 := by rw [fermat_3]; decide
      have fermat_5 : (59 : ZMod 129393864601) ^ 60 = 106201252252 := by
        calc
          (59 : ZMod 129393864601) ^ 60 = (59 : ZMod 129393864601) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 30 * (59 : ZMod 129393864601) ^ 30 := by rw [pow_add]
          _ = 106201252252 := by rw [fermat_4]; decide
      have fermat_6 : (59 : ZMod 129393864601) ^ 120 = 36236272916 := by
        calc
          (59 : ZMod 129393864601) ^ 120 = (59 : ZMod 129393864601) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 60 * (59 : ZMod 129393864601) ^ 60 := by rw [pow_add]
          _ = 36236272916 := by rw [fermat_5]; decide
      have fermat_7 : (59 : ZMod 129393864601) ^ 241 = 13313076293 := by
        calc
          (59 : ZMod 129393864601) ^ 241 = (59 : ZMod 129393864601) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 120 * (59 : ZMod 129393864601) ^ 120) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 13313076293 := by rw [fermat_6]; decide
      have fermat_8 : (59 : ZMod 129393864601) ^ 482 = 109182112620 := by
        calc
          (59 : ZMod 129393864601) ^ 482 = (59 : ZMod 129393864601) ^ (241 + 241) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 241 * (59 : ZMod 129393864601) ^ 241 := by rw [pow_add]
          _ = 109182112620 := by rw [fermat_7]; decide
      have fermat_9 : (59 : ZMod 129393864601) ^ 964 = 59513962683 := by
        calc
          (59 : ZMod 129393864601) ^ 964 = (59 : ZMod 129393864601) ^ (482 + 482) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 482 * (59 : ZMod 129393864601) ^ 482 := by rw [pow_add]
          _ = 59513962683 := by rw [fermat_8]; decide
      have fermat_10 : (59 : ZMod 129393864601) ^ 1928 = 12994517568 := by
        calc
          (59 : ZMod 129393864601) ^ 1928 = (59 : ZMod 129393864601) ^ (964 + 964) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 964 * (59 : ZMod 129393864601) ^ 964 := by rw [pow_add]
          _ = 12994517568 := by rw [fermat_9]; decide
      have fermat_11 : (59 : ZMod 129393864601) ^ 3856 = 53521184067 := by
        calc
          (59 : ZMod 129393864601) ^ 3856 = (59 : ZMod 129393864601) ^ (1928 + 1928) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1928 * (59 : ZMod 129393864601) ^ 1928 := by rw [pow_add]
          _ = 53521184067 := by rw [fermat_10]; decide
      have fermat_12 : (59 : ZMod 129393864601) ^ 7712 = 58553654785 := by
        calc
          (59 : ZMod 129393864601) ^ 7712 = (59 : ZMod 129393864601) ^ (3856 + 3856) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3856 * (59 : ZMod 129393864601) ^ 3856 := by rw [pow_add]
          _ = 58553654785 := by rw [fermat_11]; decide
      have fermat_13 : (59 : ZMod 129393864601) ^ 15424 = 14392934267 := by
        calc
          (59 : ZMod 129393864601) ^ 15424 = (59 : ZMod 129393864601) ^ (7712 + 7712) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 7712 * (59 : ZMod 129393864601) ^ 7712 := by rw [pow_add]
          _ = 14392934267 := by rw [fermat_12]; decide
      have fermat_14 : (59 : ZMod 129393864601) ^ 30849 = 26709057675 := by
        calc
          (59 : ZMod 129393864601) ^ 30849 = (59 : ZMod 129393864601) ^ (15424 + 15424 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 15424 * (59 : ZMod 129393864601) ^ 15424) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 26709057675 := by rw [fermat_13]; decide
      have fermat_15 : (59 : ZMod 129393864601) ^ 61699 = 107131182011 := by
        calc
          (59 : ZMod 129393864601) ^ 61699 = (59 : ZMod 129393864601) ^ (30849 + 30849 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 30849 * (59 : ZMod 129393864601) ^ 30849) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 107131182011 := by rw [fermat_14]; decide
      have fermat_16 : (59 : ZMod 129393864601) ^ 123399 = 61307937637 := by
        calc
          (59 : ZMod 129393864601) ^ 123399 = (59 : ZMod 129393864601) ^ (61699 + 61699 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 61699 * (59 : ZMod 129393864601) ^ 61699) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 61307937637 := by rw [fermat_15]; decide
      have fermat_17 : (59 : ZMod 129393864601) ^ 246799 = 1153396915 := by
        calc
          (59 : ZMod 129393864601) ^ 246799 = (59 : ZMod 129393864601) ^ (123399 + 123399 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 123399 * (59 : ZMod 129393864601) ^ 123399) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 1153396915 := by rw [fermat_16]; decide
      have fermat_18 : (59 : ZMod 129393864601) ^ 493598 = 113401851424 := by
        calc
          (59 : ZMod 129393864601) ^ 493598 = (59 : ZMod 129393864601) ^ (246799 + 246799) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 246799 * (59 : ZMod 129393864601) ^ 246799 := by rw [pow_add]
          _ = 113401851424 := by rw [fermat_17]; decide
      have fermat_19 : (59 : ZMod 129393864601) ^ 987196 = 54693681357 := by
        calc
          (59 : ZMod 129393864601) ^ 987196 = (59 : ZMod 129393864601) ^ (493598 + 493598) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 493598 * (59 : ZMod 129393864601) ^ 493598 := by rw [pow_add]
          _ = 54693681357 := by rw [fermat_18]; decide
      have fermat_20 : (59 : ZMod 129393864601) ^ 1974393 = 98978210828 := by
        calc
          (59 : ZMod 129393864601) ^ 1974393 = (59 : ZMod 129393864601) ^ (987196 + 987196 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 987196 * (59 : ZMod 129393864601) ^ 987196) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 98978210828 := by rw [fermat_19]; decide
      have fermat_21 : (59 : ZMod 129393864601) ^ 3948787 = 31897121785 := by
        calc
          (59 : ZMod 129393864601) ^ 3948787 = (59 : ZMod 129393864601) ^ (1974393 + 1974393 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1974393 * (59 : ZMod 129393864601) ^ 1974393) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 31897121785 := by rw [fermat_20]; decide
      have fermat_22 : (59 : ZMod 129393864601) ^ 7897574 = 109039630717 := by
        calc
          (59 : ZMod 129393864601) ^ 7897574 = (59 : ZMod 129393864601) ^ (3948787 + 3948787) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3948787 * (59 : ZMod 129393864601) ^ 3948787 := by rw [pow_add]
          _ = 109039630717 := by rw [fermat_21]; decide
      have fermat_23 : (59 : ZMod 129393864601) ^ 15795149 = 100336857984 := by
        calc
          (59 : ZMod 129393864601) ^ 15795149 = (59 : ZMod 129393864601) ^ (7897574 + 7897574 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 7897574 * (59 : ZMod 129393864601) ^ 7897574) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 100336857984 := by rw [fermat_22]; decide
      have fermat_24 : (59 : ZMod 129393864601) ^ 31590298 = 94910396738 := by
        calc
          (59 : ZMod 129393864601) ^ 31590298 = (59 : ZMod 129393864601) ^ (15795149 + 15795149) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 15795149 * (59 : ZMod 129393864601) ^ 15795149 := by rw [pow_add]
          _ = 94910396738 := by rw [fermat_23]; decide
      have fermat_25 : (59 : ZMod 129393864601) ^ 63180597 = 54474407293 := by
        calc
          (59 : ZMod 129393864601) ^ 63180597 = (59 : ZMod 129393864601) ^ (31590298 + 31590298 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 31590298 * (59 : ZMod 129393864601) ^ 31590298) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 54474407293 := by rw [fermat_24]; decide
      have fermat_26 : (59 : ZMod 129393864601) ^ 126361195 = 24284047502 := by
        calc
          (59 : ZMod 129393864601) ^ 126361195 = (59 : ZMod 129393864601) ^ (63180597 + 63180597 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 63180597 * (59 : ZMod 129393864601) ^ 63180597) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 24284047502 := by rw [fermat_25]; decide
      have fermat_27 : (59 : ZMod 129393864601) ^ 252722391 = 77316351431 := by
        calc
          (59 : ZMod 129393864601) ^ 252722391 = (59 : ZMod 129393864601) ^ (126361195 + 126361195 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 126361195 * (59 : ZMod 129393864601) ^ 126361195) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 77316351431 := by rw [fermat_26]; decide
      have fermat_28 : (59 : ZMod 129393864601) ^ 505444783 = 43524795694 := by
        calc
          (59 : ZMod 129393864601) ^ 505444783 = (59 : ZMod 129393864601) ^ (252722391 + 252722391 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 252722391 * (59 : ZMod 129393864601) ^ 252722391) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 43524795694 := by rw [fermat_27]; decide
      have fermat_29 : (59 : ZMod 129393864601) ^ 1010889567 = 109351776123 := by
        calc
          (59 : ZMod 129393864601) ^ 1010889567 = (59 : ZMod 129393864601) ^ (505444783 + 505444783 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 505444783 * (59 : ZMod 129393864601) ^ 505444783) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 109351776123 := by rw [fermat_28]; decide
      have fermat_30 : (59 : ZMod 129393864601) ^ 2021779134 = 47623024947 := by
        calc
          (59 : ZMod 129393864601) ^ 2021779134 = (59 : ZMod 129393864601) ^ (1010889567 + 1010889567) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1010889567 * (59 : ZMod 129393864601) ^ 1010889567 := by rw [pow_add]
          _ = 47623024947 := by rw [fermat_29]; decide
      have fermat_31 : (59 : ZMod 129393864601) ^ 4043558268 = 27933756682 := by
        calc
          (59 : ZMod 129393864601) ^ 4043558268 = (59 : ZMod 129393864601) ^ (2021779134 + 2021779134) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2021779134 * (59 : ZMod 129393864601) ^ 2021779134 := by rw [pow_add]
          _ = 27933756682 := by rw [fermat_30]; decide
      have fermat_32 : (59 : ZMod 129393864601) ^ 8087116537 = 1082330277 := by
        calc
          (59 : ZMod 129393864601) ^ 8087116537 = (59 : ZMod 129393864601) ^ (4043558268 + 4043558268 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 4043558268 * (59 : ZMod 129393864601) ^ 4043558268) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 1082330277 := by rw [fermat_31]; decide
      have fermat_33 : (59 : ZMod 129393864601) ^ 16174233075 = 71395715718 := by
        calc
          (59 : ZMod 129393864601) ^ 16174233075 = (59 : ZMod 129393864601) ^ (8087116537 + 8087116537 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 8087116537 * (59 : ZMod 129393864601) ^ 8087116537) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 71395715718 := by rw [fermat_32]; decide
      have fermat_34 : (59 : ZMod 129393864601) ^ 32348466150 = 32786361275 := by
        calc
          (59 : ZMod 129393864601) ^ 32348466150 = (59 : ZMod 129393864601) ^ (16174233075 + 16174233075) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 16174233075 * (59 : ZMod 129393864601) ^ 16174233075 := by rw [pow_add]
          _ = 32786361275 := by rw [fermat_33]; decide
      have fermat_35 : (59 : ZMod 129393864601) ^ 64696932300 = 129393864600 := by
        calc
          (59 : ZMod 129393864601) ^ 64696932300 = (59 : ZMod 129393864601) ^ (32348466150 + 32348466150) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 32348466150 * (59 : ZMod 129393864601) ^ 32348466150 := by rw [pow_add]
          _ = 129393864600 := by rw [fermat_34]; decide
      have fermat_36 : (59 : ZMod 129393864601) ^ 129393864600 = 1 := by
        calc
          (59 : ZMod 129393864601) ^ 129393864600 = (59 : ZMod 129393864601) ^ (64696932300 + 64696932300) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 64696932300 * (59 : ZMod 129393864601) ^ 64696932300 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 129393864601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_0_1 : (59 : ZMod 129393864601) ^ 3 = 205379 := by
        calc
          (59 : ZMod 129393864601) ^ 3 = (59 : ZMod 129393864601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 205379 := by rw [factor_0_0]; decide
      have factor_0_2 : (59 : ZMod 129393864601) ^ 7 = 30168057400 := by
        calc
          (59 : ZMod 129393864601) ^ 7 = (59 : ZMod 129393864601) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 3 * (59 : ZMod 129393864601) ^ 3) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 30168057400 := by rw [factor_0_1]; decide
      have factor_0_3 : (59 : ZMod 129393864601) ^ 15 = 120007604034 := by
        calc
          (59 : ZMod 129393864601) ^ 15 = (59 : ZMod 129393864601) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 7 * (59 : ZMod 129393864601) ^ 7) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 120007604034 := by rw [factor_0_2]; decide
      have factor_0_4 : (59 : ZMod 129393864601) ^ 30 = 105232025999 := by
        calc
          (59 : ZMod 129393864601) ^ 30 = (59 : ZMod 129393864601) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 15 * (59 : ZMod 129393864601) ^ 15 := by rw [pow_add]
          _ = 105232025999 := by rw [factor_0_3]; decide
      have factor_0_5 : (59 : ZMod 129393864601) ^ 60 = 106201252252 := by
        calc
          (59 : ZMod 129393864601) ^ 60 = (59 : ZMod 129393864601) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 30 * (59 : ZMod 129393864601) ^ 30 := by rw [pow_add]
          _ = 106201252252 := by rw [factor_0_4]; decide
      have factor_0_6 : (59 : ZMod 129393864601) ^ 120 = 36236272916 := by
        calc
          (59 : ZMod 129393864601) ^ 120 = (59 : ZMod 129393864601) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 60 * (59 : ZMod 129393864601) ^ 60 := by rw [pow_add]
          _ = 36236272916 := by rw [factor_0_5]; decide
      have factor_0_7 : (59 : ZMod 129393864601) ^ 241 = 13313076293 := by
        calc
          (59 : ZMod 129393864601) ^ 241 = (59 : ZMod 129393864601) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 120 * (59 : ZMod 129393864601) ^ 120) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 13313076293 := by rw [factor_0_6]; decide
      have factor_0_8 : (59 : ZMod 129393864601) ^ 482 = 109182112620 := by
        calc
          (59 : ZMod 129393864601) ^ 482 = (59 : ZMod 129393864601) ^ (241 + 241) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 241 * (59 : ZMod 129393864601) ^ 241 := by rw [pow_add]
          _ = 109182112620 := by rw [factor_0_7]; decide
      have factor_0_9 : (59 : ZMod 129393864601) ^ 964 = 59513962683 := by
        calc
          (59 : ZMod 129393864601) ^ 964 = (59 : ZMod 129393864601) ^ (482 + 482) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 482 * (59 : ZMod 129393864601) ^ 482 := by rw [pow_add]
          _ = 59513962683 := by rw [factor_0_8]; decide
      have factor_0_10 : (59 : ZMod 129393864601) ^ 1928 = 12994517568 := by
        calc
          (59 : ZMod 129393864601) ^ 1928 = (59 : ZMod 129393864601) ^ (964 + 964) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 964 * (59 : ZMod 129393864601) ^ 964 := by rw [pow_add]
          _ = 12994517568 := by rw [factor_0_9]; decide
      have factor_0_11 : (59 : ZMod 129393864601) ^ 3856 = 53521184067 := by
        calc
          (59 : ZMod 129393864601) ^ 3856 = (59 : ZMod 129393864601) ^ (1928 + 1928) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1928 * (59 : ZMod 129393864601) ^ 1928 := by rw [pow_add]
          _ = 53521184067 := by rw [factor_0_10]; decide
      have factor_0_12 : (59 : ZMod 129393864601) ^ 7712 = 58553654785 := by
        calc
          (59 : ZMod 129393864601) ^ 7712 = (59 : ZMod 129393864601) ^ (3856 + 3856) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3856 * (59 : ZMod 129393864601) ^ 3856 := by rw [pow_add]
          _ = 58553654785 := by rw [factor_0_11]; decide
      have factor_0_13 : (59 : ZMod 129393864601) ^ 15424 = 14392934267 := by
        calc
          (59 : ZMod 129393864601) ^ 15424 = (59 : ZMod 129393864601) ^ (7712 + 7712) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 7712 * (59 : ZMod 129393864601) ^ 7712 := by rw [pow_add]
          _ = 14392934267 := by rw [factor_0_12]; decide
      have factor_0_14 : (59 : ZMod 129393864601) ^ 30849 = 26709057675 := by
        calc
          (59 : ZMod 129393864601) ^ 30849 = (59 : ZMod 129393864601) ^ (15424 + 15424 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 15424 * (59 : ZMod 129393864601) ^ 15424) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 26709057675 := by rw [factor_0_13]; decide
      have factor_0_15 : (59 : ZMod 129393864601) ^ 61699 = 107131182011 := by
        calc
          (59 : ZMod 129393864601) ^ 61699 = (59 : ZMod 129393864601) ^ (30849 + 30849 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 30849 * (59 : ZMod 129393864601) ^ 30849) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 107131182011 := by rw [factor_0_14]; decide
      have factor_0_16 : (59 : ZMod 129393864601) ^ 123399 = 61307937637 := by
        calc
          (59 : ZMod 129393864601) ^ 123399 = (59 : ZMod 129393864601) ^ (61699 + 61699 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 61699 * (59 : ZMod 129393864601) ^ 61699) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 61307937637 := by rw [factor_0_15]; decide
      have factor_0_17 : (59 : ZMod 129393864601) ^ 246799 = 1153396915 := by
        calc
          (59 : ZMod 129393864601) ^ 246799 = (59 : ZMod 129393864601) ^ (123399 + 123399 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 123399 * (59 : ZMod 129393864601) ^ 123399) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 1153396915 := by rw [factor_0_16]; decide
      have factor_0_18 : (59 : ZMod 129393864601) ^ 493598 = 113401851424 := by
        calc
          (59 : ZMod 129393864601) ^ 493598 = (59 : ZMod 129393864601) ^ (246799 + 246799) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 246799 * (59 : ZMod 129393864601) ^ 246799 := by rw [pow_add]
          _ = 113401851424 := by rw [factor_0_17]; decide
      have factor_0_19 : (59 : ZMod 129393864601) ^ 987196 = 54693681357 := by
        calc
          (59 : ZMod 129393864601) ^ 987196 = (59 : ZMod 129393864601) ^ (493598 + 493598) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 493598 * (59 : ZMod 129393864601) ^ 493598 := by rw [pow_add]
          _ = 54693681357 := by rw [factor_0_18]; decide
      have factor_0_20 : (59 : ZMod 129393864601) ^ 1974393 = 98978210828 := by
        calc
          (59 : ZMod 129393864601) ^ 1974393 = (59 : ZMod 129393864601) ^ (987196 + 987196 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 987196 * (59 : ZMod 129393864601) ^ 987196) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 98978210828 := by rw [factor_0_19]; decide
      have factor_0_21 : (59 : ZMod 129393864601) ^ 3948787 = 31897121785 := by
        calc
          (59 : ZMod 129393864601) ^ 3948787 = (59 : ZMod 129393864601) ^ (1974393 + 1974393 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1974393 * (59 : ZMod 129393864601) ^ 1974393) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 31897121785 := by rw [factor_0_20]; decide
      have factor_0_22 : (59 : ZMod 129393864601) ^ 7897574 = 109039630717 := by
        calc
          (59 : ZMod 129393864601) ^ 7897574 = (59 : ZMod 129393864601) ^ (3948787 + 3948787) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3948787 * (59 : ZMod 129393864601) ^ 3948787 := by rw [pow_add]
          _ = 109039630717 := by rw [factor_0_21]; decide
      have factor_0_23 : (59 : ZMod 129393864601) ^ 15795149 = 100336857984 := by
        calc
          (59 : ZMod 129393864601) ^ 15795149 = (59 : ZMod 129393864601) ^ (7897574 + 7897574 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 7897574 * (59 : ZMod 129393864601) ^ 7897574) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 100336857984 := by rw [factor_0_22]; decide
      have factor_0_24 : (59 : ZMod 129393864601) ^ 31590298 = 94910396738 := by
        calc
          (59 : ZMod 129393864601) ^ 31590298 = (59 : ZMod 129393864601) ^ (15795149 + 15795149) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 15795149 * (59 : ZMod 129393864601) ^ 15795149 := by rw [pow_add]
          _ = 94910396738 := by rw [factor_0_23]; decide
      have factor_0_25 : (59 : ZMod 129393864601) ^ 63180597 = 54474407293 := by
        calc
          (59 : ZMod 129393864601) ^ 63180597 = (59 : ZMod 129393864601) ^ (31590298 + 31590298 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 31590298 * (59 : ZMod 129393864601) ^ 31590298) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 54474407293 := by rw [factor_0_24]; decide
      have factor_0_26 : (59 : ZMod 129393864601) ^ 126361195 = 24284047502 := by
        calc
          (59 : ZMod 129393864601) ^ 126361195 = (59 : ZMod 129393864601) ^ (63180597 + 63180597 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 63180597 * (59 : ZMod 129393864601) ^ 63180597) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 24284047502 := by rw [factor_0_25]; decide
      have factor_0_27 : (59 : ZMod 129393864601) ^ 252722391 = 77316351431 := by
        calc
          (59 : ZMod 129393864601) ^ 252722391 = (59 : ZMod 129393864601) ^ (126361195 + 126361195 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 126361195 * (59 : ZMod 129393864601) ^ 126361195) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 77316351431 := by rw [factor_0_26]; decide
      have factor_0_28 : (59 : ZMod 129393864601) ^ 505444783 = 43524795694 := by
        calc
          (59 : ZMod 129393864601) ^ 505444783 = (59 : ZMod 129393864601) ^ (252722391 + 252722391 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 252722391 * (59 : ZMod 129393864601) ^ 252722391) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 43524795694 := by rw [factor_0_27]; decide
      have factor_0_29 : (59 : ZMod 129393864601) ^ 1010889567 = 109351776123 := by
        calc
          (59 : ZMod 129393864601) ^ 1010889567 = (59 : ZMod 129393864601) ^ (505444783 + 505444783 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 505444783 * (59 : ZMod 129393864601) ^ 505444783) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 109351776123 := by rw [factor_0_28]; decide
      have factor_0_30 : (59 : ZMod 129393864601) ^ 2021779134 = 47623024947 := by
        calc
          (59 : ZMod 129393864601) ^ 2021779134 = (59 : ZMod 129393864601) ^ (1010889567 + 1010889567) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1010889567 * (59 : ZMod 129393864601) ^ 1010889567 := by rw [pow_add]
          _ = 47623024947 := by rw [factor_0_29]; decide
      have factor_0_31 : (59 : ZMod 129393864601) ^ 4043558268 = 27933756682 := by
        calc
          (59 : ZMod 129393864601) ^ 4043558268 = (59 : ZMod 129393864601) ^ (2021779134 + 2021779134) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2021779134 * (59 : ZMod 129393864601) ^ 2021779134 := by rw [pow_add]
          _ = 27933756682 := by rw [factor_0_30]; decide
      have factor_0_32 : (59 : ZMod 129393864601) ^ 8087116537 = 1082330277 := by
        calc
          (59 : ZMod 129393864601) ^ 8087116537 = (59 : ZMod 129393864601) ^ (4043558268 + 4043558268 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 4043558268 * (59 : ZMod 129393864601) ^ 4043558268) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 1082330277 := by rw [factor_0_31]; decide
      have factor_0_33 : (59 : ZMod 129393864601) ^ 16174233075 = 71395715718 := by
        calc
          (59 : ZMod 129393864601) ^ 16174233075 = (59 : ZMod 129393864601) ^ (8087116537 + 8087116537 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 8087116537 * (59 : ZMod 129393864601) ^ 8087116537) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 71395715718 := by rw [factor_0_32]; decide
      have factor_0_34 : (59 : ZMod 129393864601) ^ 32348466150 = 32786361275 := by
        calc
          (59 : ZMod 129393864601) ^ 32348466150 = (59 : ZMod 129393864601) ^ (16174233075 + 16174233075) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 16174233075 * (59 : ZMod 129393864601) ^ 16174233075 := by rw [pow_add]
          _ = 32786361275 := by rw [factor_0_33]; decide
      have factor_0_35 : (59 : ZMod 129393864601) ^ 64696932300 = 129393864600 := by
        calc
          (59 : ZMod 129393864601) ^ 64696932300 = (59 : ZMod 129393864601) ^ (32348466150 + 32348466150) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 32348466150 * (59 : ZMod 129393864601) ^ 32348466150 := by rw [pow_add]
          _ = 129393864600 := by rw [factor_0_34]; decide
      change (59 : ZMod 129393864601) ^ 64696932300 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_1_1 : (59 : ZMod 129393864601) ^ 2 = 3481 := by
        calc
          (59 : ZMod 129393864601) ^ 2 = (59 : ZMod 129393864601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1 := by rw [pow_add]
          _ = 3481 := by rw [factor_1_0]; decide
      have factor_1_2 : (59 : ZMod 129393864601) ^ 5 = 714924299 := by
        calc
          (59 : ZMod 129393864601) ^ 5 = (59 : ZMod 129393864601) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2 * (59 : ZMod 129393864601) ^ 2) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 714924299 := by rw [factor_1_1]; decide
      have factor_1_3 : (59 : ZMod 129393864601) ^ 10 = 119042064917 := by
        calc
          (59 : ZMod 129393864601) ^ 10 = (59 : ZMod 129393864601) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 5 * (59 : ZMod 129393864601) ^ 5 := by rw [pow_add]
          _ = 119042064917 := by rw [factor_1_2]; decide
      have factor_1_4 : (59 : ZMod 129393864601) ^ 20 = 83571379040 := by
        calc
          (59 : ZMod 129393864601) ^ 20 = (59 : ZMod 129393864601) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 10 * (59 : ZMod 129393864601) ^ 10 := by rw [pow_add]
          _ = 83571379040 := by rw [factor_1_3]; decide
      have factor_1_5 : (59 : ZMod 129393864601) ^ 40 = 61106494832 := by
        calc
          (59 : ZMod 129393864601) ^ 40 = (59 : ZMod 129393864601) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 20 * (59 : ZMod 129393864601) ^ 20 := by rw [pow_add]
          _ = 61106494832 := by rw [factor_1_4]; decide
      have factor_1_6 : (59 : ZMod 129393864601) ^ 80 = 109476420826 := by
        calc
          (59 : ZMod 129393864601) ^ 80 = (59 : ZMod 129393864601) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 40 * (59 : ZMod 129393864601) ^ 40 := by rw [pow_add]
          _ = 109476420826 := by rw [factor_1_5]; decide
      have factor_1_7 : (59 : ZMod 129393864601) ^ 160 = 73477835180 := by
        calc
          (59 : ZMod 129393864601) ^ 160 = (59 : ZMod 129393864601) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 80 * (59 : ZMod 129393864601) ^ 80 := by rw [pow_add]
          _ = 73477835180 := by rw [factor_1_6]; decide
      have factor_1_8 : (59 : ZMod 129393864601) ^ 321 = 91258585935 := by
        calc
          (59 : ZMod 129393864601) ^ 321 = (59 : ZMod 129393864601) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 160 * (59 : ZMod 129393864601) ^ 160) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 91258585935 := by rw [factor_1_7]; decide
      have factor_1_9 : (59 : ZMod 129393864601) ^ 642 = 93683861044 := by
        calc
          (59 : ZMod 129393864601) ^ 642 = (59 : ZMod 129393864601) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 321 * (59 : ZMod 129393864601) ^ 321 := by rw [pow_add]
          _ = 93683861044 := by rw [factor_1_8]; decide
      have factor_1_10 : (59 : ZMod 129393864601) ^ 1285 = 10708589276 := by
        calc
          (59 : ZMod 129393864601) ^ 1285 = (59 : ZMod 129393864601) ^ (642 + 642 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 642 * (59 : ZMod 129393864601) ^ 642) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 10708589276 := by rw [factor_1_9]; decide
      have factor_1_11 : (59 : ZMod 129393864601) ^ 2570 = 28903420014 := by
        calc
          (59 : ZMod 129393864601) ^ 2570 = (59 : ZMod 129393864601) ^ (1285 + 1285) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1285 * (59 : ZMod 129393864601) ^ 1285 := by rw [pow_add]
          _ = 28903420014 := by rw [factor_1_10]; decide
      have factor_1_12 : (59 : ZMod 129393864601) ^ 5141 = 128199194323 := by
        calc
          (59 : ZMod 129393864601) ^ 5141 = (59 : ZMod 129393864601) ^ (2570 + 2570 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2570 * (59 : ZMod 129393864601) ^ 2570) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 128199194323 := by rw [factor_1_11]; decide
      have factor_1_13 : (59 : ZMod 129393864601) ^ 10283 = 104896692785 := by
        calc
          (59 : ZMod 129393864601) ^ 10283 = (59 : ZMod 129393864601) ^ (5141 + 5141 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 5141 * (59 : ZMod 129393864601) ^ 5141) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 104896692785 := by rw [factor_1_12]; decide
      have factor_1_14 : (59 : ZMod 129393864601) ^ 20566 = 2874018888 := by
        calc
          (59 : ZMod 129393864601) ^ 20566 = (59 : ZMod 129393864601) ^ (10283 + 10283) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 10283 * (59 : ZMod 129393864601) ^ 10283 := by rw [pow_add]
          _ = 2874018888 := by rw [factor_1_13]; decide
      have factor_1_15 : (59 : ZMod 129393864601) ^ 41133 = 76087731687 := by
        calc
          (59 : ZMod 129393864601) ^ 41133 = (59 : ZMod 129393864601) ^ (20566 + 20566 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 20566 * (59 : ZMod 129393864601) ^ 20566) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 76087731687 := by rw [factor_1_14]; decide
      have factor_1_16 : (59 : ZMod 129393864601) ^ 82266 = 93144809896 := by
        calc
          (59 : ZMod 129393864601) ^ 82266 = (59 : ZMod 129393864601) ^ (41133 + 41133) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 41133 * (59 : ZMod 129393864601) ^ 41133 := by rw [pow_add]
          _ = 93144809896 := by rw [factor_1_15]; decide
      have factor_1_17 : (59 : ZMod 129393864601) ^ 164532 = 82203746852 := by
        calc
          (59 : ZMod 129393864601) ^ 164532 = (59 : ZMod 129393864601) ^ (82266 + 82266) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 82266 * (59 : ZMod 129393864601) ^ 82266 := by rw [pow_add]
          _ = 82203746852 := by rw [factor_1_16]; decide
      have factor_1_18 : (59 : ZMod 129393864601) ^ 329065 = 77030639198 := by
        calc
          (59 : ZMod 129393864601) ^ 329065 = (59 : ZMod 129393864601) ^ (164532 + 164532 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 164532 * (59 : ZMod 129393864601) ^ 164532) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 77030639198 := by rw [factor_1_17]; decide
      have factor_1_19 : (59 : ZMod 129393864601) ^ 658131 = 45658653990 := by
        calc
          (59 : ZMod 129393864601) ^ 658131 = (59 : ZMod 129393864601) ^ (329065 + 329065 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 329065 * (59 : ZMod 129393864601) ^ 329065) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 45658653990 := by rw [factor_1_18]; decide
      have factor_1_20 : (59 : ZMod 129393864601) ^ 1316262 = 50259233923 := by
        calc
          (59 : ZMod 129393864601) ^ 1316262 = (59 : ZMod 129393864601) ^ (658131 + 658131) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 658131 * (59 : ZMod 129393864601) ^ 658131 := by rw [pow_add]
          _ = 50259233923 := by rw [factor_1_19]; decide
      have factor_1_21 : (59 : ZMod 129393864601) ^ 2632524 = 111114923075 := by
        calc
          (59 : ZMod 129393864601) ^ 2632524 = (59 : ZMod 129393864601) ^ (1316262 + 1316262) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1316262 * (59 : ZMod 129393864601) ^ 1316262 := by rw [pow_add]
          _ = 111114923075 := by rw [factor_1_20]; decide
      have factor_1_22 : (59 : ZMod 129393864601) ^ 5265049 = 77212874894 := by
        calc
          (59 : ZMod 129393864601) ^ 5265049 = (59 : ZMod 129393864601) ^ (2632524 + 2632524 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2632524 * (59 : ZMod 129393864601) ^ 2632524) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 77212874894 := by rw [factor_1_21]; decide
      have factor_1_23 : (59 : ZMod 129393864601) ^ 10530099 = 17007951599 := by
        calc
          (59 : ZMod 129393864601) ^ 10530099 = (59 : ZMod 129393864601) ^ (5265049 + 5265049 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 5265049 * (59 : ZMod 129393864601) ^ 5265049) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 17007951599 := by rw [factor_1_22]; decide
      have factor_1_24 : (59 : ZMod 129393864601) ^ 21060199 = 63313747575 := by
        calc
          (59 : ZMod 129393864601) ^ 21060199 = (59 : ZMod 129393864601) ^ (10530099 + 10530099 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 10530099 * (59 : ZMod 129393864601) ^ 10530099) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 63313747575 := by rw [factor_1_23]; decide
      have factor_1_25 : (59 : ZMod 129393864601) ^ 42120398 = 126870973138 := by
        calc
          (59 : ZMod 129393864601) ^ 42120398 = (59 : ZMod 129393864601) ^ (21060199 + 21060199) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 21060199 * (59 : ZMod 129393864601) ^ 21060199 := by rw [pow_add]
          _ = 126870973138 := by rw [factor_1_24]; decide
      have factor_1_26 : (59 : ZMod 129393864601) ^ 84240797 = 72687153481 := by
        calc
          (59 : ZMod 129393864601) ^ 84240797 = (59 : ZMod 129393864601) ^ (42120398 + 42120398 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 42120398 * (59 : ZMod 129393864601) ^ 42120398) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 72687153481 := by rw [factor_1_25]; decide
      have factor_1_27 : (59 : ZMod 129393864601) ^ 168481594 = 113295080808 := by
        calc
          (59 : ZMod 129393864601) ^ 168481594 = (59 : ZMod 129393864601) ^ (84240797 + 84240797) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 84240797 * (59 : ZMod 129393864601) ^ 84240797 := by rw [pow_add]
          _ = 113295080808 := by rw [factor_1_26]; decide
      have factor_1_28 : (59 : ZMod 129393864601) ^ 336963189 = 21637999209 := by
        calc
          (59 : ZMod 129393864601) ^ 336963189 = (59 : ZMod 129393864601) ^ (168481594 + 168481594 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 168481594 * (59 : ZMod 129393864601) ^ 168481594) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 21637999209 := by rw [factor_1_27]; decide
      have factor_1_29 : (59 : ZMod 129393864601) ^ 673926378 = 25549541235 := by
        calc
          (59 : ZMod 129393864601) ^ 673926378 = (59 : ZMod 129393864601) ^ (336963189 + 336963189) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 336963189 * (59 : ZMod 129393864601) ^ 336963189 := by rw [pow_add]
          _ = 25549541235 := by rw [factor_1_28]; decide
      have factor_1_30 : (59 : ZMod 129393864601) ^ 1347852756 = 127593755014 := by
        calc
          (59 : ZMod 129393864601) ^ 1347852756 = (59 : ZMod 129393864601) ^ (673926378 + 673926378) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 673926378 * (59 : ZMod 129393864601) ^ 673926378 := by rw [pow_add]
          _ = 127593755014 := by rw [factor_1_29]; decide
      have factor_1_31 : (59 : ZMod 129393864601) ^ 2695705512 = 18845678093 := by
        calc
          (59 : ZMod 129393864601) ^ 2695705512 = (59 : ZMod 129393864601) ^ (1347852756 + 1347852756) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1347852756 * (59 : ZMod 129393864601) ^ 1347852756 := by rw [pow_add]
          _ = 18845678093 := by rw [factor_1_30]; decide
      have factor_1_32 : (59 : ZMod 129393864601) ^ 5391411025 = 56492201400 := by
        calc
          (59 : ZMod 129393864601) ^ 5391411025 = (59 : ZMod 129393864601) ^ (2695705512 + 2695705512 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2695705512 * (59 : ZMod 129393864601) ^ 2695705512) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 56492201400 := by rw [factor_1_31]; decide
      have factor_1_33 : (59 : ZMod 129393864601) ^ 10782822050 = 120982690265 := by
        calc
          (59 : ZMod 129393864601) ^ 10782822050 = (59 : ZMod 129393864601) ^ (5391411025 + 5391411025) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 5391411025 * (59 : ZMod 129393864601) ^ 5391411025 := by rw [pow_add]
          _ = 120982690265 := by rw [factor_1_32]; decide
      have factor_1_34 : (59 : ZMod 129393864601) ^ 21565644100 = 36156092508 := by
        calc
          (59 : ZMod 129393864601) ^ 21565644100 = (59 : ZMod 129393864601) ^ (10782822050 + 10782822050) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 10782822050 * (59 : ZMod 129393864601) ^ 10782822050 := by rw [pow_add]
          _ = 36156092508 := by rw [factor_1_33]; decide
      have factor_1_35 : (59 : ZMod 129393864601) ^ 43131288200 = 36156092507 := by
        calc
          (59 : ZMod 129393864601) ^ 43131288200 = (59 : ZMod 129393864601) ^ (21565644100 + 21565644100) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 21565644100 * (59 : ZMod 129393864601) ^ 21565644100 := by rw [pow_add]
          _ = 36156092507 := by rw [factor_1_34]; decide
      change (59 : ZMod 129393864601) ^ 43131288200 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_2_1 : (59 : ZMod 129393864601) ^ 3 = 205379 := by
        calc
          (59 : ZMod 129393864601) ^ 3 = (59 : ZMod 129393864601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 205379 := by rw [factor_2_0]; decide
      have factor_2_2 : (59 : ZMod 129393864601) ^ 6 = 42180533641 := by
        calc
          (59 : ZMod 129393864601) ^ 6 = (59 : ZMod 129393864601) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3 * (59 : ZMod 129393864601) ^ 3 := by rw [pow_add]
          _ = 42180533641 := by rw [factor_2_1]; decide
      have factor_2_3 : (59 : ZMod 129393864601) ^ 12 = 66273523675 := by
        calc
          (59 : ZMod 129393864601) ^ 12 = (59 : ZMod 129393864601) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 6 * (59 : ZMod 129393864601) ^ 6 := by rw [pow_add]
          _ = 66273523675 := by rw [factor_2_2]; decide
      have factor_2_4 : (59 : ZMod 129393864601) ^ 24 = 106259469023 := by
        calc
          (59 : ZMod 129393864601) ^ 24 = (59 : ZMod 129393864601) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 12 * (59 : ZMod 129393864601) ^ 12 := by rw [pow_add]
          _ = 106259469023 := by rw [factor_2_3]; decide
      have factor_2_5 : (59 : ZMod 129393864601) ^ 48 = 78422600205 := by
        calc
          (59 : ZMod 129393864601) ^ 48 = (59 : ZMod 129393864601) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 24 * (59 : ZMod 129393864601) ^ 24 := by rw [pow_add]
          _ = 78422600205 := by rw [factor_2_4]; decide
      have factor_2_6 : (59 : ZMod 129393864601) ^ 96 = 12704694277 := by
        calc
          (59 : ZMod 129393864601) ^ 96 = (59 : ZMod 129393864601) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 48 * (59 : ZMod 129393864601) ^ 48 := by rw [pow_add]
          _ = 12704694277 := by rw [factor_2_5]; decide
      have factor_2_7 : (59 : ZMod 129393864601) ^ 192 = 90988497440 := by
        calc
          (59 : ZMod 129393864601) ^ 192 = (59 : ZMod 129393864601) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 96 * (59 : ZMod 129393864601) ^ 96 := by rw [pow_add]
          _ = 90988497440 := by rw [factor_2_6]; decide
      have factor_2_8 : (59 : ZMod 129393864601) ^ 385 = 19901410793 := by
        calc
          (59 : ZMod 129393864601) ^ 385 = (59 : ZMod 129393864601) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 192 * (59 : ZMod 129393864601) ^ 192) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 19901410793 := by rw [factor_2_7]; decide
      have factor_2_9 : (59 : ZMod 129393864601) ^ 771 = 55265020660 := by
        calc
          (59 : ZMod 129393864601) ^ 771 = (59 : ZMod 129393864601) ^ (385 + 385 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 385 * (59 : ZMod 129393864601) ^ 385) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 55265020660 := by rw [factor_2_8]; decide
      have factor_2_10 : (59 : ZMod 129393864601) ^ 1542 = 30512809415 := by
        calc
          (59 : ZMod 129393864601) ^ 1542 = (59 : ZMod 129393864601) ^ (771 + 771) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 771 * (59 : ZMod 129393864601) ^ 771 := by rw [pow_add]
          _ = 30512809415 := by rw [factor_2_9]; decide
      have factor_2_11 : (59 : ZMod 129393864601) ^ 3084 = 84771033360 := by
        calc
          (59 : ZMod 129393864601) ^ 3084 = (59 : ZMod 129393864601) ^ (1542 + 1542) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1542 * (59 : ZMod 129393864601) ^ 1542 := by rw [pow_add]
          _ = 84771033360 := by rw [factor_2_10]; decide
      have factor_2_12 : (59 : ZMod 129393864601) ^ 6169 = 98121709482 := by
        calc
          (59 : ZMod 129393864601) ^ 6169 = (59 : ZMod 129393864601) ^ (3084 + 3084 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 3084 * (59 : ZMod 129393864601) ^ 3084) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 98121709482 := by rw [factor_2_11]; decide
      have factor_2_13 : (59 : ZMod 129393864601) ^ 12339 = 78185961137 := by
        calc
          (59 : ZMod 129393864601) ^ 12339 = (59 : ZMod 129393864601) ^ (6169 + 6169 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 6169 * (59 : ZMod 129393864601) ^ 6169) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 78185961137 := by rw [factor_2_12]; decide
      have factor_2_14 : (59 : ZMod 129393864601) ^ 24679 = 24228301933 := by
        calc
          (59 : ZMod 129393864601) ^ 24679 = (59 : ZMod 129393864601) ^ (12339 + 12339 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 12339 * (59 : ZMod 129393864601) ^ 12339) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 24228301933 := by rw [factor_2_13]; decide
      have factor_2_15 : (59 : ZMod 129393864601) ^ 49359 = 112467831085 := by
        calc
          (59 : ZMod 129393864601) ^ 49359 = (59 : ZMod 129393864601) ^ (24679 + 24679 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 24679 * (59 : ZMod 129393864601) ^ 24679) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 112467831085 := by rw [factor_2_14]; decide
      have factor_2_16 : (59 : ZMod 129393864601) ^ 98719 = 89546600828 := by
        calc
          (59 : ZMod 129393864601) ^ 98719 = (59 : ZMod 129393864601) ^ (49359 + 49359 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 49359 * (59 : ZMod 129393864601) ^ 49359) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 89546600828 := by rw [factor_2_15]; decide
      have factor_2_17 : (59 : ZMod 129393864601) ^ 197439 = 53637321494 := by
        calc
          (59 : ZMod 129393864601) ^ 197439 = (59 : ZMod 129393864601) ^ (98719 + 98719 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 98719 * (59 : ZMod 129393864601) ^ 98719) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 53637321494 := by rw [factor_2_16]; decide
      have factor_2_18 : (59 : ZMod 129393864601) ^ 394878 = 20982986045 := by
        calc
          (59 : ZMod 129393864601) ^ 394878 = (59 : ZMod 129393864601) ^ (197439 + 197439) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 197439 * (59 : ZMod 129393864601) ^ 197439 := by rw [pow_add]
          _ = 20982986045 := by rw [factor_2_17]; decide
      have factor_2_19 : (59 : ZMod 129393864601) ^ 789757 = 96079199267 := by
        calc
          (59 : ZMod 129393864601) ^ 789757 = (59 : ZMod 129393864601) ^ (394878 + 394878 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 394878 * (59 : ZMod 129393864601) ^ 394878) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 96079199267 := by rw [factor_2_18]; decide
      have factor_2_20 : (59 : ZMod 129393864601) ^ 1579514 = 28293261504 := by
        calc
          (59 : ZMod 129393864601) ^ 1579514 = (59 : ZMod 129393864601) ^ (789757 + 789757) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 789757 * (59 : ZMod 129393864601) ^ 789757 := by rw [pow_add]
          _ = 28293261504 := by rw [factor_2_19]; decide
      have factor_2_21 : (59 : ZMod 129393864601) ^ 3159029 = 128768206071 := by
        calc
          (59 : ZMod 129393864601) ^ 3159029 = (59 : ZMod 129393864601) ^ (1579514 + 1579514 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1579514 * (59 : ZMod 129393864601) ^ 1579514) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 128768206071 := by rw [factor_2_20]; decide
      have factor_2_22 : (59 : ZMod 129393864601) ^ 6318059 = 16037638238 := by
        calc
          (59 : ZMod 129393864601) ^ 6318059 = (59 : ZMod 129393864601) ^ (3159029 + 3159029 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 3159029 * (59 : ZMod 129393864601) ^ 3159029) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 16037638238 := by rw [factor_2_21]; decide
      have factor_2_23 : (59 : ZMod 129393864601) ^ 12636119 = 26556832518 := by
        calc
          (59 : ZMod 129393864601) ^ 12636119 = (59 : ZMod 129393864601) ^ (6318059 + 6318059 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 6318059 * (59 : ZMod 129393864601) ^ 6318059) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 26556832518 := by rw [factor_2_22]; decide
      have factor_2_24 : (59 : ZMod 129393864601) ^ 25272239 = 117869006393 := by
        calc
          (59 : ZMod 129393864601) ^ 25272239 = (59 : ZMod 129393864601) ^ (12636119 + 12636119 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 12636119 * (59 : ZMod 129393864601) ^ 12636119) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 117869006393 := by rw [factor_2_23]; decide
      have factor_2_25 : (59 : ZMod 129393864601) ^ 50544478 = 75260427906 := by
        calc
          (59 : ZMod 129393864601) ^ 50544478 = (59 : ZMod 129393864601) ^ (25272239 + 25272239) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 25272239 * (59 : ZMod 129393864601) ^ 25272239 := by rw [pow_add]
          _ = 75260427906 := by rw [factor_2_24]; decide
      have factor_2_26 : (59 : ZMod 129393864601) ^ 101088956 = 43018539019 := by
        calc
          (59 : ZMod 129393864601) ^ 101088956 = (59 : ZMod 129393864601) ^ (50544478 + 50544478) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 50544478 * (59 : ZMod 129393864601) ^ 50544478 := by rw [pow_add]
          _ = 43018539019 := by rw [factor_2_25]; decide
      have factor_2_27 : (59 : ZMod 129393864601) ^ 202177913 = 110876209802 := by
        calc
          (59 : ZMod 129393864601) ^ 202177913 = (59 : ZMod 129393864601) ^ (101088956 + 101088956 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 101088956 * (59 : ZMod 129393864601) ^ 101088956) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 110876209802 := by rw [factor_2_26]; decide
      have factor_2_28 : (59 : ZMod 129393864601) ^ 404355826 = 100062413479 := by
        calc
          (59 : ZMod 129393864601) ^ 404355826 = (59 : ZMod 129393864601) ^ (202177913 + 202177913) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 202177913 * (59 : ZMod 129393864601) ^ 202177913 := by rw [pow_add]
          _ = 100062413479 := by rw [factor_2_27]; decide
      have factor_2_29 : (59 : ZMod 129393864601) ^ 808711653 = 87706739445 := by
        calc
          (59 : ZMod 129393864601) ^ 808711653 = (59 : ZMod 129393864601) ^ (404355826 + 404355826 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 404355826 * (59 : ZMod 129393864601) ^ 404355826) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 87706739445 := by rw [factor_2_28]; decide
      have factor_2_30 : (59 : ZMod 129393864601) ^ 1617423307 = 44375811 := by
        calc
          (59 : ZMod 129393864601) ^ 1617423307 = (59 : ZMod 129393864601) ^ (808711653 + 808711653 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 808711653 * (59 : ZMod 129393864601) ^ 808711653) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 44375811 := by rw [factor_2_29]; decide
      have factor_2_31 : (59 : ZMod 129393864601) ^ 3234846615 = 16124130033 := by
        calc
          (59 : ZMod 129393864601) ^ 3234846615 = (59 : ZMod 129393864601) ^ (1617423307 + 1617423307 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1617423307 * (59 : ZMod 129393864601) ^ 1617423307) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 16124130033 := by rw [factor_2_30]; decide
      have factor_2_32 : (59 : ZMod 129393864601) ^ 6469693230 = 55660907915 := by
        calc
          (59 : ZMod 129393864601) ^ 6469693230 = (59 : ZMod 129393864601) ^ (3234846615 + 3234846615) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3234846615 * (59 : ZMod 129393864601) ^ 3234846615 := by rw [pow_add]
          _ = 55660907915 := by rw [factor_2_31]; decide
      have factor_2_33 : (59 : ZMod 129393864601) ^ 12939386460 = 122865634996 := by
        calc
          (59 : ZMod 129393864601) ^ 12939386460 = (59 : ZMod 129393864601) ^ (6469693230 + 6469693230) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 6469693230 * (59 : ZMod 129393864601) ^ 6469693230 := by rw [pow_add]
          _ = 122865634996 := by rw [factor_2_32]; decide
      have factor_2_34 : (59 : ZMod 129393864601) ^ 25878772920 = 27940303245 := by
        calc
          (59 : ZMod 129393864601) ^ 25878772920 = (59 : ZMod 129393864601) ^ (12939386460 + 12939386460) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 12939386460 * (59 : ZMod 129393864601) ^ 12939386460 := by rw [pow_add]
          _ = 27940303245 := by rw [factor_2_33]; decide
      change (59 : ZMod 129393864601) ^ 25878772920 ≠ 1
      rw [factor_2_34]
      decide
    ·
      have factor_3_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_3_1 : (59 : ZMod 129393864601) ^ 2 = 3481 := by
        calc
          (59 : ZMod 129393864601) ^ 2 = (59 : ZMod 129393864601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1 := by rw [pow_add]
          _ = 3481 := by rw [factor_3_0]; decide
      have factor_3_2 : (59 : ZMod 129393864601) ^ 4 = 12117361 := by
        calc
          (59 : ZMod 129393864601) ^ 4 = (59 : ZMod 129393864601) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2 * (59 : ZMod 129393864601) ^ 2 := by rw [pow_add]
          _ = 12117361 := by rw [factor_3_1]; decide
      have factor_3_3 : (59 : ZMod 129393864601) ^ 8 = 97795146787 := by
        calc
          (59 : ZMod 129393864601) ^ 8 = (59 : ZMod 129393864601) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 4 * (59 : ZMod 129393864601) ^ 4 := by rw [pow_add]
          _ = 97795146787 := by rw [factor_3_2]; decide
      have factor_3_4 : (59 : ZMod 129393864601) ^ 17 = 63074710326 := by
        calc
          (59 : ZMod 129393864601) ^ 17 = (59 : ZMod 129393864601) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 8 * (59 : ZMod 129393864601) ^ 8) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 63074710326 := by rw [factor_3_3]; decide
      have factor_3_5 : (59 : ZMod 129393864601) ^ 34 = 94548273565 := by
        calc
          (59 : ZMod 129393864601) ^ 34 = (59 : ZMod 129393864601) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 17 * (59 : ZMod 129393864601) ^ 17 := by rw [pow_add]
          _ = 94548273565 := by rw [factor_3_4]; decide
      have factor_3_6 : (59 : ZMod 129393864601) ^ 68 = 83268515216 := by
        calc
          (59 : ZMod 129393864601) ^ 68 = (59 : ZMod 129393864601) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 34 * (59 : ZMod 129393864601) ^ 34 := by rw [pow_add]
          _ = 83268515216 := by rw [factor_3_5]; decide
      have factor_3_7 : (59 : ZMod 129393864601) ^ 137 = 80124765219 := by
        calc
          (59 : ZMod 129393864601) ^ 137 = (59 : ZMod 129393864601) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 68 * (59 : ZMod 129393864601) ^ 68) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 80124765219 := by rw [factor_3_6]; decide
      have factor_3_8 : (59 : ZMod 129393864601) ^ 275 = 92276067318 := by
        calc
          (59 : ZMod 129393864601) ^ 275 = (59 : ZMod 129393864601) ^ (137 + 137 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 137 * (59 : ZMod 129393864601) ^ 137) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 92276067318 := by rw [factor_3_7]; decide
      have factor_3_9 : (59 : ZMod 129393864601) ^ 550 = 109554628311 := by
        calc
          (59 : ZMod 129393864601) ^ 550 = (59 : ZMod 129393864601) ^ (275 + 275) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 275 * (59 : ZMod 129393864601) ^ 275 := by rw [pow_add]
          _ = 109554628311 := by rw [factor_3_8]; decide
      have factor_3_10 : (59 : ZMod 129393864601) ^ 1101 = 36533327953 := by
        calc
          (59 : ZMod 129393864601) ^ 1101 = (59 : ZMod 129393864601) ^ (550 + 550 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 550 * (59 : ZMod 129393864601) ^ 550) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 36533327953 := by rw [factor_3_9]; decide
      have factor_3_11 : (59 : ZMod 129393864601) ^ 2203 = 10110753240 := by
        calc
          (59 : ZMod 129393864601) ^ 2203 = (59 : ZMod 129393864601) ^ (1101 + 1101 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1101 * (59 : ZMod 129393864601) ^ 1101) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 10110753240 := by rw [factor_3_10]; decide
      have factor_3_12 : (59 : ZMod 129393864601) ^ 4407 = 90566507784 := by
        calc
          (59 : ZMod 129393864601) ^ 4407 = (59 : ZMod 129393864601) ^ (2203 + 2203 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2203 * (59 : ZMod 129393864601) ^ 2203) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 90566507784 := by rw [factor_3_11]; decide
      have factor_3_13 : (59 : ZMod 129393864601) ^ 8814 = 112881591160 := by
        calc
          (59 : ZMod 129393864601) ^ 8814 = (59 : ZMod 129393864601) ^ (4407 + 4407) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 4407 * (59 : ZMod 129393864601) ^ 4407 := by rw [pow_add]
          _ = 112881591160 := by rw [factor_3_12]; decide
      have factor_3_14 : (59 : ZMod 129393864601) ^ 17628 = 55301404328 := by
        calc
          (59 : ZMod 129393864601) ^ 17628 = (59 : ZMod 129393864601) ^ (8814 + 8814) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 8814 * (59 : ZMod 129393864601) ^ 8814 := by rw [pow_add]
          _ = 55301404328 := by rw [factor_3_13]; decide
      have factor_3_15 : (59 : ZMod 129393864601) ^ 35257 = 119462558004 := by
        calc
          (59 : ZMod 129393864601) ^ 35257 = (59 : ZMod 129393864601) ^ (17628 + 17628 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 17628 * (59 : ZMod 129393864601) ^ 17628) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 119462558004 := by rw [factor_3_14]; decide
      have factor_3_16 : (59 : ZMod 129393864601) ^ 70514 = 118994293893 := by
        calc
          (59 : ZMod 129393864601) ^ 70514 = (59 : ZMod 129393864601) ^ (35257 + 35257) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 35257 * (59 : ZMod 129393864601) ^ 35257 := by rw [pow_add]
          _ = 118994293893 := by rw [factor_3_15]; decide
      have factor_3_17 : (59 : ZMod 129393864601) ^ 141028 = 80211350233 := by
        calc
          (59 : ZMod 129393864601) ^ 141028 = (59 : ZMod 129393864601) ^ (70514 + 70514) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 70514 * (59 : ZMod 129393864601) ^ 70514 := by rw [pow_add]
          _ = 80211350233 := by rw [factor_3_16]; decide
      have factor_3_18 : (59 : ZMod 129393864601) ^ 282056 = 76153169678 := by
        calc
          (59 : ZMod 129393864601) ^ 282056 = (59 : ZMod 129393864601) ^ (141028 + 141028) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 141028 * (59 : ZMod 129393864601) ^ 141028 := by rw [pow_add]
          _ = 76153169678 := by rw [factor_3_17]; decide
      have factor_3_19 : (59 : ZMod 129393864601) ^ 564112 = 80135848453 := by
        calc
          (59 : ZMod 129393864601) ^ 564112 = (59 : ZMod 129393864601) ^ (282056 + 282056) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 282056 * (59 : ZMod 129393864601) ^ 282056 := by rw [pow_add]
          _ = 80135848453 := by rw [factor_3_18]; decide
      have factor_3_20 : (59 : ZMod 129393864601) ^ 1128224 = 14028207758 := by
        calc
          (59 : ZMod 129393864601) ^ 1128224 = (59 : ZMod 129393864601) ^ (564112 + 564112) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 564112 * (59 : ZMod 129393864601) ^ 564112 := by rw [pow_add]
          _ = 14028207758 := by rw [factor_3_19]; decide
      have factor_3_21 : (59 : ZMod 129393864601) ^ 2256449 = 74287229942 := by
        calc
          (59 : ZMod 129393864601) ^ 2256449 = (59 : ZMod 129393864601) ^ (1128224 + 1128224 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1128224 * (59 : ZMod 129393864601) ^ 1128224) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 74287229942 := by rw [factor_3_20]; decide
      have factor_3_22 : (59 : ZMod 129393864601) ^ 4512899 = 116279746830 := by
        calc
          (59 : ZMod 129393864601) ^ 4512899 = (59 : ZMod 129393864601) ^ (2256449 + 2256449 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2256449 * (59 : ZMod 129393864601) ^ 2256449) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 116279746830 := by rw [factor_3_21]; decide
      have factor_3_23 : (59 : ZMod 129393864601) ^ 9025799 = 49423925336 := by
        calc
          (59 : ZMod 129393864601) ^ 9025799 = (59 : ZMod 129393864601) ^ (4512899 + 4512899 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 4512899 * (59 : ZMod 129393864601) ^ 4512899) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 49423925336 := by rw [factor_3_22]; decide
      have factor_3_24 : (59 : ZMod 129393864601) ^ 18051599 = 31335799442 := by
        calc
          (59 : ZMod 129393864601) ^ 18051599 = (59 : ZMod 129393864601) ^ (9025799 + 9025799 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 9025799 * (59 : ZMod 129393864601) ^ 9025799) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 31335799442 := by rw [factor_3_23]; decide
      have factor_3_25 : (59 : ZMod 129393864601) ^ 36103198 = 54096472814 := by
        calc
          (59 : ZMod 129393864601) ^ 36103198 = (59 : ZMod 129393864601) ^ (18051599 + 18051599) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 18051599 * (59 : ZMod 129393864601) ^ 18051599 := by rw [pow_add]
          _ = 54096472814 := by rw [factor_3_24]; decide
      have factor_3_26 : (59 : ZMod 129393864601) ^ 72206397 = 15570676274 := by
        calc
          (59 : ZMod 129393864601) ^ 72206397 = (59 : ZMod 129393864601) ^ (36103198 + 36103198 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 36103198 * (59 : ZMod 129393864601) ^ 36103198) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 15570676274 := by rw [factor_3_25]; decide
      have factor_3_27 : (59 : ZMod 129393864601) ^ 144412795 = 54388296863 := by
        calc
          (59 : ZMod 129393864601) ^ 144412795 = (59 : ZMod 129393864601) ^ (72206397 + 72206397 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 72206397 * (59 : ZMod 129393864601) ^ 72206397) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 54388296863 := by rw [factor_3_26]; decide
      have factor_3_28 : (59 : ZMod 129393864601) ^ 288825590 = 26817301914 := by
        calc
          (59 : ZMod 129393864601) ^ 288825590 = (59 : ZMod 129393864601) ^ (144412795 + 144412795) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 144412795 * (59 : ZMod 129393864601) ^ 144412795 := by rw [pow_add]
          _ = 26817301914 := by rw [factor_3_27]; decide
      have factor_3_29 : (59 : ZMod 129393864601) ^ 577651181 = 68415103452 := by
        calc
          (59 : ZMod 129393864601) ^ 577651181 = (59 : ZMod 129393864601) ^ (288825590 + 288825590 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 288825590 * (59 : ZMod 129393864601) ^ 288825590) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 68415103452 := by rw [factor_3_28]; decide
      have factor_3_30 : (59 : ZMod 129393864601) ^ 1155302362 = 93612147850 := by
        calc
          (59 : ZMod 129393864601) ^ 1155302362 = (59 : ZMod 129393864601) ^ (577651181 + 577651181) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 577651181 * (59 : ZMod 129393864601) ^ 577651181 := by rw [pow_add]
          _ = 93612147850 := by rw [factor_3_29]; decide
      have factor_3_31 : (59 : ZMod 129393864601) ^ 2310604725 = 4316828553 := by
        calc
          (59 : ZMod 129393864601) ^ 2310604725 = (59 : ZMod 129393864601) ^ (1155302362 + 1155302362 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1155302362 * (59 : ZMod 129393864601) ^ 1155302362) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 4316828553 := by rw [factor_3_30]; decide
      have factor_3_32 : (59 : ZMod 129393864601) ^ 4621209450 = 41140667094 := by
        calc
          (59 : ZMod 129393864601) ^ 4621209450 = (59 : ZMod 129393864601) ^ (2310604725 + 2310604725) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2310604725 * (59 : ZMod 129393864601) ^ 2310604725 := by rw [pow_add]
          _ = 41140667094 := by rw [factor_3_31]; decide
      have factor_3_33 : (59 : ZMod 129393864601) ^ 9242418900 = 86686212194 := by
        calc
          (59 : ZMod 129393864601) ^ 9242418900 = (59 : ZMod 129393864601) ^ (4621209450 + 4621209450) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 4621209450 * (59 : ZMod 129393864601) ^ 4621209450 := by rw [pow_add]
          _ = 86686212194 := by rw [factor_3_32]; decide
      have factor_3_34 : (59 : ZMod 129393864601) ^ 18484837800 = 7985025060 := by
        calc
          (59 : ZMod 129393864601) ^ 18484837800 = (59 : ZMod 129393864601) ^ (9242418900 + 9242418900) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 9242418900 * (59 : ZMod 129393864601) ^ 9242418900 := by rw [pow_add]
          _ = 7985025060 := by rw [factor_3_33]; decide
      change (59 : ZMod 129393864601) ^ 18484837800 ≠ 1
      rw [factor_3_34]
      decide
    ·
      have factor_4_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_4_1 : (59 : ZMod 129393864601) ^ 2 = 3481 := by
        calc
          (59 : ZMod 129393864601) ^ 2 = (59 : ZMod 129393864601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1 := by rw [pow_add]
          _ = 3481 := by rw [factor_4_0]; decide
      have factor_4_2 : (59 : ZMod 129393864601) ^ 5 = 714924299 := by
        calc
          (59 : ZMod 129393864601) ^ 5 = (59 : ZMod 129393864601) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2 * (59 : ZMod 129393864601) ^ 2) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 714924299 := by rw [factor_4_1]; decide
      have factor_4_3 : (59 : ZMod 129393864601) ^ 10 = 119042064917 := by
        calc
          (59 : ZMod 129393864601) ^ 10 = (59 : ZMod 129393864601) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 5 * (59 : ZMod 129393864601) ^ 5 := by rw [pow_add]
          _ = 119042064917 := by rw [factor_4_2]; decide
      have factor_4_4 : (59 : ZMod 129393864601) ^ 21 = 13744508522 := by
        calc
          (59 : ZMod 129393864601) ^ 21 = (59 : ZMod 129393864601) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 10 * (59 : ZMod 129393864601) ^ 10) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 13744508522 := by rw [factor_4_3]; decide
      have factor_4_5 : (59 : ZMod 129393864601) ^ 43 = 79874450338 := by
        calc
          (59 : ZMod 129393864601) ^ 43 = (59 : ZMod 129393864601) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 21 * (59 : ZMod 129393864601) ^ 21) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 79874450338 := by rw [factor_4_4]; decide
      have factor_4_6 : (59 : ZMod 129393864601) ^ 87 = 58191466417 := by
        calc
          (59 : ZMod 129393864601) ^ 87 = (59 : ZMod 129393864601) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 43 * (59 : ZMod 129393864601) ^ 43) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 58191466417 := by rw [factor_4_5]; decide
      have factor_4_7 : (59 : ZMod 129393864601) ^ 175 = 123427505930 := by
        calc
          (59 : ZMod 129393864601) ^ 175 = (59 : ZMod 129393864601) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 87 * (59 : ZMod 129393864601) ^ 87) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 123427505930 := by rw [factor_4_6]; decide
      have factor_4_8 : (59 : ZMod 129393864601) ^ 350 = 73602280894 := by
        calc
          (59 : ZMod 129393864601) ^ 350 = (59 : ZMod 129393864601) ^ (175 + 175) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 175 * (59 : ZMod 129393864601) ^ 175 := by rw [pow_add]
          _ = 73602280894 := by rw [factor_4_7]; decide
      have factor_4_9 : (59 : ZMod 129393864601) ^ 701 = 53447650551 := by
        calc
          (59 : ZMod 129393864601) ^ 701 = (59 : ZMod 129393864601) ^ (350 + 350 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 350 * (59 : ZMod 129393864601) ^ 350) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 53447650551 := by rw [factor_4_8]; decide
      have factor_4_10 : (59 : ZMod 129393864601) ^ 1402 = 89737588245 := by
        calc
          (59 : ZMod 129393864601) ^ 1402 = (59 : ZMod 129393864601) ^ (701 + 701) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 701 * (59 : ZMod 129393864601) ^ 701 := by rw [pow_add]
          _ = 89737588245 := by rw [factor_4_9]; decide
      have factor_4_11 : (59 : ZMod 129393864601) ^ 2804 = 46369530440 := by
        calc
          (59 : ZMod 129393864601) ^ 2804 = (59 : ZMod 129393864601) ^ (1402 + 1402) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1402 * (59 : ZMod 129393864601) ^ 1402 := by rw [pow_add]
          _ = 46369530440 := by rw [factor_4_10]; decide
      have factor_4_12 : (59 : ZMod 129393864601) ^ 5609 = 14646251526 := by
        calc
          (59 : ZMod 129393864601) ^ 5609 = (59 : ZMod 129393864601) ^ (2804 + 2804 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2804 * (59 : ZMod 129393864601) ^ 2804) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 14646251526 := by rw [factor_4_11]; decide
      have factor_4_13 : (59 : ZMod 129393864601) ^ 11218 = 116332493957 := by
        calc
          (59 : ZMod 129393864601) ^ 11218 = (59 : ZMod 129393864601) ^ (5609 + 5609) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 5609 * (59 : ZMod 129393864601) ^ 5609 := by rw [pow_add]
          _ = 116332493957 := by rw [factor_4_12]; decide
      have factor_4_14 : (59 : ZMod 129393864601) ^ 22436 = 78307651655 := by
        calc
          (59 : ZMod 129393864601) ^ 22436 = (59 : ZMod 129393864601) ^ (11218 + 11218) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 11218 * (59 : ZMod 129393864601) ^ 11218 := by rw [pow_add]
          _ = 78307651655 := by rw [factor_4_13]; decide
      have factor_4_15 : (59 : ZMod 129393864601) ^ 44872 = 49939749826 := by
        calc
          (59 : ZMod 129393864601) ^ 44872 = (59 : ZMod 129393864601) ^ (22436 + 22436) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 22436 * (59 : ZMod 129393864601) ^ 22436 := by rw [pow_add]
          _ = 49939749826 := by rw [factor_4_14]; decide
      have factor_4_16 : (59 : ZMod 129393864601) ^ 89745 = 7176750171 := by
        calc
          (59 : ZMod 129393864601) ^ 89745 = (59 : ZMod 129393864601) ^ (44872 + 44872 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 44872 * (59 : ZMod 129393864601) ^ 44872) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 7176750171 := by rw [factor_4_15]; decide
      have factor_4_17 : (59 : ZMod 129393864601) ^ 179490 = 95545502660 := by
        calc
          (59 : ZMod 129393864601) ^ 179490 = (59 : ZMod 129393864601) ^ (89745 + 89745) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 89745 * (59 : ZMod 129393864601) ^ 89745 := by rw [pow_add]
          _ = 95545502660 := by rw [factor_4_16]; decide
      have factor_4_18 : (59 : ZMod 129393864601) ^ 358980 = 98429125696 := by
        calc
          (59 : ZMod 129393864601) ^ 358980 = (59 : ZMod 129393864601) ^ (179490 + 179490) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 179490 * (59 : ZMod 129393864601) ^ 179490 := by rw [pow_add]
          _ = 98429125696 := by rw [factor_4_17]; decide
      have factor_4_19 : (59 : ZMod 129393864601) ^ 717961 = 93719674302 := by
        calc
          (59 : ZMod 129393864601) ^ 717961 = (59 : ZMod 129393864601) ^ (358980 + 358980 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 358980 * (59 : ZMod 129393864601) ^ 358980) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 93719674302 := by rw [factor_4_18]; decide
      have factor_4_20 : (59 : ZMod 129393864601) ^ 1435922 = 33253043921 := by
        calc
          (59 : ZMod 129393864601) ^ 1435922 = (59 : ZMod 129393864601) ^ (717961 + 717961) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 717961 * (59 : ZMod 129393864601) ^ 717961 := by rw [pow_add]
          _ = 33253043921 := by rw [factor_4_19]; decide
      have factor_4_21 : (59 : ZMod 129393864601) ^ 2871845 = 66399846256 := by
        calc
          (59 : ZMod 129393864601) ^ 2871845 = (59 : ZMod 129393864601) ^ (1435922 + 1435922 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1435922 * (59 : ZMod 129393864601) ^ 1435922) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 66399846256 := by rw [factor_4_20]; decide
      have factor_4_22 : (59 : ZMod 129393864601) ^ 5743690 = 5834429689 := by
        calc
          (59 : ZMod 129393864601) ^ 5743690 = (59 : ZMod 129393864601) ^ (2871845 + 2871845) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2871845 * (59 : ZMod 129393864601) ^ 2871845 := by rw [pow_add]
          _ = 5834429689 := by rw [factor_4_21]; decide
      have factor_4_23 : (59 : ZMod 129393864601) ^ 11487381 = 15763801384 := by
        calc
          (59 : ZMod 129393864601) ^ 11487381 = (59 : ZMod 129393864601) ^ (5743690 + 5743690 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 5743690 * (59 : ZMod 129393864601) ^ 5743690) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 15763801384 := by rw [factor_4_22]; decide
      have factor_4_24 : (59 : ZMod 129393864601) ^ 22974762 = 2633280573 := by
        calc
          (59 : ZMod 129393864601) ^ 22974762 = (59 : ZMod 129393864601) ^ (11487381 + 11487381) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 11487381 * (59 : ZMod 129393864601) ^ 11487381 := by rw [pow_add]
          _ = 2633280573 := by rw [factor_4_23]; decide
      have factor_4_25 : (59 : ZMod 129393864601) ^ 45949525 = 15489795496 := by
        calc
          (59 : ZMod 129393864601) ^ 45949525 = (59 : ZMod 129393864601) ^ (22974762 + 22974762 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 22974762 * (59 : ZMod 129393864601) ^ 22974762) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 15489795496 := by rw [factor_4_24]; decide
      have factor_4_26 : (59 : ZMod 129393864601) ^ 91899051 = 11151791560 := by
        calc
          (59 : ZMod 129393864601) ^ 91899051 = (59 : ZMod 129393864601) ^ (45949525 + 45949525 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 45949525 * (59 : ZMod 129393864601) ^ 45949525) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 11151791560 := by rw [factor_4_25]; decide
      have factor_4_27 : (59 : ZMod 129393864601) ^ 183798103 = 93454301908 := by
        calc
          (59 : ZMod 129393864601) ^ 183798103 = (59 : ZMod 129393864601) ^ (91899051 + 91899051 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 91899051 * (59 : ZMod 129393864601) ^ 91899051) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 93454301908 := by rw [factor_4_26]; decide
      have factor_4_28 : (59 : ZMod 129393864601) ^ 367596206 = 70312979944 := by
        calc
          (59 : ZMod 129393864601) ^ 367596206 = (59 : ZMod 129393864601) ^ (183798103 + 183798103) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 183798103 * (59 : ZMod 129393864601) ^ 183798103 := by rw [pow_add]
          _ = 70312979944 := by rw [factor_4_27]; decide
      have factor_4_29 : (59 : ZMod 129393864601) ^ 735192412 = 73235196314 := by
        calc
          (59 : ZMod 129393864601) ^ 735192412 = (59 : ZMod 129393864601) ^ (367596206 + 367596206) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 367596206 * (59 : ZMod 129393864601) ^ 367596206 := by rw [pow_add]
          _ = 73235196314 := by rw [factor_4_28]; decide
      have factor_4_30 : (59 : ZMod 129393864601) ^ 1470384825 = 104677933178 := by
        calc
          (59 : ZMod 129393864601) ^ 1470384825 = (59 : ZMod 129393864601) ^ (735192412 + 735192412 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 735192412 * (59 : ZMod 129393864601) ^ 735192412) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 104677933178 := by rw [factor_4_29]; decide
      have factor_4_31 : (59 : ZMod 129393864601) ^ 2940769650 = 64464922078 := by
        calc
          (59 : ZMod 129393864601) ^ 2940769650 = (59 : ZMod 129393864601) ^ (1470384825 + 1470384825) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1470384825 * (59 : ZMod 129393864601) ^ 1470384825 := by rw [pow_add]
          _ = 64464922078 := by rw [factor_4_30]; decide
      have factor_4_32 : (59 : ZMod 129393864601) ^ 5881539300 = 86958829750 := by
        calc
          (59 : ZMod 129393864601) ^ 5881539300 = (59 : ZMod 129393864601) ^ (2940769650 + 2940769650) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2940769650 * (59 : ZMod 129393864601) ^ 2940769650 := by rw [pow_add]
          _ = 86958829750 := by rw [factor_4_31]; decide
      have factor_4_33 : (59 : ZMod 129393864601) ^ 11763078600 = 76026743576 := by
        calc
          (59 : ZMod 129393864601) ^ 11763078600 = (59 : ZMod 129393864601) ^ (5881539300 + 5881539300) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 5881539300 * (59 : ZMod 129393864601) ^ 5881539300 := by rw [pow_add]
          _ = 76026743576 := by rw [factor_4_32]; decide
      change (59 : ZMod 129393864601) ^ 11763078600 ≠ 1
      rw [factor_4_33]
      decide
    ·
      have factor_5_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_5_1 : (59 : ZMod 129393864601) ^ 2 = 3481 := by
        calc
          (59 : ZMod 129393864601) ^ 2 = (59 : ZMod 129393864601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1 := by rw [pow_add]
          _ = 3481 := by rw [factor_5_0]; decide
      have factor_5_2 : (59 : ZMod 129393864601) ^ 4 = 12117361 := by
        calc
          (59 : ZMod 129393864601) ^ 4 = (59 : ZMod 129393864601) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2 * (59 : ZMod 129393864601) ^ 2 := by rw [pow_add]
          _ = 12117361 := by rw [factor_5_1]; decide
      have factor_5_3 : (59 : ZMod 129393864601) ^ 9 = 76583617989 := by
        calc
          (59 : ZMod 129393864601) ^ 9 = (59 : ZMod 129393864601) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 4 * (59 : ZMod 129393864601) ^ 4) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 76583617989 := by rw [factor_5_2]; decide
      have factor_5_4 : (59 : ZMod 129393864601) ^ 18 = 98379700406 := by
        calc
          (59 : ZMod 129393864601) ^ 18 = (59 : ZMod 129393864601) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 9 * (59 : ZMod 129393864601) ^ 9 := by rw [pow_add]
          _ = 98379700406 := by rw [factor_5_3]; decide
      have factor_5_5 : (59 : ZMod 129393864601) ^ 37 = 92615834065 := by
        calc
          (59 : ZMod 129393864601) ^ 37 = (59 : ZMod 129393864601) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 18 * (59 : ZMod 129393864601) ^ 18) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 92615834065 := by rw [factor_5_4]; decide
      have factor_5_6 : (59 : ZMod 129393864601) ^ 74 = 18604640259 := by
        calc
          (59 : ZMod 129393864601) ^ 74 = (59 : ZMod 129393864601) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 37 * (59 : ZMod 129393864601) ^ 37 := by rw [pow_add]
          _ = 18604640259 := by rw [factor_5_5]; decide
      have factor_5_7 : (59 : ZMod 129393864601) ^ 148 = 37227929771 := by
        calc
          (59 : ZMod 129393864601) ^ 148 = (59 : ZMod 129393864601) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 74 * (59 : ZMod 129393864601) ^ 74 := by rw [pow_add]
          _ = 37227929771 := by rw [factor_5_6]; decide
      have factor_5_8 : (59 : ZMod 129393864601) ^ 296 = 62861863529 := by
        calc
          (59 : ZMod 129393864601) ^ 296 = (59 : ZMod 129393864601) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 148 * (59 : ZMod 129393864601) ^ 148 := by rw [pow_add]
          _ = 62861863529 := by rw [factor_5_7]; decide
      have factor_5_9 : (59 : ZMod 129393864601) ^ 593 = 8256441329 := by
        calc
          (59 : ZMod 129393864601) ^ 593 = (59 : ZMod 129393864601) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 296 * (59 : ZMod 129393864601) ^ 296) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 8256441329 := by rw [factor_5_8]; decide
      have factor_5_10 : (59 : ZMod 129393864601) ^ 1186 = 119499838281 := by
        calc
          (59 : ZMod 129393864601) ^ 1186 = (59 : ZMod 129393864601) ^ (593 + 593) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 593 * (59 : ZMod 129393864601) ^ 593 := by rw [pow_add]
          _ = 119499838281 := by rw [factor_5_9]; decide
      have factor_5_11 : (59 : ZMod 129393864601) ^ 2373 = 76206517346 := by
        calc
          (59 : ZMod 129393864601) ^ 2373 = (59 : ZMod 129393864601) ^ (1186 + 1186 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1186 * (59 : ZMod 129393864601) ^ 1186) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 76206517346 := by rw [factor_5_10]; decide
      have factor_5_12 : (59 : ZMod 129393864601) ^ 4746 = 97074021861 := by
        calc
          (59 : ZMod 129393864601) ^ 4746 = (59 : ZMod 129393864601) ^ (2373 + 2373) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2373 * (59 : ZMod 129393864601) ^ 2373 := by rw [pow_add]
          _ = 97074021861 := by rw [factor_5_11]; decide
      have factor_5_13 : (59 : ZMod 129393864601) ^ 9492 = 34273502036 := by
        calc
          (59 : ZMod 129393864601) ^ 9492 = (59 : ZMod 129393864601) ^ (4746 + 4746) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 4746 * (59 : ZMod 129393864601) ^ 4746 := by rw [pow_add]
          _ = 34273502036 := by rw [factor_5_12]; decide
      have factor_5_14 : (59 : ZMod 129393864601) ^ 18984 = 54605765012 := by
        calc
          (59 : ZMod 129393864601) ^ 18984 = (59 : ZMod 129393864601) ^ (9492 + 9492) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 9492 * (59 : ZMod 129393864601) ^ 9492 := by rw [pow_add]
          _ = 54605765012 := by rw [factor_5_13]; decide
      have factor_5_15 : (59 : ZMod 129393864601) ^ 37969 = 30411467290 := by
        calc
          (59 : ZMod 129393864601) ^ 37969 = (59 : ZMod 129393864601) ^ (18984 + 18984 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 18984 * (59 : ZMod 129393864601) ^ 18984) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 30411467290 := by rw [factor_5_14]; decide
      have factor_5_16 : (59 : ZMod 129393864601) ^ 75938 = 104495843929 := by
        calc
          (59 : ZMod 129393864601) ^ 75938 = (59 : ZMod 129393864601) ^ (37969 + 37969) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 37969 * (59 : ZMod 129393864601) ^ 37969 := by rw [pow_add]
          _ = 104495843929 := by rw [factor_5_15]; decide
      have factor_5_17 : (59 : ZMod 129393864601) ^ 151876 = 28798102401 := by
        calc
          (59 : ZMod 129393864601) ^ 151876 = (59 : ZMod 129393864601) ^ (75938 + 75938) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 75938 * (59 : ZMod 129393864601) ^ 75938 := by rw [pow_add]
          _ = 28798102401 := by rw [factor_5_16]; decide
      have factor_5_18 : (59 : ZMod 129393864601) ^ 303752 = 83898648352 := by
        calc
          (59 : ZMod 129393864601) ^ 303752 = (59 : ZMod 129393864601) ^ (151876 + 151876) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 151876 * (59 : ZMod 129393864601) ^ 151876 := by rw [pow_add]
          _ = 83898648352 := by rw [factor_5_17]; decide
      have factor_5_19 : (59 : ZMod 129393864601) ^ 607505 = 44115183123 := by
        calc
          (59 : ZMod 129393864601) ^ 607505 = (59 : ZMod 129393864601) ^ (303752 + 303752 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 303752 * (59 : ZMod 129393864601) ^ 303752) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 44115183123 := by rw [factor_5_18]; decide
      have factor_5_20 : (59 : ZMod 129393864601) ^ 1215011 = 118832157620 := by
        calc
          (59 : ZMod 129393864601) ^ 1215011 = (59 : ZMod 129393864601) ^ (607505 + 607505 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 607505 * (59 : ZMod 129393864601) ^ 607505) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 118832157620 := by rw [factor_5_19]; decide
      have factor_5_21 : (59 : ZMod 129393864601) ^ 2430022 = 99218653516 := by
        calc
          (59 : ZMod 129393864601) ^ 2430022 = (59 : ZMod 129393864601) ^ (1215011 + 1215011) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1215011 * (59 : ZMod 129393864601) ^ 1215011 := by rw [pow_add]
          _ = 99218653516 := by rw [factor_5_20]; decide
      have factor_5_22 : (59 : ZMod 129393864601) ^ 4860045 = 32900207335 := by
        calc
          (59 : ZMod 129393864601) ^ 4860045 = (59 : ZMod 129393864601) ^ (2430022 + 2430022 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2430022 * (59 : ZMod 129393864601) ^ 2430022) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 32900207335 := by rw [factor_5_21]; decide
      have factor_5_23 : (59 : ZMod 129393864601) ^ 9720091 = 25994585123 := by
        calc
          (59 : ZMod 129393864601) ^ 9720091 = (59 : ZMod 129393864601) ^ (4860045 + 4860045 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 4860045 * (59 : ZMod 129393864601) ^ 4860045) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 25994585123 := by rw [factor_5_22]; decide
      have factor_5_24 : (59 : ZMod 129393864601) ^ 19440183 = 88586365456 := by
        calc
          (59 : ZMod 129393864601) ^ 19440183 = (59 : ZMod 129393864601) ^ (9720091 + 9720091 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 9720091 * (59 : ZMod 129393864601) ^ 9720091) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 88586365456 := by rw [factor_5_23]; decide
      have factor_5_25 : (59 : ZMod 129393864601) ^ 38880367 = 82466545597 := by
        calc
          (59 : ZMod 129393864601) ^ 38880367 = (59 : ZMod 129393864601) ^ (19440183 + 19440183 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 19440183 * (59 : ZMod 129393864601) ^ 19440183) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 82466545597 := by rw [factor_5_24]; decide
      have factor_5_26 : (59 : ZMod 129393864601) ^ 77760735 = 79632998886 := by
        calc
          (59 : ZMod 129393864601) ^ 77760735 = (59 : ZMod 129393864601) ^ (38880367 + 38880367 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 38880367 * (59 : ZMod 129393864601) ^ 38880367) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 79632998886 := by rw [factor_5_25]; decide
      have factor_5_27 : (59 : ZMod 129393864601) ^ 155521471 = 75977493775 := by
        calc
          (59 : ZMod 129393864601) ^ 155521471 = (59 : ZMod 129393864601) ^ (77760735 + 77760735 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 77760735 * (59 : ZMod 129393864601) ^ 77760735) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 75977493775 := by rw [factor_5_26]; decide
      have factor_5_28 : (59 : ZMod 129393864601) ^ 311042943 = 81570418985 := by
        calc
          (59 : ZMod 129393864601) ^ 311042943 = (59 : ZMod 129393864601) ^ (155521471 + 155521471 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 155521471 * (59 : ZMod 129393864601) ^ 155521471) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 81570418985 := by rw [factor_5_27]; decide
      have factor_5_29 : (59 : ZMod 129393864601) ^ 622085887 = 73722586412 := by
        calc
          (59 : ZMod 129393864601) ^ 622085887 = (59 : ZMod 129393864601) ^ (311042943 + 311042943 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 311042943 * (59 : ZMod 129393864601) ^ 311042943) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 73722586412 := by rw [factor_5_28]; decide
      have factor_5_30 : (59 : ZMod 129393864601) ^ 1244171775 = 57482590069 := by
        calc
          (59 : ZMod 129393864601) ^ 1244171775 = (59 : ZMod 129393864601) ^ (622085887 + 622085887 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 622085887 * (59 : ZMod 129393864601) ^ 622085887) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 57482590069 := by rw [factor_5_29]; decide
      have factor_5_31 : (59 : ZMod 129393864601) ^ 2488343550 = 48522980699 := by
        calc
          (59 : ZMod 129393864601) ^ 2488343550 = (59 : ZMod 129393864601) ^ (1244171775 + 1244171775) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1244171775 * (59 : ZMod 129393864601) ^ 1244171775 := by rw [pow_add]
          _ = 48522980699 := by rw [factor_5_30]; decide
      have factor_5_32 : (59 : ZMod 129393864601) ^ 4976687100 = 44857156286 := by
        calc
          (59 : ZMod 129393864601) ^ 4976687100 = (59 : ZMod 129393864601) ^ (2488343550 + 2488343550) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2488343550 * (59 : ZMod 129393864601) ^ 2488343550 := by rw [pow_add]
          _ = 44857156286 := by rw [factor_5_31]; decide
      have factor_5_33 : (59 : ZMod 129393864601) ^ 9953374200 = 95453834408 := by
        calc
          (59 : ZMod 129393864601) ^ 9953374200 = (59 : ZMod 129393864601) ^ (4976687100 + 4976687100) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 4976687100 * (59 : ZMod 129393864601) ^ 4976687100 := by rw [pow_add]
          _ = 95453834408 := by rw [factor_5_32]; decide
      change (59 : ZMod 129393864601) ^ 9953374200 ≠ 1
      rw [factor_5_33]
      decide
    ·
      have factor_6_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_6_1 : (59 : ZMod 129393864601) ^ 3 = 205379 := by
        calc
          (59 : ZMod 129393864601) ^ 3 = (59 : ZMod 129393864601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 205379 := by rw [factor_6_0]; decide
      have factor_6_2 : (59 : ZMod 129393864601) ^ 7 = 30168057400 := by
        calc
          (59 : ZMod 129393864601) ^ 7 = (59 : ZMod 129393864601) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 3 * (59 : ZMod 129393864601) ^ 3) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 30168057400 := by rw [factor_6_1]; decide
      have factor_6_3 : (59 : ZMod 129393864601) ^ 14 = 118269193693 := by
        calc
          (59 : ZMod 129393864601) ^ 14 = (59 : ZMod 129393864601) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 7 * (59 : ZMod 129393864601) ^ 7 := by rw [pow_add]
          _ = 118269193693 := by rw [factor_6_2]; decide
      have factor_6_4 : (59 : ZMod 129393864601) ^ 28 = 103106698812 := by
        calc
          (59 : ZMod 129393864601) ^ 28 = (59 : ZMod 129393864601) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 14 * (59 : ZMod 129393864601) ^ 14 := by rw [pow_add]
          _ = 103106698812 := by rw [factor_6_3]; decide
      have factor_6_5 : (59 : ZMod 129393864601) ^ 56 = 127486371821 := by
        calc
          (59 : ZMod 129393864601) ^ 56 = (59 : ZMod 129393864601) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 28 * (59 : ZMod 129393864601) ^ 28 := by rw [pow_add]
          _ = 127486371821 := by rw [factor_6_4]; decide
      have factor_6_6 : (59 : ZMod 129393864601) ^ 113 = 9265950805 := by
        calc
          (59 : ZMod 129393864601) ^ 113 = (59 : ZMod 129393864601) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 56 * (59 : ZMod 129393864601) ^ 56) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 9265950805 := by rw [factor_6_5]; decide
      have factor_6_7 : (59 : ZMod 129393864601) ^ 226 = 110512442467 := by
        calc
          (59 : ZMod 129393864601) ^ 226 = (59 : ZMod 129393864601) ^ (113 + 113) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 113 * (59 : ZMod 129393864601) ^ 113 := by rw [pow_add]
          _ = 110512442467 := by rw [factor_6_6]; decide
      have factor_6_8 : (59 : ZMod 129393864601) ^ 453 = 34549557383 := by
        calc
          (59 : ZMod 129393864601) ^ 453 = (59 : ZMod 129393864601) ^ (226 + 226 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 226 * (59 : ZMod 129393864601) ^ 226) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 34549557383 := by rw [factor_6_7]; decide
      have factor_6_9 : (59 : ZMod 129393864601) ^ 907 = 117841024254 := by
        calc
          (59 : ZMod 129393864601) ^ 907 = (59 : ZMod 129393864601) ^ (453 + 453 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 453 * (59 : ZMod 129393864601) ^ 453) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 117841024254 := by rw [factor_6_8]; decide
      have factor_6_10 : (59 : ZMod 129393864601) ^ 1814 = 71839618371 := by
        calc
          (59 : ZMod 129393864601) ^ 1814 = (59 : ZMod 129393864601) ^ (907 + 907) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 907 * (59 : ZMod 129393864601) ^ 907 := by rw [pow_add]
          _ = 71839618371 := by rw [factor_6_9]; decide
      have factor_6_11 : (59 : ZMod 129393864601) ^ 3629 = 22751465187 := by
        calc
          (59 : ZMod 129393864601) ^ 3629 = (59 : ZMod 129393864601) ^ (1814 + 1814 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1814 * (59 : ZMod 129393864601) ^ 1814) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 22751465187 := by rw [factor_6_10]; decide
      have factor_6_12 : (59 : ZMod 129393864601) ^ 7258 = 40197309682 := by
        calc
          (59 : ZMod 129393864601) ^ 7258 = (59 : ZMod 129393864601) ^ (3629 + 3629) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3629 * (59 : ZMod 129393864601) ^ 3629 := by rw [pow_add]
          _ = 40197309682 := by rw [factor_6_11]; decide
      have factor_6_13 : (59 : ZMod 129393864601) ^ 14517 = 23799757024 := by
        calc
          (59 : ZMod 129393864601) ^ 14517 = (59 : ZMod 129393864601) ^ (7258 + 7258 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 7258 * (59 : ZMod 129393864601) ^ 7258) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 23799757024 := by rw [factor_6_12]; decide
      have factor_6_14 : (59 : ZMod 129393864601) ^ 29035 = 42240821171 := by
        calc
          (59 : ZMod 129393864601) ^ 29035 = (59 : ZMod 129393864601) ^ (14517 + 14517 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 14517 * (59 : ZMod 129393864601) ^ 14517) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 42240821171 := by rw [factor_6_13]; decide
      have factor_6_15 : (59 : ZMod 129393864601) ^ 58070 = 47822512215 := by
        calc
          (59 : ZMod 129393864601) ^ 58070 = (59 : ZMod 129393864601) ^ (29035 + 29035) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 29035 * (59 : ZMod 129393864601) ^ 29035 := by rw [pow_add]
          _ = 47822512215 := by rw [factor_6_14]; decide
      have factor_6_16 : (59 : ZMod 129393864601) ^ 116140 = 107602260163 := by
        calc
          (59 : ZMod 129393864601) ^ 116140 = (59 : ZMod 129393864601) ^ (58070 + 58070) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 58070 * (59 : ZMod 129393864601) ^ 58070 := by rw [pow_add]
          _ = 107602260163 := by rw [factor_6_15]; decide
      have factor_6_17 : (59 : ZMod 129393864601) ^ 232281 = 60338010707 := by
        calc
          (59 : ZMod 129393864601) ^ 232281 = (59 : ZMod 129393864601) ^ (116140 + 116140 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 116140 * (59 : ZMod 129393864601) ^ 116140) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 60338010707 := by rw [factor_6_16]; decide
      have factor_6_18 : (59 : ZMod 129393864601) ^ 464563 = 75919989358 := by
        calc
          (59 : ZMod 129393864601) ^ 464563 = (59 : ZMod 129393864601) ^ (232281 + 232281 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 232281 * (59 : ZMod 129393864601) ^ 232281) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 75919989358 := by rw [factor_6_17]; decide
      have factor_6_19 : (59 : ZMod 129393864601) ^ 929126 = 105053527346 := by
        calc
          (59 : ZMod 129393864601) ^ 929126 = (59 : ZMod 129393864601) ^ (464563 + 464563) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 464563 * (59 : ZMod 129393864601) ^ 464563 := by rw [pow_add]
          _ = 105053527346 := by rw [factor_6_18]; decide
      have factor_6_20 : (59 : ZMod 129393864601) ^ 1858252 = 95511642390 := by
        calc
          (59 : ZMod 129393864601) ^ 1858252 = (59 : ZMod 129393864601) ^ (929126 + 929126) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 929126 * (59 : ZMod 129393864601) ^ 929126 := by rw [pow_add]
          _ = 95511642390 := by rw [factor_6_19]; decide
      have factor_6_21 : (59 : ZMod 129393864601) ^ 3716505 = 87544014031 := by
        calc
          (59 : ZMod 129393864601) ^ 3716505 = (59 : ZMod 129393864601) ^ (1858252 + 1858252 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1858252 * (59 : ZMod 129393864601) ^ 1858252) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 87544014031 := by rw [factor_6_20]; decide
      have factor_6_22 : (59 : ZMod 129393864601) ^ 7433011 = 127725071361 := by
        calc
          (59 : ZMod 129393864601) ^ 7433011 = (59 : ZMod 129393864601) ^ (3716505 + 3716505 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 3716505 * (59 : ZMod 129393864601) ^ 3716505) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 127725071361 := by rw [factor_6_21]; decide
      have factor_6_23 : (59 : ZMod 129393864601) ^ 14866023 = 122696420810 := by
        calc
          (59 : ZMod 129393864601) ^ 14866023 = (59 : ZMod 129393864601) ^ (7433011 + 7433011 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 7433011 * (59 : ZMod 129393864601) ^ 7433011) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 122696420810 := by rw [factor_6_22]; decide
      have factor_6_24 : (59 : ZMod 129393864601) ^ 29732046 = 18035541692 := by
        calc
          (59 : ZMod 129393864601) ^ 29732046 = (59 : ZMod 129393864601) ^ (14866023 + 14866023) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 14866023 * (59 : ZMod 129393864601) ^ 14866023 := by rw [pow_add]
          _ = 18035541692 := by rw [factor_6_23]; decide
      have factor_6_25 : (59 : ZMod 129393864601) ^ 59464092 = 102593389570 := by
        calc
          (59 : ZMod 129393864601) ^ 59464092 = (59 : ZMod 129393864601) ^ (29732046 + 29732046) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 29732046 * (59 : ZMod 129393864601) ^ 29732046 := by rw [pow_add]
          _ = 102593389570 := by rw [factor_6_24]; decide
      have factor_6_26 : (59 : ZMod 129393864601) ^ 118928184 = 56566424238 := by
        calc
          (59 : ZMod 129393864601) ^ 118928184 = (59 : ZMod 129393864601) ^ (59464092 + 59464092) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 59464092 * (59 : ZMod 129393864601) ^ 59464092 := by rw [pow_add]
          _ = 56566424238 := by rw [factor_6_25]; decide
      have factor_6_27 : (59 : ZMod 129393864601) ^ 237856368 = 9763589481 := by
        calc
          (59 : ZMod 129393864601) ^ 237856368 = (59 : ZMod 129393864601) ^ (118928184 + 118928184) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 118928184 * (59 : ZMod 129393864601) ^ 118928184 := by rw [pow_add]
          _ = 9763589481 := by rw [factor_6_26]; decide
      have factor_6_28 : (59 : ZMod 129393864601) ^ 475712737 = 32875950496 := by
        calc
          (59 : ZMod 129393864601) ^ 475712737 = (59 : ZMod 129393864601) ^ (237856368 + 237856368 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 237856368 * (59 : ZMod 129393864601) ^ 237856368) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 32875950496 := by rw [factor_6_27]; decide
      have factor_6_29 : (59 : ZMod 129393864601) ^ 951425475 = 120050856656 := by
        calc
          (59 : ZMod 129393864601) ^ 951425475 = (59 : ZMod 129393864601) ^ (475712737 + 475712737 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 475712737 * (59 : ZMod 129393864601) ^ 475712737) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 120050856656 := by rw [factor_6_28]; decide
      have factor_6_30 : (59 : ZMod 129393864601) ^ 1902850950 = 91147967387 := by
        calc
          (59 : ZMod 129393864601) ^ 1902850950 = (59 : ZMod 129393864601) ^ (951425475 + 951425475) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 951425475 * (59 : ZMod 129393864601) ^ 951425475 := by rw [pow_add]
          _ = 91147967387 := by rw [factor_6_29]; decide
      have factor_6_31 : (59 : ZMod 129393864601) ^ 3805701900 = 60020879174 := by
        calc
          (59 : ZMod 129393864601) ^ 3805701900 = (59 : ZMod 129393864601) ^ (1902850950 + 1902850950) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1902850950 * (59 : ZMod 129393864601) ^ 1902850950 := by rw [pow_add]
          _ = 60020879174 := by rw [factor_6_30]; decide
      have factor_6_32 : (59 : ZMod 129393864601) ^ 7611403800 = 49815588007 := by
        calc
          (59 : ZMod 129393864601) ^ 7611403800 = (59 : ZMod 129393864601) ^ (3805701900 + 3805701900) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3805701900 * (59 : ZMod 129393864601) ^ 3805701900 := by rw [pow_add]
          _ = 49815588007 := by rw [factor_6_31]; decide
      change (59 : ZMod 129393864601) ^ 7611403800 ≠ 1
      rw [factor_6_32]
      decide
    ·
      have factor_7_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_7_1 : (59 : ZMod 129393864601) ^ 3 = 205379 := by
        calc
          (59 : ZMod 129393864601) ^ 3 = (59 : ZMod 129393864601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 205379 := by rw [factor_7_0]; decide
      have factor_7_2 : (59 : ZMod 129393864601) ^ 6 = 42180533641 := by
        calc
          (59 : ZMod 129393864601) ^ 6 = (59 : ZMod 129393864601) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3 * (59 : ZMod 129393864601) ^ 3 := by rw [pow_add]
          _ = 42180533641 := by rw [factor_7_1]; decide
      have factor_7_3 : (59 : ZMod 129393864601) ^ 12 = 66273523675 := by
        calc
          (59 : ZMod 129393864601) ^ 12 = (59 : ZMod 129393864601) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 6 * (59 : ZMod 129393864601) ^ 6 := by rw [pow_add]
          _ = 66273523675 := by rw [factor_7_2]; decide
      have factor_7_4 : (59 : ZMod 129393864601) ^ 25 = 58403171509 := by
        calc
          (59 : ZMod 129393864601) ^ 25 = (59 : ZMod 129393864601) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 12 * (59 : ZMod 129393864601) ^ 12) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 58403171509 := by rw [factor_7_3]; decide
      have factor_7_5 : (59 : ZMod 129393864601) ^ 50 = 97410870096 := by
        calc
          (59 : ZMod 129393864601) ^ 50 = (59 : ZMod 129393864601) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 25 * (59 : ZMod 129393864601) ^ 25 := by rw [pow_add]
          _ = 97410870096 := by rw [factor_7_4]; decide
      have factor_7_6 : (59 : ZMod 129393864601) ^ 101 = 66500881310 := by
        calc
          (59 : ZMod 129393864601) ^ 101 = (59 : ZMod 129393864601) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 50 * (59 : ZMod 129393864601) ^ 50) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 66500881310 := by rw [factor_7_5]; decide
      have factor_7_7 : (59 : ZMod 129393864601) ^ 202 = 110283501524 := by
        calc
          (59 : ZMod 129393864601) ^ 202 = (59 : ZMod 129393864601) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 101 * (59 : ZMod 129393864601) ^ 101 := by rw [pow_add]
          _ = 110283501524 := by rw [factor_7_6]; decide
      have factor_7_8 : (59 : ZMod 129393864601) ^ 405 = 43706639274 := by
        calc
          (59 : ZMod 129393864601) ^ 405 = (59 : ZMod 129393864601) ^ (202 + 202 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 202 * (59 : ZMod 129393864601) ^ 202) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 43706639274 := by rw [factor_7_7]; decide
      have factor_7_9 : (59 : ZMod 129393864601) ^ 811 = 87146217837 := by
        calc
          (59 : ZMod 129393864601) ^ 811 = (59 : ZMod 129393864601) ^ (405 + 405 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 405 * (59 : ZMod 129393864601) ^ 405) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 87146217837 := by rw [factor_7_8]; decide
      have factor_7_10 : (59 : ZMod 129393864601) ^ 1623 = 63433869907 := by
        calc
          (59 : ZMod 129393864601) ^ 1623 = (59 : ZMod 129393864601) ^ (811 + 811 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 811 * (59 : ZMod 129393864601) ^ 811) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 63433869907 := by rw [factor_7_9]; decide
      have factor_7_11 : (59 : ZMod 129393864601) ^ 3247 = 37190166722 := by
        calc
          (59 : ZMod 129393864601) ^ 3247 = (59 : ZMod 129393864601) ^ (1623 + 1623 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1623 * (59 : ZMod 129393864601) ^ 1623) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 37190166722 := by rw [factor_7_10]; decide
      have factor_7_12 : (59 : ZMod 129393864601) ^ 6494 = 73202577977 := by
        calc
          (59 : ZMod 129393864601) ^ 6494 = (59 : ZMod 129393864601) ^ (3247 + 3247) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3247 * (59 : ZMod 129393864601) ^ 3247 := by rw [pow_add]
          _ = 73202577977 := by rw [factor_7_11]; decide
      have factor_7_13 : (59 : ZMod 129393864601) ^ 12989 = 68725719090 := by
        calc
          (59 : ZMod 129393864601) ^ 12989 = (59 : ZMod 129393864601) ^ (6494 + 6494 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 6494 * (59 : ZMod 129393864601) ^ 6494) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 68725719090 := by rw [factor_7_12]; decide
      have factor_7_14 : (59 : ZMod 129393864601) ^ 25978 = 63690317096 := by
        calc
          (59 : ZMod 129393864601) ^ 25978 = (59 : ZMod 129393864601) ^ (12989 + 12989) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 12989 * (59 : ZMod 129393864601) ^ 12989 := by rw [pow_add]
          _ = 63690317096 := by rw [factor_7_13]; decide
      have factor_7_15 : (59 : ZMod 129393864601) ^ 51957 = 92022018533 := by
        calc
          (59 : ZMod 129393864601) ^ 51957 = (59 : ZMod 129393864601) ^ (25978 + 25978 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 25978 * (59 : ZMod 129393864601) ^ 25978) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 92022018533 := by rw [factor_7_14]; decide
      have factor_7_16 : (59 : ZMod 129393864601) ^ 103915 = 81602189154 := by
        calc
          (59 : ZMod 129393864601) ^ 103915 = (59 : ZMod 129393864601) ^ (51957 + 51957 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 51957 * (59 : ZMod 129393864601) ^ 51957) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 81602189154 := by rw [factor_7_15]; decide
      have factor_7_17 : (59 : ZMod 129393864601) ^ 207830 = 104528202641 := by
        calc
          (59 : ZMod 129393864601) ^ 207830 = (59 : ZMod 129393864601) ^ (103915 + 103915) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 103915 * (59 : ZMod 129393864601) ^ 103915 := by rw [pow_add]
          _ = 104528202641 := by rw [factor_7_16]; decide
      have factor_7_18 : (59 : ZMod 129393864601) ^ 415661 = 29699407196 := by
        calc
          (59 : ZMod 129393864601) ^ 415661 = (59 : ZMod 129393864601) ^ (207830 + 207830 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 207830 * (59 : ZMod 129393864601) ^ 207830) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 29699407196 := by rw [factor_7_17]; decide
      have factor_7_19 : (59 : ZMod 129393864601) ^ 831323 = 42956459658 := by
        calc
          (59 : ZMod 129393864601) ^ 831323 = (59 : ZMod 129393864601) ^ (415661 + 415661 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 415661 * (59 : ZMod 129393864601) ^ 415661) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 42956459658 := by rw [factor_7_18]; decide
      have factor_7_20 : (59 : ZMod 129393864601) ^ 1662647 = 124036962471 := by
        calc
          (59 : ZMod 129393864601) ^ 1662647 = (59 : ZMod 129393864601) ^ (831323 + 831323 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 831323 * (59 : ZMod 129393864601) ^ 831323) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 124036962471 := by rw [factor_7_19]; decide
      have factor_7_21 : (59 : ZMod 129393864601) ^ 3325294 = 24919376512 := by
        calc
          (59 : ZMod 129393864601) ^ 3325294 = (59 : ZMod 129393864601) ^ (1662647 + 1662647) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1662647 * (59 : ZMod 129393864601) ^ 1662647 := by rw [pow_add]
          _ = 24919376512 := by rw [factor_7_20]; decide
      have factor_7_22 : (59 : ZMod 129393864601) ^ 6650589 = 86133500187 := by
        calc
          (59 : ZMod 129393864601) ^ 6650589 = (59 : ZMod 129393864601) ^ (3325294 + 3325294 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 3325294 * (59 : ZMod 129393864601) ^ 3325294) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 86133500187 := by rw [factor_7_21]; decide
      have factor_7_23 : (59 : ZMod 129393864601) ^ 13301178 = 29945266761 := by
        calc
          (59 : ZMod 129393864601) ^ 13301178 = (59 : ZMod 129393864601) ^ (6650589 + 6650589) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 6650589 * (59 : ZMod 129393864601) ^ 6650589 := by rw [pow_add]
          _ = 29945266761 := by rw [factor_7_22]; decide
      have factor_7_24 : (59 : ZMod 129393864601) ^ 26602357 = 120515111699 := by
        calc
          (59 : ZMod 129393864601) ^ 26602357 = (59 : ZMod 129393864601) ^ (13301178 + 13301178 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 13301178 * (59 : ZMod 129393864601) ^ 13301178) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 120515111699 := by rw [factor_7_23]; decide
      have factor_7_25 : (59 : ZMod 129393864601) ^ 53204714 = 24544729615 := by
        calc
          (59 : ZMod 129393864601) ^ 53204714 = (59 : ZMod 129393864601) ^ (26602357 + 26602357) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 26602357 * (59 : ZMod 129393864601) ^ 26602357 := by rw [pow_add]
          _ = 24544729615 := by rw [factor_7_24]; decide
      have factor_7_26 : (59 : ZMod 129393864601) ^ 106409428 = 96092710454 := by
        calc
          (59 : ZMod 129393864601) ^ 106409428 = (59 : ZMod 129393864601) ^ (53204714 + 53204714) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 53204714 * (59 : ZMod 129393864601) ^ 53204714 := by rw [pow_add]
          _ = 96092710454 := by rw [factor_7_25]; decide
      have factor_7_27 : (59 : ZMod 129393864601) ^ 212818856 = 39324928719 := by
        calc
          (59 : ZMod 129393864601) ^ 212818856 = (59 : ZMod 129393864601) ^ (106409428 + 106409428) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 106409428 * (59 : ZMod 129393864601) ^ 106409428 := by rw [pow_add]
          _ = 39324928719 := by rw [factor_7_26]; decide
      have factor_7_28 : (59 : ZMod 129393864601) ^ 425637712 = 83022375589 := by
        calc
          (59 : ZMod 129393864601) ^ 425637712 = (59 : ZMod 129393864601) ^ (212818856 + 212818856) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 212818856 * (59 : ZMod 129393864601) ^ 212818856 := by rw [pow_add]
          _ = 83022375589 := by rw [factor_7_27]; decide
      have factor_7_29 : (59 : ZMod 129393864601) ^ 851275425 = 118020355256 := by
        calc
          (59 : ZMod 129393864601) ^ 851275425 = (59 : ZMod 129393864601) ^ (425637712 + 425637712 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 425637712 * (59 : ZMod 129393864601) ^ 425637712) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 118020355256 := by rw [factor_7_28]; decide
      have factor_7_30 : (59 : ZMod 129393864601) ^ 1702550850 = 104086328332 := by
        calc
          (59 : ZMod 129393864601) ^ 1702550850 = (59 : ZMod 129393864601) ^ (851275425 + 851275425) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 851275425 * (59 : ZMod 129393864601) ^ 851275425 := by rw [pow_add]
          _ = 104086328332 := by rw [factor_7_29]; decide
      have factor_7_31 : (59 : ZMod 129393864601) ^ 3405101700 = 113660045793 := by
        calc
          (59 : ZMod 129393864601) ^ 3405101700 = (59 : ZMod 129393864601) ^ (1702550850 + 1702550850) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1702550850 * (59 : ZMod 129393864601) ^ 1702550850 := by rw [pow_add]
          _ = 113660045793 := by rw [factor_7_30]; decide
      have factor_7_32 : (59 : ZMod 129393864601) ^ 6810203400 = 38259258471 := by
        calc
          (59 : ZMod 129393864601) ^ 6810203400 = (59 : ZMod 129393864601) ^ (3405101700 + 3405101700) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 3405101700 * (59 : ZMod 129393864601) ^ 3405101700 := by rw [pow_add]
          _ = 38259258471 := by rw [factor_7_31]; decide
      change (59 : ZMod 129393864601) ^ 6810203400 ≠ 1
      rw [factor_7_32]
      decide
    ·
      have factor_8_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_8_1 : (59 : ZMod 129393864601) ^ 2 = 3481 := by
        calc
          (59 : ZMod 129393864601) ^ 2 = (59 : ZMod 129393864601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1 := by rw [pow_add]
          _ = 3481 := by rw [factor_8_0]; decide
      have factor_8_2 : (59 : ZMod 129393864601) ^ 5 = 714924299 := by
        calc
          (59 : ZMod 129393864601) ^ 5 = (59 : ZMod 129393864601) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2 * (59 : ZMod 129393864601) ^ 2) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 714924299 := by rw [factor_8_1]; decide
      have factor_8_3 : (59 : ZMod 129393864601) ^ 10 = 119042064917 := by
        calc
          (59 : ZMod 129393864601) ^ 10 = (59 : ZMod 129393864601) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 5 * (59 : ZMod 129393864601) ^ 5 := by rw [pow_add]
          _ = 119042064917 := by rw [factor_8_2]; decide
      have factor_8_4 : (59 : ZMod 129393864601) ^ 20 = 83571379040 := by
        calc
          (59 : ZMod 129393864601) ^ 20 = (59 : ZMod 129393864601) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 10 * (59 : ZMod 129393864601) ^ 10 := by rw [pow_add]
          _ = 83571379040 := by rw [factor_8_3]; decide
      have factor_8_5 : (59 : ZMod 129393864601) ^ 41 = 111648850861 := by
        calc
          (59 : ZMod 129393864601) ^ 41 = (59 : ZMod 129393864601) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 20 * (59 : ZMod 129393864601) ^ 20) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 111648850861 := by rw [factor_8_4]; decide
      have factor_8_6 : (59 : ZMod 129393864601) ^ 83 = 32950430289 := by
        calc
          (59 : ZMod 129393864601) ^ 83 = (59 : ZMod 129393864601) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 41 * (59 : ZMod 129393864601) ^ 41) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 32950430289 := by rw [factor_8_5]; decide
      have factor_8_7 : (59 : ZMod 129393864601) ^ 167 = 35540141282 := by
        calc
          (59 : ZMod 129393864601) ^ 167 = (59 : ZMod 129393864601) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 83 * (59 : ZMod 129393864601) ^ 83) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 35540141282 := by rw [factor_8_6]; decide
      have factor_8_8 : (59 : ZMod 129393864601) ^ 335 = 93684238702 := by
        calc
          (59 : ZMod 129393864601) ^ 335 = (59 : ZMod 129393864601) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 167 * (59 : ZMod 129393864601) ^ 167) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 93684238702 := by rw [factor_8_7]; decide
      have factor_8_9 : (59 : ZMod 129393864601) ^ 670 = 97195932262 := by
        calc
          (59 : ZMod 129393864601) ^ 670 = (59 : ZMod 129393864601) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 335 * (59 : ZMod 129393864601) ^ 335 := by rw [pow_add]
          _ = 97195932262 := by rw [factor_8_8]; decide
      have factor_8_10 : (59 : ZMod 129393864601) ^ 1341 = 100430586731 := by
        calc
          (59 : ZMod 129393864601) ^ 1341 = (59 : ZMod 129393864601) ^ (670 + 670 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 670 * (59 : ZMod 129393864601) ^ 670) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 100430586731 := by rw [factor_8_9]; decide
      have factor_8_11 : (59 : ZMod 129393864601) ^ 2682 = 105657791974 := by
        calc
          (59 : ZMod 129393864601) ^ 2682 = (59 : ZMod 129393864601) ^ (1341 + 1341) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1341 * (59 : ZMod 129393864601) ^ 1341 := by rw [pow_add]
          _ = 105657791974 := by rw [factor_8_10]; decide
      have factor_8_12 : (59 : ZMod 129393864601) ^ 5365 = 51199712255 := by
        calc
          (59 : ZMod 129393864601) ^ 5365 = (59 : ZMod 129393864601) ^ (2682 + 2682 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2682 * (59 : ZMod 129393864601) ^ 2682) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 51199712255 := by rw [factor_8_11]; decide
      have factor_8_13 : (59 : ZMod 129393864601) ^ 10730 = 18469172665 := by
        calc
          (59 : ZMod 129393864601) ^ 10730 = (59 : ZMod 129393864601) ^ (5365 + 5365) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 5365 * (59 : ZMod 129393864601) ^ 5365 := by rw [pow_add]
          _ = 18469172665 := by rw [factor_8_12]; decide
      have factor_8_14 : (59 : ZMod 129393864601) ^ 21460 = 118505582768 := by
        calc
          (59 : ZMod 129393864601) ^ 21460 = (59 : ZMod 129393864601) ^ (10730 + 10730) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 10730 * (59 : ZMod 129393864601) ^ 10730 := by rw [pow_add]
          _ = 118505582768 := by rw [factor_8_13]; decide
      have factor_8_15 : (59 : ZMod 129393864601) ^ 42921 = 66000183291 := by
        calc
          (59 : ZMod 129393864601) ^ 42921 = (59 : ZMod 129393864601) ^ (21460 + 21460 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 21460 * (59 : ZMod 129393864601) ^ 21460) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 66000183291 := by rw [factor_8_14]; decide
      have factor_8_16 : (59 : ZMod 129393864601) ^ 85843 = 89331127166 := by
        calc
          (59 : ZMod 129393864601) ^ 85843 = (59 : ZMod 129393864601) ^ (42921 + 42921 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 42921 * (59 : ZMod 129393864601) ^ 42921) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 89331127166 := by rw [factor_8_15]; decide
      have factor_8_17 : (59 : ZMod 129393864601) ^ 171686 = 51881358974 := by
        calc
          (59 : ZMod 129393864601) ^ 171686 = (59 : ZMod 129393864601) ^ (85843 + 85843) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 85843 * (59 : ZMod 129393864601) ^ 85843 := by rw [pow_add]
          _ = 51881358974 := by rw [factor_8_16]; decide
      have factor_8_18 : (59 : ZMod 129393864601) ^ 343372 = 17906731760 := by
        calc
          (59 : ZMod 129393864601) ^ 343372 = (59 : ZMod 129393864601) ^ (171686 + 171686) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 171686 * (59 : ZMod 129393864601) ^ 171686 := by rw [pow_add]
          _ = 17906731760 := by rw [factor_8_17]; decide
      have factor_8_19 : (59 : ZMod 129393864601) ^ 686745 = 46839661259 := by
        calc
          (59 : ZMod 129393864601) ^ 686745 = (59 : ZMod 129393864601) ^ (343372 + 343372 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 343372 * (59 : ZMod 129393864601) ^ 343372) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 46839661259 := by rw [factor_8_18]; decide
      have factor_8_20 : (59 : ZMod 129393864601) ^ 1373491 = 108769569630 := by
        calc
          (59 : ZMod 129393864601) ^ 1373491 = (59 : ZMod 129393864601) ^ (686745 + 686745 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 686745 * (59 : ZMod 129393864601) ^ 686745) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 108769569630 := by rw [factor_8_19]; decide
      have factor_8_21 : (59 : ZMod 129393864601) ^ 2746982 = 40588812289 := by
        calc
          (59 : ZMod 129393864601) ^ 2746982 = (59 : ZMod 129393864601) ^ (1373491 + 1373491) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1373491 * (59 : ZMod 129393864601) ^ 1373491 := by rw [pow_add]
          _ = 40588812289 := by rw [factor_8_20]; decide
      have factor_8_22 : (59 : ZMod 129393864601) ^ 5493965 = 45329323277 := by
        calc
          (59 : ZMod 129393864601) ^ 5493965 = (59 : ZMod 129393864601) ^ (2746982 + 2746982 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2746982 * (59 : ZMod 129393864601) ^ 2746982) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 45329323277 := by rw [factor_8_21]; decide
      have factor_8_23 : (59 : ZMod 129393864601) ^ 10987930 = 78244780958 := by
        calc
          (59 : ZMod 129393864601) ^ 10987930 = (59 : ZMod 129393864601) ^ (5493965 + 5493965) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 5493965 * (59 : ZMod 129393864601) ^ 5493965 := by rw [pow_add]
          _ = 78244780958 := by rw [factor_8_22]; decide
      have factor_8_24 : (59 : ZMod 129393864601) ^ 21975860 = 22537721836 := by
        calc
          (59 : ZMod 129393864601) ^ 21975860 = (59 : ZMod 129393864601) ^ (10987930 + 10987930) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 10987930 * (59 : ZMod 129393864601) ^ 10987930 := by rw [pow_add]
          _ = 22537721836 := by rw [factor_8_23]; decide
      have factor_8_25 : (59 : ZMod 129393864601) ^ 43951720 = 21852542186 := by
        calc
          (59 : ZMod 129393864601) ^ 43951720 = (59 : ZMod 129393864601) ^ (21975860 + 21975860) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 21975860 * (59 : ZMod 129393864601) ^ 21975860 := by rw [pow_add]
          _ = 21852542186 := by rw [factor_8_24]; decide
      have factor_8_26 : (59 : ZMod 129393864601) ^ 87903440 = 94728974761 := by
        calc
          (59 : ZMod 129393864601) ^ 87903440 = (59 : ZMod 129393864601) ^ (43951720 + 43951720) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 43951720 * (59 : ZMod 129393864601) ^ 43951720 := by rw [pow_add]
          _ = 94728974761 := by rw [factor_8_25]; decide
      have factor_8_27 : (59 : ZMod 129393864601) ^ 175806881 = 20956067486 := by
        calc
          (59 : ZMod 129393864601) ^ 175806881 = (59 : ZMod 129393864601) ^ (87903440 + 87903440 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 87903440 * (59 : ZMod 129393864601) ^ 87903440) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 20956067486 := by rw [factor_8_26]; decide
      have factor_8_28 : (59 : ZMod 129393864601) ^ 351613762 = 49123316459 := by
        calc
          (59 : ZMod 129393864601) ^ 351613762 = (59 : ZMod 129393864601) ^ (175806881 + 175806881) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 175806881 * (59 : ZMod 129393864601) ^ 175806881 := by rw [pow_add]
          _ = 49123316459 := by rw [factor_8_27]; decide
      have factor_8_29 : (59 : ZMod 129393864601) ^ 703227525 = 58151483349 := by
        calc
          (59 : ZMod 129393864601) ^ 703227525 = (59 : ZMod 129393864601) ^ (351613762 + 351613762 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 351613762 * (59 : ZMod 129393864601) ^ 351613762) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 58151483349 := by rw [factor_8_28]; decide
      have factor_8_30 : (59 : ZMod 129393864601) ^ 1406455050 = 104083687617 := by
        calc
          (59 : ZMod 129393864601) ^ 1406455050 = (59 : ZMod 129393864601) ^ (703227525 + 703227525) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 703227525 * (59 : ZMod 129393864601) ^ 703227525 := by rw [pow_add]
          _ = 104083687617 := by rw [factor_8_29]; decide
      have factor_8_31 : (59 : ZMod 129393864601) ^ 2812910100 = 100727358264 := by
        calc
          (59 : ZMod 129393864601) ^ 2812910100 = (59 : ZMod 129393864601) ^ (1406455050 + 1406455050) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1406455050 * (59 : ZMod 129393864601) ^ 1406455050 := by rw [pow_add]
          _ = 100727358264 := by rw [factor_8_30]; decide
      have factor_8_32 : (59 : ZMod 129393864601) ^ 5625820200 = 84491671139 := by
        calc
          (59 : ZMod 129393864601) ^ 5625820200 = (59 : ZMod 129393864601) ^ (2812910100 + 2812910100) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2812910100 * (59 : ZMod 129393864601) ^ 2812910100 := by rw [pow_add]
          _ = 84491671139 := by rw [factor_8_31]; decide
      change (59 : ZMod 129393864601) ^ 5625820200 ≠ 1
      rw [factor_8_32]
      decide
    ·
      have factor_9_0 : (59 : ZMod 129393864601) ^ 1 = 59 := by norm_num
      have factor_9_1 : (59 : ZMod 129393864601) ^ 2 = 3481 := by
        calc
          (59 : ZMod 129393864601) ^ 2 = (59 : ZMod 129393864601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1 * (59 : ZMod 129393864601) ^ 1 := by rw [pow_add]
          _ = 3481 := by rw [factor_9_0]; decide
      have factor_9_2 : (59 : ZMod 129393864601) ^ 4 = 12117361 := by
        calc
          (59 : ZMod 129393864601) ^ 4 = (59 : ZMod 129393864601) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2 * (59 : ZMod 129393864601) ^ 2 := by rw [pow_add]
          _ = 12117361 := by rw [factor_9_1]; decide
      have factor_9_3 : (59 : ZMod 129393864601) ^ 8 = 97795146787 := by
        calc
          (59 : ZMod 129393864601) ^ 8 = (59 : ZMod 129393864601) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 4 * (59 : ZMod 129393864601) ^ 4 := by rw [pow_add]
          _ = 97795146787 := by rw [factor_9_2]; decide
      have factor_9_4 : (59 : ZMod 129393864601) ^ 16 = 93179949552 := by
        calc
          (59 : ZMod 129393864601) ^ 16 = (59 : ZMod 129393864601) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 8 * (59 : ZMod 129393864601) ^ 8 := by rw [pow_add]
          _ = 93179949552 := by rw [factor_9_3]; decide
      have factor_9_5 : (59 : ZMod 129393864601) ^ 33 = 49851072793 := by
        calc
          (59 : ZMod 129393864601) ^ 33 = (59 : ZMod 129393864601) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 16 * (59 : ZMod 129393864601) ^ 16) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 49851072793 := by rw [factor_9_4]; decide
      have factor_9_6 : (59 : ZMod 129393864601) ^ 66 = 14855334815 := by
        calc
          (59 : ZMod 129393864601) ^ 66 = (59 : ZMod 129393864601) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 33 * (59 : ZMod 129393864601) ^ 33 := by rw [pow_add]
          _ = 14855334815 := by rw [factor_9_5]; decide
      have factor_9_7 : (59 : ZMod 129393864601) ^ 132 = 93441641063 := by
        calc
          (59 : ZMod 129393864601) ^ 132 = (59 : ZMod 129393864601) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 66 * (59 : ZMod 129393864601) ^ 66 := by rw [pow_add]
          _ = 93441641063 := by rw [factor_9_6]; decide
      have factor_9_8 : (59 : ZMod 129393864601) ^ 265 = 109800657002 := by
        calc
          (59 : ZMod 129393864601) ^ 265 = (59 : ZMod 129393864601) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 132 * (59 : ZMod 129393864601) ^ 132) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 109800657002 := by rw [factor_9_7]; decide
      have factor_9_9 : (59 : ZMod 129393864601) ^ 531 = 28068288351 := by
        calc
          (59 : ZMod 129393864601) ^ 531 = (59 : ZMod 129393864601) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 265 * (59 : ZMod 129393864601) ^ 265) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 28068288351 := by rw [factor_9_8]; decide
      have factor_9_10 : (59 : ZMod 129393864601) ^ 1063 = 11011417809 := by
        calc
          (59 : ZMod 129393864601) ^ 1063 = (59 : ZMod 129393864601) ^ (531 + 531 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 531 * (59 : ZMod 129393864601) ^ 531) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 11011417809 := by rw [factor_9_9]; decide
      have factor_9_11 : (59 : ZMod 129393864601) ^ 2127 = 6470929246 := by
        calc
          (59 : ZMod 129393864601) ^ 2127 = (59 : ZMod 129393864601) ^ (1063 + 1063 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1063 * (59 : ZMod 129393864601) ^ 1063) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 6470929246 := by rw [factor_9_10]; decide
      have factor_9_12 : (59 : ZMod 129393864601) ^ 4255 = 46235546825 := by
        calc
          (59 : ZMod 129393864601) ^ 4255 = (59 : ZMod 129393864601) ^ (2127 + 2127 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 2127 * (59 : ZMod 129393864601) ^ 2127) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 46235546825 := by rw [factor_9_11]; decide
      have factor_9_13 : (59 : ZMod 129393864601) ^ 8510 = 71102280250 := by
        calc
          (59 : ZMod 129393864601) ^ 8510 = (59 : ZMod 129393864601) ^ (4255 + 4255) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 4255 * (59 : ZMod 129393864601) ^ 4255 := by rw [pow_add]
          _ = 71102280250 := by rw [factor_9_12]; decide
      have factor_9_14 : (59 : ZMod 129393864601) ^ 17020 = 125198708270 := by
        calc
          (59 : ZMod 129393864601) ^ 17020 = (59 : ZMod 129393864601) ^ (8510 + 8510) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 8510 * (59 : ZMod 129393864601) ^ 8510 := by rw [pow_add]
          _ = 125198708270 := by rw [factor_9_13]; decide
      have factor_9_15 : (59 : ZMod 129393864601) ^ 34041 = 17663245347 := by
        calc
          (59 : ZMod 129393864601) ^ 34041 = (59 : ZMod 129393864601) ^ (17020 + 17020 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 17020 * (59 : ZMod 129393864601) ^ 17020) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 17663245347 := by rw [factor_9_14]; decide
      have factor_9_16 : (59 : ZMod 129393864601) ^ 68082 = 62656499456 := by
        calc
          (59 : ZMod 129393864601) ^ 68082 = (59 : ZMod 129393864601) ^ (34041 + 34041) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 34041 * (59 : ZMod 129393864601) ^ 34041 := by rw [pow_add]
          _ = 62656499456 := by rw [factor_9_15]; decide
      have factor_9_17 : (59 : ZMod 129393864601) ^ 136165 = 34192557907 := by
        calc
          (59 : ZMod 129393864601) ^ 136165 = (59 : ZMod 129393864601) ^ (68082 + 68082 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 68082 * (59 : ZMod 129393864601) ^ 68082) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 34192557907 := by rw [factor_9_16]; decide
      have factor_9_18 : (59 : ZMod 129393864601) ^ 272330 = 100962887260 := by
        calc
          (59 : ZMod 129393864601) ^ 272330 = (59 : ZMod 129393864601) ^ (136165 + 136165) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 136165 * (59 : ZMod 129393864601) ^ 136165 := by rw [pow_add]
          _ = 100962887260 := by rw [factor_9_17]; decide
      have factor_9_19 : (59 : ZMod 129393864601) ^ 544660 = 10577610663 := by
        calc
          (59 : ZMod 129393864601) ^ 544660 = (59 : ZMod 129393864601) ^ (272330 + 272330) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 272330 * (59 : ZMod 129393864601) ^ 272330 := by rw [pow_add]
          _ = 10577610663 := by rw [factor_9_18]; decide
      have factor_9_20 : (59 : ZMod 129393864601) ^ 1089320 = 4811531509 := by
        calc
          (59 : ZMod 129393864601) ^ 1089320 = (59 : ZMod 129393864601) ^ (544660 + 544660) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 544660 * (59 : ZMod 129393864601) ^ 544660 := by rw [pow_add]
          _ = 4811531509 := by rw [factor_9_19]; decide
      have factor_9_21 : (59 : ZMod 129393864601) ^ 2178641 = 60788161516 := by
        calc
          (59 : ZMod 129393864601) ^ 2178641 = (59 : ZMod 129393864601) ^ (1089320 + 1089320 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 1089320 * (59 : ZMod 129393864601) ^ 1089320) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 60788161516 := by rw [factor_9_20]; decide
      have factor_9_22 : (59 : ZMod 129393864601) ^ 4357282 = 105069860107 := by
        calc
          (59 : ZMod 129393864601) ^ 4357282 = (59 : ZMod 129393864601) ^ (2178641 + 2178641) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2178641 * (59 : ZMod 129393864601) ^ 2178641 := by rw [pow_add]
          _ = 105069860107 := by rw [factor_9_21]; decide
      have factor_9_23 : (59 : ZMod 129393864601) ^ 8714565 = 36276149405 := by
        calc
          (59 : ZMod 129393864601) ^ 8714565 = (59 : ZMod 129393864601) ^ (4357282 + 4357282 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 4357282 * (59 : ZMod 129393864601) ^ 4357282) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 36276149405 := by rw [factor_9_22]; decide
      have factor_9_24 : (59 : ZMod 129393864601) ^ 17429130 = 6457084484 := by
        calc
          (59 : ZMod 129393864601) ^ 17429130 = (59 : ZMod 129393864601) ^ (8714565 + 8714565) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 8714565 * (59 : ZMod 129393864601) ^ 8714565 := by rw [pow_add]
          _ = 6457084484 := by rw [factor_9_23]; decide
      have factor_9_25 : (59 : ZMod 129393864601) ^ 34858260 = 71548352241 := by
        calc
          (59 : ZMod 129393864601) ^ 34858260 = (59 : ZMod 129393864601) ^ (17429130 + 17429130) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 17429130 * (59 : ZMod 129393864601) ^ 17429130 := by rw [pow_add]
          _ = 71548352241 := by rw [factor_9_24]; decide
      have factor_9_26 : (59 : ZMod 129393864601) ^ 69716521 = 34345343093 := by
        calc
          (59 : ZMod 129393864601) ^ 69716521 = (59 : ZMod 129393864601) ^ (34858260 + 34858260 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 34858260 * (59 : ZMod 129393864601) ^ 34858260) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 34345343093 := by rw [factor_9_25]; decide
      have factor_9_27 : (59 : ZMod 129393864601) ^ 139433043 = 7683232983 := by
        calc
          (59 : ZMod 129393864601) ^ 139433043 = (59 : ZMod 129393864601) ^ (69716521 + 69716521 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 69716521 * (59 : ZMod 129393864601) ^ 69716521) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 7683232983 := by rw [factor_9_26]; decide
      have factor_9_28 : (59 : ZMod 129393864601) ^ 278866087 = 29514658577 := by
        calc
          (59 : ZMod 129393864601) ^ 278866087 = (59 : ZMod 129393864601) ^ (139433043 + 139433043 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 139433043 * (59 : ZMod 129393864601) ^ 139433043) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 29514658577 := by rw [factor_9_27]; decide
      have factor_9_29 : (59 : ZMod 129393864601) ^ 557732175 = 63488098265 := by
        calc
          (59 : ZMod 129393864601) ^ 557732175 = (59 : ZMod 129393864601) ^ (278866087 + 278866087 + 1) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = ((59 : ZMod 129393864601) ^ 278866087 * (59 : ZMod 129393864601) ^ 278866087) * (59 : ZMod 129393864601) := by rw [pow_succ, pow_add]
          _ = 63488098265 := by rw [factor_9_28]; decide
      have factor_9_30 : (59 : ZMod 129393864601) ^ 1115464350 = 102539943042 := by
        calc
          (59 : ZMod 129393864601) ^ 1115464350 = (59 : ZMod 129393864601) ^ (557732175 + 557732175) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 557732175 * (59 : ZMod 129393864601) ^ 557732175 := by rw [pow_add]
          _ = 102539943042 := by rw [factor_9_29]; decide
      have factor_9_31 : (59 : ZMod 129393864601) ^ 2230928700 = 76230631047 := by
        calc
          (59 : ZMod 129393864601) ^ 2230928700 = (59 : ZMod 129393864601) ^ (1115464350 + 1115464350) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 1115464350 * (59 : ZMod 129393864601) ^ 1115464350 := by rw [pow_add]
          _ = 76230631047 := by rw [factor_9_30]; decide
      have factor_9_32 : (59 : ZMod 129393864601) ^ 4461857400 = 33071360531 := by
        calc
          (59 : ZMod 129393864601) ^ 4461857400 = (59 : ZMod 129393864601) ^ (2230928700 + 2230928700) :=
            congrArg (fun n : ℕ => (59 : ZMod 129393864601) ^ n) (by norm_num)
          _ = (59 : ZMod 129393864601) ^ 2230928700 * (59 : ZMod 129393864601) ^ 2230928700 := by rw [pow_add]
          _ = 33071360531 := by rw [factor_9_31]; decide
      change (59 : ZMod 129393864601) ^ 4461857400 ≠ 1
      rw [factor_9_32]
      decide

#print axioms prime_lucas_129393864601

end TotientTailPeriodKiller
end Erdos249257
