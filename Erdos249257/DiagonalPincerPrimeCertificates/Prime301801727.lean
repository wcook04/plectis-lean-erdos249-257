import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_301801727 : Nat.Prime 301801727 := by
  apply lucas_primality 301801727 (5 : ZMod 301801727)
  ·
      have fermat_0 : (5 : ZMod 301801727) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 301801727) ^ 2 = 25 := by
        calc
          (5 : ZMod 301801727) ^ 2 = (5 : ZMod 301801727) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 1 * (5 : ZMod 301801727) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 301801727) ^ 4 = 625 := by
        calc
          (5 : ZMod 301801727) ^ 4 = (5 : ZMod 301801727) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 2 * (5 : ZMod 301801727) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 301801727) ^ 8 = 390625 := by
        calc
          (5 : ZMod 301801727) ^ 8 = (5 : ZMod 301801727) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 4 * (5 : ZMod 301801727) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 301801727) ^ 17 = 286488996 := by
        calc
          (5 : ZMod 301801727) ^ 17 = (5 : ZMod 301801727) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 8 * (5 : ZMod 301801727) ^ 8) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 286488996 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 301801727) ^ 35 = 47575350 := by
        calc
          (5 : ZMod 301801727) ^ 35 = (5 : ZMod 301801727) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 17 * (5 : ZMod 301801727) ^ 17) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 47575350 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 301801727) ^ 71 = 132246507 := by
        calc
          (5 : ZMod 301801727) ^ 71 = (5 : ZMod 301801727) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 35 * (5 : ZMod 301801727) ^ 35) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 132246507 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 301801727) ^ 143 = 174423291 := by
        calc
          (5 : ZMod 301801727) ^ 143 = (5 : ZMod 301801727) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 71 * (5 : ZMod 301801727) ^ 71) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 174423291 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 301801727) ^ 287 = 180040583 := by
        calc
          (5 : ZMod 301801727) ^ 287 = (5 : ZMod 301801727) ^ (143 + 143 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 143 * (5 : ZMod 301801727) ^ 143) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 180040583 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 301801727) ^ 575 = 21053897 := by
        calc
          (5 : ZMod 301801727) ^ 575 = (5 : ZMod 301801727) ^ (287 + 287 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 287 * (5 : ZMod 301801727) ^ 287) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 21053897 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 301801727) ^ 1151 = 2311501 := by
        calc
          (5 : ZMod 301801727) ^ 1151 = (5 : ZMod 301801727) ^ (575 + 575 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 575 * (5 : ZMod 301801727) ^ 575) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 2311501 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 301801727) ^ 2302 = 240899920 := by
        calc
          (5 : ZMod 301801727) ^ 2302 = (5 : ZMod 301801727) ^ (1151 + 1151) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 1151 * (5 : ZMod 301801727) ^ 1151 := by rw [pow_add]
          _ = 240899920 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 301801727) ^ 4605 = 233414370 := by
        calc
          (5 : ZMod 301801727) ^ 4605 = (5 : ZMod 301801727) ^ (2302 + 2302 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 2302 * (5 : ZMod 301801727) ^ 2302) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 233414370 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 301801727) ^ 9210 = 274619640 := by
        calc
          (5 : ZMod 301801727) ^ 9210 = (5 : ZMod 301801727) ^ (4605 + 4605) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 4605 * (5 : ZMod 301801727) ^ 4605 := by rw [pow_add]
          _ = 274619640 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 301801727) ^ 18420 = 298065255 := by
        calc
          (5 : ZMod 301801727) ^ 18420 = (5 : ZMod 301801727) ^ (9210 + 9210) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 9210 * (5 : ZMod 301801727) ^ 9210 := by rw [pow_add]
          _ = 298065255 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 301801727) ^ 36841 = 280984001 := by
        calc
          (5 : ZMod 301801727) ^ 36841 = (5 : ZMod 301801727) ^ (18420 + 18420 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 18420 * (5 : ZMod 301801727) ^ 18420) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 280984001 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 301801727) ^ 73682 = 93494340 := by
        calc
          (5 : ZMod 301801727) ^ 73682 = (5 : ZMod 301801727) ^ (36841 + 36841) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 36841 * (5 : ZMod 301801727) ^ 36841 := by rw [pow_add]
          _ = 93494340 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 301801727) ^ 147364 = 147916334 := by
        calc
          (5 : ZMod 301801727) ^ 147364 = (5 : ZMod 301801727) ^ (73682 + 73682) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 73682 * (5 : ZMod 301801727) ^ 73682 := by rw [pow_add]
          _ = 147916334 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 301801727) ^ 294728 = 115616124 := by
        calc
          (5 : ZMod 301801727) ^ 294728 = (5 : ZMod 301801727) ^ (147364 + 147364) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 147364 * (5 : ZMod 301801727) ^ 147364 := by rw [pow_add]
          _ = 115616124 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 301801727) ^ 589456 = 212097183 := by
        calc
          (5 : ZMod 301801727) ^ 589456 = (5 : ZMod 301801727) ^ (294728 + 294728) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 294728 * (5 : ZMod 301801727) ^ 294728 := by rw [pow_add]
          _ = 212097183 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 301801727) ^ 1178912 = 172643814 := by
        calc
          (5 : ZMod 301801727) ^ 1178912 = (5 : ZMod 301801727) ^ (589456 + 589456) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 589456 * (5 : ZMod 301801727) ^ 589456 := by rw [pow_add]
          _ = 172643814 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 301801727) ^ 2357825 = 224623381 := by
        calc
          (5 : ZMod 301801727) ^ 2357825 = (5 : ZMod 301801727) ^ (1178912 + 1178912 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 1178912 * (5 : ZMod 301801727) ^ 1178912) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 224623381 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 301801727) ^ 4715651 = 211965477 := by
        calc
          (5 : ZMod 301801727) ^ 4715651 = (5 : ZMod 301801727) ^ (2357825 + 2357825 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 2357825 * (5 : ZMod 301801727) ^ 2357825) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 211965477 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 301801727) ^ 9431303 = 17722370 := by
        calc
          (5 : ZMod 301801727) ^ 9431303 = (5 : ZMod 301801727) ^ (4715651 + 4715651 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 4715651 * (5 : ZMod 301801727) ^ 4715651) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 17722370 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 301801727) ^ 18862607 = 286717715 := by
        calc
          (5 : ZMod 301801727) ^ 18862607 = (5 : ZMod 301801727) ^ (9431303 + 9431303 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 9431303 * (5 : ZMod 301801727) ^ 9431303) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 286717715 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 301801727) ^ 37725215 = 7180125 := by
        calc
          (5 : ZMod 301801727) ^ 37725215 = (5 : ZMod 301801727) ^ (18862607 + 18862607 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 18862607 * (5 : ZMod 301801727) ^ 18862607) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 7180125 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 301801727) ^ 75450431 = 7435336 := by
        calc
          (5 : ZMod 301801727) ^ 75450431 = (5 : ZMod 301801727) ^ (37725215 + 37725215 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 37725215 * (5 : ZMod 301801727) ^ 37725215) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 7435336 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 301801727) ^ 150900863 = 301801726 := by
        calc
          (5 : ZMod 301801727) ^ 150900863 = (5 : ZMod 301801727) ^ (75450431 + 75450431 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 75450431 * (5 : ZMod 301801727) ^ 75450431) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 301801726 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 301801727) ^ 301801726 = 1 := by
        calc
          (5 : ZMod 301801727) ^ 301801726 = (5 : ZMod 301801727) ^ (150900863 + 150900863) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 150900863 * (5 : ZMod 301801727) ^ 150900863 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (97, 1), (1555679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (97, 1), (1555679, 1)] : List FactorBlock).map factorBlockValue).prod = 301801727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 301801727) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 301801727) ^ 2 = 25 := by
        calc
          (5 : ZMod 301801727) ^ 2 = (5 : ZMod 301801727) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 1 * (5 : ZMod 301801727) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 301801727) ^ 4 = 625 := by
        calc
          (5 : ZMod 301801727) ^ 4 = (5 : ZMod 301801727) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 2 * (5 : ZMod 301801727) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 301801727) ^ 8 = 390625 := by
        calc
          (5 : ZMod 301801727) ^ 8 = (5 : ZMod 301801727) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 4 * (5 : ZMod 301801727) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 301801727) ^ 17 = 286488996 := by
        calc
          (5 : ZMod 301801727) ^ 17 = (5 : ZMod 301801727) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 8 * (5 : ZMod 301801727) ^ 8) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 286488996 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 301801727) ^ 35 = 47575350 := by
        calc
          (5 : ZMod 301801727) ^ 35 = (5 : ZMod 301801727) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 17 * (5 : ZMod 301801727) ^ 17) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 47575350 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 301801727) ^ 71 = 132246507 := by
        calc
          (5 : ZMod 301801727) ^ 71 = (5 : ZMod 301801727) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 35 * (5 : ZMod 301801727) ^ 35) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 132246507 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 301801727) ^ 143 = 174423291 := by
        calc
          (5 : ZMod 301801727) ^ 143 = (5 : ZMod 301801727) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 71 * (5 : ZMod 301801727) ^ 71) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 174423291 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 301801727) ^ 287 = 180040583 := by
        calc
          (5 : ZMod 301801727) ^ 287 = (5 : ZMod 301801727) ^ (143 + 143 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 143 * (5 : ZMod 301801727) ^ 143) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 180040583 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 301801727) ^ 575 = 21053897 := by
        calc
          (5 : ZMod 301801727) ^ 575 = (5 : ZMod 301801727) ^ (287 + 287 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 287 * (5 : ZMod 301801727) ^ 287) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 21053897 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 301801727) ^ 1151 = 2311501 := by
        calc
          (5 : ZMod 301801727) ^ 1151 = (5 : ZMod 301801727) ^ (575 + 575 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 575 * (5 : ZMod 301801727) ^ 575) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 2311501 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 301801727) ^ 2302 = 240899920 := by
        calc
          (5 : ZMod 301801727) ^ 2302 = (5 : ZMod 301801727) ^ (1151 + 1151) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 1151 * (5 : ZMod 301801727) ^ 1151 := by rw [pow_add]
          _ = 240899920 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 301801727) ^ 4605 = 233414370 := by
        calc
          (5 : ZMod 301801727) ^ 4605 = (5 : ZMod 301801727) ^ (2302 + 2302 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 2302 * (5 : ZMod 301801727) ^ 2302) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 233414370 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 301801727) ^ 9210 = 274619640 := by
        calc
          (5 : ZMod 301801727) ^ 9210 = (5 : ZMod 301801727) ^ (4605 + 4605) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 4605 * (5 : ZMod 301801727) ^ 4605 := by rw [pow_add]
          _ = 274619640 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 301801727) ^ 18420 = 298065255 := by
        calc
          (5 : ZMod 301801727) ^ 18420 = (5 : ZMod 301801727) ^ (9210 + 9210) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 9210 * (5 : ZMod 301801727) ^ 9210 := by rw [pow_add]
          _ = 298065255 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 301801727) ^ 36841 = 280984001 := by
        calc
          (5 : ZMod 301801727) ^ 36841 = (5 : ZMod 301801727) ^ (18420 + 18420 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 18420 * (5 : ZMod 301801727) ^ 18420) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 280984001 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 301801727) ^ 73682 = 93494340 := by
        calc
          (5 : ZMod 301801727) ^ 73682 = (5 : ZMod 301801727) ^ (36841 + 36841) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 36841 * (5 : ZMod 301801727) ^ 36841 := by rw [pow_add]
          _ = 93494340 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 301801727) ^ 147364 = 147916334 := by
        calc
          (5 : ZMod 301801727) ^ 147364 = (5 : ZMod 301801727) ^ (73682 + 73682) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 73682 * (5 : ZMod 301801727) ^ 73682 := by rw [pow_add]
          _ = 147916334 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 301801727) ^ 294728 = 115616124 := by
        calc
          (5 : ZMod 301801727) ^ 294728 = (5 : ZMod 301801727) ^ (147364 + 147364) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 147364 * (5 : ZMod 301801727) ^ 147364 := by rw [pow_add]
          _ = 115616124 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 301801727) ^ 589456 = 212097183 := by
        calc
          (5 : ZMod 301801727) ^ 589456 = (5 : ZMod 301801727) ^ (294728 + 294728) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 294728 * (5 : ZMod 301801727) ^ 294728 := by rw [pow_add]
          _ = 212097183 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 301801727) ^ 1178912 = 172643814 := by
        calc
          (5 : ZMod 301801727) ^ 1178912 = (5 : ZMod 301801727) ^ (589456 + 589456) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 589456 * (5 : ZMod 301801727) ^ 589456 := by rw [pow_add]
          _ = 172643814 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 301801727) ^ 2357825 = 224623381 := by
        calc
          (5 : ZMod 301801727) ^ 2357825 = (5 : ZMod 301801727) ^ (1178912 + 1178912 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 1178912 * (5 : ZMod 301801727) ^ 1178912) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 224623381 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 301801727) ^ 4715651 = 211965477 := by
        calc
          (5 : ZMod 301801727) ^ 4715651 = (5 : ZMod 301801727) ^ (2357825 + 2357825 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 2357825 * (5 : ZMod 301801727) ^ 2357825) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 211965477 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 301801727) ^ 9431303 = 17722370 := by
        calc
          (5 : ZMod 301801727) ^ 9431303 = (5 : ZMod 301801727) ^ (4715651 + 4715651 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 4715651 * (5 : ZMod 301801727) ^ 4715651) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 17722370 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 301801727) ^ 18862607 = 286717715 := by
        calc
          (5 : ZMod 301801727) ^ 18862607 = (5 : ZMod 301801727) ^ (9431303 + 9431303 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 9431303 * (5 : ZMod 301801727) ^ 9431303) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 286717715 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 301801727) ^ 37725215 = 7180125 := by
        calc
          (5 : ZMod 301801727) ^ 37725215 = (5 : ZMod 301801727) ^ (18862607 + 18862607 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 18862607 * (5 : ZMod 301801727) ^ 18862607) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 7180125 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 301801727) ^ 75450431 = 7435336 := by
        calc
          (5 : ZMod 301801727) ^ 75450431 = (5 : ZMod 301801727) ^ (37725215 + 37725215 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 37725215 * (5 : ZMod 301801727) ^ 37725215) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 7435336 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 301801727) ^ 150900863 = 301801726 := by
        calc
          (5 : ZMod 301801727) ^ 150900863 = (5 : ZMod 301801727) ^ (75450431 + 75450431 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 75450431 * (5 : ZMod 301801727) ^ 75450431) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 301801726 := by rw [factor_0_26]; decide
      change (5 : ZMod 301801727) ^ 150900863 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (5 : ZMod 301801727) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 301801727) ^ 2 = 25 := by
        calc
          (5 : ZMod 301801727) ^ 2 = (5 : ZMod 301801727) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 1 * (5 : ZMod 301801727) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 301801727) ^ 5 = 3125 := by
        calc
          (5 : ZMod 301801727) ^ 5 = (5 : ZMod 301801727) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 2 * (5 : ZMod 301801727) ^ 2) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 301801727) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 301801727) ^ 11 = (5 : ZMod 301801727) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 5 * (5 : ZMod 301801727) ^ 5) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 301801727) ^ 23 = 67347636 := by
        calc
          (5 : ZMod 301801727) ^ 23 = (5 : ZMod 301801727) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 11 * (5 : ZMod 301801727) ^ 11) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 67347636 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 301801727) ^ 47 = 211048236 := by
        calc
          (5 : ZMod 301801727) ^ 47 = (5 : ZMod 301801727) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 23 * (5 : ZMod 301801727) ^ 23) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 211048236 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 301801727) ^ 94 = 138503378 := by
        calc
          (5 : ZMod 301801727) ^ 94 = (5 : ZMod 301801727) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 47 * (5 : ZMod 301801727) ^ 47 := by rw [pow_add]
          _ = 138503378 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 301801727) ^ 189 = 8543438 := by
        calc
          (5 : ZMod 301801727) ^ 189 = (5 : ZMod 301801727) ^ (94 + 94 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 94 * (5 : ZMod 301801727) ^ 94) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 8543438 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 301801727) ^ 379 = 38536559 := by
        calc
          (5 : ZMod 301801727) ^ 379 = (5 : ZMod 301801727) ^ (189 + 189 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 189 * (5 : ZMod 301801727) ^ 189) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 38536559 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 301801727) ^ 759 = 188627317 := by
        calc
          (5 : ZMod 301801727) ^ 759 = (5 : ZMod 301801727) ^ (379 + 379 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 379 * (5 : ZMod 301801727) ^ 379) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 188627317 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 301801727) ^ 1519 = 68962054 := by
        calc
          (5 : ZMod 301801727) ^ 1519 = (5 : ZMod 301801727) ^ (759 + 759 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 759 * (5 : ZMod 301801727) ^ 759) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 68962054 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 301801727) ^ 3038 = 138186619 := by
        calc
          (5 : ZMod 301801727) ^ 3038 = (5 : ZMod 301801727) ^ (1519 + 1519) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 1519 * (5 : ZMod 301801727) ^ 1519 := by rw [pow_add]
          _ = 138186619 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 301801727) ^ 6076 = 142235291 := by
        calc
          (5 : ZMod 301801727) ^ 6076 = (5 : ZMod 301801727) ^ (3038 + 3038) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 3038 * (5 : ZMod 301801727) ^ 3038 := by rw [pow_add]
          _ = 142235291 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 301801727) ^ 12153 = 145515685 := by
        calc
          (5 : ZMod 301801727) ^ 12153 = (5 : ZMod 301801727) ^ (6076 + 6076 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 6076 * (5 : ZMod 301801727) ^ 6076) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 145515685 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 301801727) ^ 24307 = 173097593 := by
        calc
          (5 : ZMod 301801727) ^ 24307 = (5 : ZMod 301801727) ^ (12153 + 12153 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 12153 * (5 : ZMod 301801727) ^ 12153) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 173097593 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 301801727) ^ 48614 = 236800105 := by
        calc
          (5 : ZMod 301801727) ^ 48614 = (5 : ZMod 301801727) ^ (24307 + 24307) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 24307 * (5 : ZMod 301801727) ^ 24307 := by rw [pow_add]
          _ = 236800105 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 301801727) ^ 97229 = 121336087 := by
        calc
          (5 : ZMod 301801727) ^ 97229 = (5 : ZMod 301801727) ^ (48614 + 48614 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 48614 * (5 : ZMod 301801727) ^ 48614) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 121336087 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 301801727) ^ 194459 = 179100365 := by
        calc
          (5 : ZMod 301801727) ^ 194459 = (5 : ZMod 301801727) ^ (97229 + 97229 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 97229 * (5 : ZMod 301801727) ^ 97229) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 179100365 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 301801727) ^ 388919 = 111288600 := by
        calc
          (5 : ZMod 301801727) ^ 388919 = (5 : ZMod 301801727) ^ (194459 + 194459 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 194459 * (5 : ZMod 301801727) ^ 194459) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 111288600 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 301801727) ^ 777839 = 163015065 := by
        calc
          (5 : ZMod 301801727) ^ 777839 = (5 : ZMod 301801727) ^ (388919 + 388919 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 388919 * (5 : ZMod 301801727) ^ 388919) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 163015065 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 301801727) ^ 1555679 = 133715251 := by
        calc
          (5 : ZMod 301801727) ^ 1555679 = (5 : ZMod 301801727) ^ (777839 + 777839 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 777839 * (5 : ZMod 301801727) ^ 777839) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 133715251 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 301801727) ^ 3111358 = 69796299 := by
        calc
          (5 : ZMod 301801727) ^ 3111358 = (5 : ZMod 301801727) ^ (1555679 + 1555679) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 1555679 * (5 : ZMod 301801727) ^ 1555679 := by rw [pow_add]
          _ = 69796299 := by rw [factor_1_20]; decide
      change (5 : ZMod 301801727) ^ 3111358 ≠ 1
      rw [factor_1_21]
      decide
    ·
      have factor_2_0 : (5 : ZMod 301801727) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 301801727) ^ 3 = 125 := by
        calc
          (5 : ZMod 301801727) ^ 3 = (5 : ZMod 301801727) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 1 * (5 : ZMod 301801727) ^ 1) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 301801727) ^ 6 = 15625 := by
        calc
          (5 : ZMod 301801727) ^ 6 = (5 : ZMod 301801727) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 3 * (5 : ZMod 301801727) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 301801727) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 301801727) ^ 12 = (5 : ZMod 301801727) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 6 * (5 : ZMod 301801727) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 301801727) ^ 24 = 34936453 := by
        calc
          (5 : ZMod 301801727) ^ 24 = (5 : ZMod 301801727) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 12 * (5 : ZMod 301801727) ^ 12 := by rw [pow_add]
          _ = 34936453 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 301801727) ^ 48 = 149835999 := by
        calc
          (5 : ZMod 301801727) ^ 48 = (5 : ZMod 301801727) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 24 * (5 : ZMod 301801727) ^ 24 := by rw [pow_add]
          _ = 149835999 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 301801727) ^ 97 = 110223811 := by
        calc
          (5 : ZMod 301801727) ^ 97 = (5 : ZMod 301801727) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = ((5 : ZMod 301801727) ^ 48 * (5 : ZMod 301801727) ^ 48) * (5 : ZMod 301801727) := by rw [pow_succ, pow_add]
          _ = 110223811 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 301801727) ^ 194 = 139691774 := by
        calc
          (5 : ZMod 301801727) ^ 194 = (5 : ZMod 301801727) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (5 : ZMod 301801727) ^ n) (by norm_num)
          _ = (5 : ZMod 301801727) ^ 97 * (5 : ZMod 301801727) ^ 97 := by rw [pow_add]
          _ = 139691774 := by rw [factor_2_6]; decide
      change (5 : ZMod 301801727) ^ 194 ≠ 1
      rw [factor_2_7]
      decide

#print axioms prime_lucas_301801727

end TotientTailPeriodKiller
end Erdos249257
