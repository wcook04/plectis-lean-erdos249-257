import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_62986559 : Nat.Prime 62986559 := by
  apply lucas_primality 62986559 (11 : ZMod 62986559)
  ·
      have fermat_0 : (11 : ZMod 62986559) ^ 1 = 11 := by norm_num
      have fermat_1 : (11 : ZMod 62986559) ^ 3 = 1331 := by
        calc
          (11 : ZMod 62986559) ^ 3 = (11 : ZMod 62986559) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 1 * (11 : ZMod 62986559) ^ 1) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [fermat_0]; decide
      have fermat_2 : (11 : ZMod 62986559) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 62986559) ^ 7 = (11 : ZMod 62986559) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 3 * (11 : ZMod 62986559) ^ 3) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [fermat_1]; decide
      have fermat_3 : (11 : ZMod 62986559) ^ 15 = 47167326 := by
        calc
          (11 : ZMod 62986559) ^ 15 = (11 : ZMod 62986559) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 7 * (11 : ZMod 62986559) ^ 7) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 47167326 := by rw [fermat_2]; decide
      have fermat_4 : (11 : ZMod 62986559) ^ 30 = 14338929 := by
        calc
          (11 : ZMod 62986559) ^ 30 = (11 : ZMod 62986559) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 15 * (11 : ZMod 62986559) ^ 15 := by rw [pow_add]
          _ = 14338929 := by rw [fermat_3]; decide
      have fermat_5 : (11 : ZMod 62986559) ^ 60 = 1866347 := by
        calc
          (11 : ZMod 62986559) ^ 60 = (11 : ZMod 62986559) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 30 * (11 : ZMod 62986559) ^ 30 := by rw [pow_add]
          _ = 1866347 := by rw [fermat_4]; decide
      have fermat_6 : (11 : ZMod 62986559) ^ 120 = 31425150 := by
        calc
          (11 : ZMod 62986559) ^ 120 = (11 : ZMod 62986559) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 60 * (11 : ZMod 62986559) ^ 60 := by rw [pow_add]
          _ = 31425150 := by rw [fermat_5]; decide
      have fermat_7 : (11 : ZMod 62986559) ^ 240 = 59356603 := by
        calc
          (11 : ZMod 62986559) ^ 240 = (11 : ZMod 62986559) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 120 * (11 : ZMod 62986559) ^ 120 := by rw [pow_add]
          _ = 59356603 := by rw [fermat_6]; decide
      have fermat_8 : (11 : ZMod 62986559) ^ 480 = 44365372 := by
        calc
          (11 : ZMod 62986559) ^ 480 = (11 : ZMod 62986559) ^ (240 + 240) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 240 * (11 : ZMod 62986559) ^ 240 := by rw [pow_add]
          _ = 44365372 := by rw [fermat_7]; decide
      have fermat_9 : (11 : ZMod 62986559) ^ 961 = 57756425 := by
        calc
          (11 : ZMod 62986559) ^ 961 = (11 : ZMod 62986559) ^ (480 + 480 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 480 * (11 : ZMod 62986559) ^ 480) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 57756425 := by rw [fermat_8]; decide
      have fermat_10 : (11 : ZMod 62986559) ^ 1922 = 57909523 := by
        calc
          (11 : ZMod 62986559) ^ 1922 = (11 : ZMod 62986559) ^ (961 + 961) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 961 * (11 : ZMod 62986559) ^ 961 := by rw [pow_add]
          _ = 57909523 := by rw [fermat_9]; decide
      have fermat_11 : (11 : ZMod 62986559) ^ 3844 = 53059490 := by
        calc
          (11 : ZMod 62986559) ^ 3844 = (11 : ZMod 62986559) ^ (1922 + 1922) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 1922 * (11 : ZMod 62986559) ^ 1922 := by rw [pow_add]
          _ = 53059490 := by rw [fermat_10]; decide
      have fermat_12 : (11 : ZMod 62986559) ^ 7688 = 7275808 := by
        calc
          (11 : ZMod 62986559) ^ 7688 = (11 : ZMod 62986559) ^ (3844 + 3844) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 3844 * (11 : ZMod 62986559) ^ 3844 := by rw [pow_add]
          _ = 7275808 := by rw [fermat_11]; decide
      have fermat_13 : (11 : ZMod 62986559) ^ 15377 = 23720591 := by
        calc
          (11 : ZMod 62986559) ^ 15377 = (11 : ZMod 62986559) ^ (7688 + 7688 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 7688 * (11 : ZMod 62986559) ^ 7688) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 23720591 := by rw [fermat_12]; decide
      have fermat_14 : (11 : ZMod 62986559) ^ 30755 = 51872801 := by
        calc
          (11 : ZMod 62986559) ^ 30755 = (11 : ZMod 62986559) ^ (15377 + 15377 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 15377 * (11 : ZMod 62986559) ^ 15377) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 51872801 := by rw [fermat_13]; decide
      have fermat_15 : (11 : ZMod 62986559) ^ 61510 = 45455067 := by
        calc
          (11 : ZMod 62986559) ^ 61510 = (11 : ZMod 62986559) ^ (30755 + 30755) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 30755 * (11 : ZMod 62986559) ^ 30755 := by rw [pow_add]
          _ = 45455067 := by rw [fermat_14]; decide
      have fermat_16 : (11 : ZMod 62986559) ^ 123020 = 30296447 := by
        calc
          (11 : ZMod 62986559) ^ 123020 = (11 : ZMod 62986559) ^ (61510 + 61510) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 61510 * (11 : ZMod 62986559) ^ 61510 := by rw [pow_add]
          _ = 30296447 := by rw [fermat_15]; decide
      have fermat_17 : (11 : ZMod 62986559) ^ 246041 = 6963775 := by
        calc
          (11 : ZMod 62986559) ^ 246041 = (11 : ZMod 62986559) ^ (123020 + 123020 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 123020 * (11 : ZMod 62986559) ^ 123020) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 6963775 := by rw [fermat_16]; decide
      have fermat_18 : (11 : ZMod 62986559) ^ 492082 = 54637817 := by
        calc
          (11 : ZMod 62986559) ^ 492082 = (11 : ZMod 62986559) ^ (246041 + 246041) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 246041 * (11 : ZMod 62986559) ^ 246041 := by rw [pow_add]
          _ = 54637817 := by rw [fermat_17]; decide
      have fermat_19 : (11 : ZMod 62986559) ^ 984164 = 62900692 := by
        calc
          (11 : ZMod 62986559) ^ 984164 = (11 : ZMod 62986559) ^ (492082 + 492082) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 492082 * (11 : ZMod 62986559) ^ 492082 := by rw [pow_add]
          _ = 62900692 := by rw [fermat_18]; decide
      have fermat_20 : (11 : ZMod 62986559) ^ 1968329 = 40857146 := by
        calc
          (11 : ZMod 62986559) ^ 1968329 = (11 : ZMod 62986559) ^ (984164 + 984164 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 984164 * (11 : ZMod 62986559) ^ 984164) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 40857146 := by rw [fermat_19]; decide
      have fermat_21 : (11 : ZMod 62986559) ^ 3936659 = 35008466 := by
        calc
          (11 : ZMod 62986559) ^ 3936659 = (11 : ZMod 62986559) ^ (1968329 + 1968329 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 1968329 * (11 : ZMod 62986559) ^ 1968329) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 35008466 := by rw [fermat_20]; decide
      have fermat_22 : (11 : ZMod 62986559) ^ 7873319 = 36686915 := by
        calc
          (11 : ZMod 62986559) ^ 7873319 = (11 : ZMod 62986559) ^ (3936659 + 3936659 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 3936659 * (11 : ZMod 62986559) ^ 3936659) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 36686915 := by rw [fermat_21]; decide
      have fermat_23 : (11 : ZMod 62986559) ^ 15746639 = 35870107 := by
        calc
          (11 : ZMod 62986559) ^ 15746639 = (11 : ZMod 62986559) ^ (7873319 + 7873319 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 7873319 * (11 : ZMod 62986559) ^ 7873319) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 35870107 := by rw [fermat_22]; decide
      have fermat_24 : (11 : ZMod 62986559) ^ 31493279 = 62986558 := by
        calc
          (11 : ZMod 62986559) ^ 31493279 = (11 : ZMod 62986559) ^ (15746639 + 15746639 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 15746639 * (11 : ZMod 62986559) ^ 15746639) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 62986558 := by rw [fermat_23]; decide
      have fermat_25 : (11 : ZMod 62986559) ^ 62986558 = 1 := by
        calc
          (11 : ZMod 62986559) ^ 62986558 = (11 : ZMod 62986559) ^ (31493279 + 31493279) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 31493279 * (11 : ZMod 62986559) ^ 31493279 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 2), (23, 1), (3793, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 2), (23, 1), (3793, 1)] : List FactorBlock).map factorBlockValue).prod = 62986559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (11 : ZMod 62986559) ^ 1 = 11 := by norm_num
      have factor_0_1 : (11 : ZMod 62986559) ^ 3 = 1331 := by
        calc
          (11 : ZMod 62986559) ^ 3 = (11 : ZMod 62986559) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 1 * (11 : ZMod 62986559) ^ 1) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_0_0]; decide
      have factor_0_2 : (11 : ZMod 62986559) ^ 7 = 19487171 := by
        calc
          (11 : ZMod 62986559) ^ 7 = (11 : ZMod 62986559) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 3 * (11 : ZMod 62986559) ^ 3) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 19487171 := by rw [factor_0_1]; decide
      have factor_0_3 : (11 : ZMod 62986559) ^ 15 = 47167326 := by
        calc
          (11 : ZMod 62986559) ^ 15 = (11 : ZMod 62986559) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 7 * (11 : ZMod 62986559) ^ 7) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 47167326 := by rw [factor_0_2]; decide
      have factor_0_4 : (11 : ZMod 62986559) ^ 30 = 14338929 := by
        calc
          (11 : ZMod 62986559) ^ 30 = (11 : ZMod 62986559) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 15 * (11 : ZMod 62986559) ^ 15 := by rw [pow_add]
          _ = 14338929 := by rw [factor_0_3]; decide
      have factor_0_5 : (11 : ZMod 62986559) ^ 60 = 1866347 := by
        calc
          (11 : ZMod 62986559) ^ 60 = (11 : ZMod 62986559) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 30 * (11 : ZMod 62986559) ^ 30 := by rw [pow_add]
          _ = 1866347 := by rw [factor_0_4]; decide
      have factor_0_6 : (11 : ZMod 62986559) ^ 120 = 31425150 := by
        calc
          (11 : ZMod 62986559) ^ 120 = (11 : ZMod 62986559) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 60 * (11 : ZMod 62986559) ^ 60 := by rw [pow_add]
          _ = 31425150 := by rw [factor_0_5]; decide
      have factor_0_7 : (11 : ZMod 62986559) ^ 240 = 59356603 := by
        calc
          (11 : ZMod 62986559) ^ 240 = (11 : ZMod 62986559) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 120 * (11 : ZMod 62986559) ^ 120 := by rw [pow_add]
          _ = 59356603 := by rw [factor_0_6]; decide
      have factor_0_8 : (11 : ZMod 62986559) ^ 480 = 44365372 := by
        calc
          (11 : ZMod 62986559) ^ 480 = (11 : ZMod 62986559) ^ (240 + 240) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 240 * (11 : ZMod 62986559) ^ 240 := by rw [pow_add]
          _ = 44365372 := by rw [factor_0_7]; decide
      have factor_0_9 : (11 : ZMod 62986559) ^ 961 = 57756425 := by
        calc
          (11 : ZMod 62986559) ^ 961 = (11 : ZMod 62986559) ^ (480 + 480 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 480 * (11 : ZMod 62986559) ^ 480) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 57756425 := by rw [factor_0_8]; decide
      have factor_0_10 : (11 : ZMod 62986559) ^ 1922 = 57909523 := by
        calc
          (11 : ZMod 62986559) ^ 1922 = (11 : ZMod 62986559) ^ (961 + 961) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 961 * (11 : ZMod 62986559) ^ 961 := by rw [pow_add]
          _ = 57909523 := by rw [factor_0_9]; decide
      have factor_0_11 : (11 : ZMod 62986559) ^ 3844 = 53059490 := by
        calc
          (11 : ZMod 62986559) ^ 3844 = (11 : ZMod 62986559) ^ (1922 + 1922) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 1922 * (11 : ZMod 62986559) ^ 1922 := by rw [pow_add]
          _ = 53059490 := by rw [factor_0_10]; decide
      have factor_0_12 : (11 : ZMod 62986559) ^ 7688 = 7275808 := by
        calc
          (11 : ZMod 62986559) ^ 7688 = (11 : ZMod 62986559) ^ (3844 + 3844) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 3844 * (11 : ZMod 62986559) ^ 3844 := by rw [pow_add]
          _ = 7275808 := by rw [factor_0_11]; decide
      have factor_0_13 : (11 : ZMod 62986559) ^ 15377 = 23720591 := by
        calc
          (11 : ZMod 62986559) ^ 15377 = (11 : ZMod 62986559) ^ (7688 + 7688 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 7688 * (11 : ZMod 62986559) ^ 7688) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 23720591 := by rw [factor_0_12]; decide
      have factor_0_14 : (11 : ZMod 62986559) ^ 30755 = 51872801 := by
        calc
          (11 : ZMod 62986559) ^ 30755 = (11 : ZMod 62986559) ^ (15377 + 15377 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 15377 * (11 : ZMod 62986559) ^ 15377) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 51872801 := by rw [factor_0_13]; decide
      have factor_0_15 : (11 : ZMod 62986559) ^ 61510 = 45455067 := by
        calc
          (11 : ZMod 62986559) ^ 61510 = (11 : ZMod 62986559) ^ (30755 + 30755) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 30755 * (11 : ZMod 62986559) ^ 30755 := by rw [pow_add]
          _ = 45455067 := by rw [factor_0_14]; decide
      have factor_0_16 : (11 : ZMod 62986559) ^ 123020 = 30296447 := by
        calc
          (11 : ZMod 62986559) ^ 123020 = (11 : ZMod 62986559) ^ (61510 + 61510) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 61510 * (11 : ZMod 62986559) ^ 61510 := by rw [pow_add]
          _ = 30296447 := by rw [factor_0_15]; decide
      have factor_0_17 : (11 : ZMod 62986559) ^ 246041 = 6963775 := by
        calc
          (11 : ZMod 62986559) ^ 246041 = (11 : ZMod 62986559) ^ (123020 + 123020 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 123020 * (11 : ZMod 62986559) ^ 123020) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 6963775 := by rw [factor_0_16]; decide
      have factor_0_18 : (11 : ZMod 62986559) ^ 492082 = 54637817 := by
        calc
          (11 : ZMod 62986559) ^ 492082 = (11 : ZMod 62986559) ^ (246041 + 246041) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 246041 * (11 : ZMod 62986559) ^ 246041 := by rw [pow_add]
          _ = 54637817 := by rw [factor_0_17]; decide
      have factor_0_19 : (11 : ZMod 62986559) ^ 984164 = 62900692 := by
        calc
          (11 : ZMod 62986559) ^ 984164 = (11 : ZMod 62986559) ^ (492082 + 492082) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 492082 * (11 : ZMod 62986559) ^ 492082 := by rw [pow_add]
          _ = 62900692 := by rw [factor_0_18]; decide
      have factor_0_20 : (11 : ZMod 62986559) ^ 1968329 = 40857146 := by
        calc
          (11 : ZMod 62986559) ^ 1968329 = (11 : ZMod 62986559) ^ (984164 + 984164 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 984164 * (11 : ZMod 62986559) ^ 984164) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 40857146 := by rw [factor_0_19]; decide
      have factor_0_21 : (11 : ZMod 62986559) ^ 3936659 = 35008466 := by
        calc
          (11 : ZMod 62986559) ^ 3936659 = (11 : ZMod 62986559) ^ (1968329 + 1968329 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 1968329 * (11 : ZMod 62986559) ^ 1968329) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 35008466 := by rw [factor_0_20]; decide
      have factor_0_22 : (11 : ZMod 62986559) ^ 7873319 = 36686915 := by
        calc
          (11 : ZMod 62986559) ^ 7873319 = (11 : ZMod 62986559) ^ (3936659 + 3936659 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 3936659 * (11 : ZMod 62986559) ^ 3936659) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 36686915 := by rw [factor_0_21]; decide
      have factor_0_23 : (11 : ZMod 62986559) ^ 15746639 = 35870107 := by
        calc
          (11 : ZMod 62986559) ^ 15746639 = (11 : ZMod 62986559) ^ (7873319 + 7873319 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 7873319 * (11 : ZMod 62986559) ^ 7873319) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 35870107 := by rw [factor_0_22]; decide
      have factor_0_24 : (11 : ZMod 62986559) ^ 31493279 = 62986558 := by
        calc
          (11 : ZMod 62986559) ^ 31493279 = (11 : ZMod 62986559) ^ (15746639 + 15746639 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 15746639 * (11 : ZMod 62986559) ^ 15746639) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 62986558 := by rw [factor_0_23]; decide
      change (11 : ZMod 62986559) ^ 31493279 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (11 : ZMod 62986559) ^ 1 = 11 := by norm_num
      have factor_1_1 : (11 : ZMod 62986559) ^ 3 = 1331 := by
        calc
          (11 : ZMod 62986559) ^ 3 = (11 : ZMod 62986559) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 1 * (11 : ZMod 62986559) ^ 1) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 1331 := by rw [factor_1_0]; decide
      have factor_1_2 : (11 : ZMod 62986559) ^ 6 = 1771561 := by
        calc
          (11 : ZMod 62986559) ^ 6 = (11 : ZMod 62986559) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 3 * (11 : ZMod 62986559) ^ 3 := by rw [pow_add]
          _ = 1771561 := by rw [factor_1_1]; decide
      have factor_1_3 : (11 : ZMod 62986559) ^ 12 = 60087987 := by
        calc
          (11 : ZMod 62986559) ^ 12 = (11 : ZMod 62986559) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 6 * (11 : ZMod 62986559) ^ 6 := by rw [pow_add]
          _ = 60087987 := by rw [factor_1_2]; decide
      have factor_1_4 : (11 : ZMod 62986559) ^ 25 = 60728063 := by
        calc
          (11 : ZMod 62986559) ^ 25 = (11 : ZMod 62986559) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 12 * (11 : ZMod 62986559) ^ 12) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 60728063 := by rw [factor_1_3]; decide
      have factor_1_5 : (11 : ZMod 62986559) ^ 50 = 26661078 := by
        calc
          (11 : ZMod 62986559) ^ 50 = (11 : ZMod 62986559) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 25 * (11 : ZMod 62986559) ^ 25 := by rw [pow_add]
          _ = 26661078 := by rw [factor_1_4]; decide
      have factor_1_6 : (11 : ZMod 62986559) ^ 101 = 50781388 := by
        calc
          (11 : ZMod 62986559) ^ 101 = (11 : ZMod 62986559) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 50 * (11 : ZMod 62986559) ^ 50) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 50781388 := by rw [factor_1_5]; decide
      have factor_1_7 : (11 : ZMod 62986559) ^ 202 = 26735968 := by
        calc
          (11 : ZMod 62986559) ^ 202 = (11 : ZMod 62986559) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 101 * (11 : ZMod 62986559) ^ 101 := by rw [pow_add]
          _ = 26735968 := by rw [factor_1_6]; decide
      have factor_1_8 : (11 : ZMod 62986559) ^ 404 = 13007587 := by
        calc
          (11 : ZMod 62986559) ^ 404 = (11 : ZMod 62986559) ^ (202 + 202) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 202 * (11 : ZMod 62986559) ^ 202 := by rw [pow_add]
          _ = 13007587 := by rw [factor_1_7]; decide
      have factor_1_9 : (11 : ZMod 62986559) ^ 809 = 20170872 := by
        calc
          (11 : ZMod 62986559) ^ 809 = (11 : ZMod 62986559) ^ (404 + 404 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 404 * (11 : ZMod 62986559) ^ 404) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 20170872 := by rw [factor_1_8]; decide
      have factor_1_10 : (11 : ZMod 62986559) ^ 1618 = 5890642 := by
        calc
          (11 : ZMod 62986559) ^ 1618 = (11 : ZMod 62986559) ^ (809 + 809) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 809 * (11 : ZMod 62986559) ^ 809 := by rw [pow_add]
          _ = 5890642 := by rw [factor_1_9]; decide
      have factor_1_11 : (11 : ZMod 62986559) ^ 3237 = 14869928 := by
        calc
          (11 : ZMod 62986559) ^ 3237 = (11 : ZMod 62986559) ^ (1618 + 1618 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 1618 * (11 : ZMod 62986559) ^ 1618) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 14869928 := by rw [factor_1_10]; decide
      have factor_1_12 : (11 : ZMod 62986559) ^ 6474 = 2449771 := by
        calc
          (11 : ZMod 62986559) ^ 6474 = (11 : ZMod 62986559) ^ (3237 + 3237) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 3237 * (11 : ZMod 62986559) ^ 3237 := by rw [pow_add]
          _ = 2449771 := by rw [factor_1_11]; decide
      have factor_1_13 : (11 : ZMod 62986559) ^ 12949 = 15760454 := by
        calc
          (11 : ZMod 62986559) ^ 12949 = (11 : ZMod 62986559) ^ (6474 + 6474 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 6474 * (11 : ZMod 62986559) ^ 6474) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 15760454 := by rw [factor_1_12]; decide
      have factor_1_14 : (11 : ZMod 62986559) ^ 25899 = 928787 := by
        calc
          (11 : ZMod 62986559) ^ 25899 = (11 : ZMod 62986559) ^ (12949 + 12949 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 12949 * (11 : ZMod 62986559) ^ 12949) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 928787 := by rw [factor_1_13]; decide
      have factor_1_15 : (11 : ZMod 62986559) ^ 51798 = 44365864 := by
        calc
          (11 : ZMod 62986559) ^ 51798 = (11 : ZMod 62986559) ^ (25899 + 25899) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 25899 * (11 : ZMod 62986559) ^ 25899 := by rw [pow_add]
          _ = 44365864 := by rw [factor_1_14]; decide
      have factor_1_16 : (11 : ZMod 62986559) ^ 103596 = 45689614 := by
        calc
          (11 : ZMod 62986559) ^ 103596 = (11 : ZMod 62986559) ^ (51798 + 51798) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 51798 * (11 : ZMod 62986559) ^ 51798 := by rw [pow_add]
          _ = 45689614 := by rw [factor_1_15]; decide
      have factor_1_17 : (11 : ZMod 62986559) ^ 207192 = 40679795 := by
        calc
          (11 : ZMod 62986559) ^ 207192 = (11 : ZMod 62986559) ^ (103596 + 103596) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 103596 * (11 : ZMod 62986559) ^ 103596 := by rw [pow_add]
          _ = 40679795 := by rw [factor_1_16]; decide
      have factor_1_18 : (11 : ZMod 62986559) ^ 414385 = 60635809 := by
        calc
          (11 : ZMod 62986559) ^ 414385 = (11 : ZMod 62986559) ^ (207192 + 207192 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 207192 * (11 : ZMod 62986559) ^ 207192) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 60635809 := by rw [factor_1_17]; decide
      have factor_1_19 : (11 : ZMod 62986559) ^ 828770 = 25781753 := by
        calc
          (11 : ZMod 62986559) ^ 828770 = (11 : ZMod 62986559) ^ (414385 + 414385) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 414385 * (11 : ZMod 62986559) ^ 414385 := by rw [pow_add]
          _ = 25781753 := by rw [factor_1_18]; decide
      have factor_1_20 : (11 : ZMod 62986559) ^ 1657541 = 48703343 := by
        calc
          (11 : ZMod 62986559) ^ 1657541 = (11 : ZMod 62986559) ^ (828770 + 828770 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 828770 * (11 : ZMod 62986559) ^ 828770) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 48703343 := by rw [factor_1_19]; decide
      have factor_1_21 : (11 : ZMod 62986559) ^ 3315082 = 7016165 := by
        calc
          (11 : ZMod 62986559) ^ 3315082 = (11 : ZMod 62986559) ^ (1657541 + 1657541) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 1657541 * (11 : ZMod 62986559) ^ 1657541 := by rw [pow_add]
          _ = 7016165 := by rw [factor_1_20]; decide
      change (11 : ZMod 62986559) ^ 3315082 ≠ 1
      rw [factor_1_21]
      decide
    ·
      have factor_2_0 : (11 : ZMod 62986559) ^ 1 = 11 := by norm_num
      have factor_2_1 : (11 : ZMod 62986559) ^ 2 = 121 := by
        calc
          (11 : ZMod 62986559) ^ 2 = (11 : ZMod 62986559) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 1 * (11 : ZMod 62986559) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_2_0]; decide
      have factor_2_2 : (11 : ZMod 62986559) ^ 5 = 161051 := by
        calc
          (11 : ZMod 62986559) ^ 5 = (11 : ZMod 62986559) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 2 * (11 : ZMod 62986559) ^ 2) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 161051 := by rw [factor_2_1]; decide
      have factor_2_3 : (11 : ZMod 62986559) ^ 10 = 49948852 := by
        calc
          (11 : ZMod 62986559) ^ 10 = (11 : ZMod 62986559) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 5 * (11 : ZMod 62986559) ^ 5 := by rw [pow_add]
          _ = 49948852 := by rw [factor_2_2]; decide
      have factor_2_4 : (11 : ZMod 62986559) ^ 20 = 40031108 := by
        calc
          (11 : ZMod 62986559) ^ 20 = (11 : ZMod 62986559) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 10 * (11 : ZMod 62986559) ^ 10 := by rw [pow_add]
          _ = 40031108 := by rw [factor_2_3]; decide
      have factor_2_5 : (11 : ZMod 62986559) ^ 41 = 36054984 := by
        calc
          (11 : ZMod 62986559) ^ 41 = (11 : ZMod 62986559) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 20 * (11 : ZMod 62986559) ^ 20) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 36054984 := by rw [factor_2_4]; decide
      have factor_2_6 : (11 : ZMod 62986559) ^ 83 = 23831921 := by
        calc
          (11 : ZMod 62986559) ^ 83 = (11 : ZMod 62986559) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 41 * (11 : ZMod 62986559) ^ 41) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 23831921 := by rw [factor_2_5]; decide
      have factor_2_7 : (11 : ZMod 62986559) ^ 167 = 61519911 := by
        calc
          (11 : ZMod 62986559) ^ 167 = (11 : ZMod 62986559) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 83 * (11 : ZMod 62986559) ^ 83) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 61519911 := by rw [factor_2_6]; decide
      have factor_2_8 : (11 : ZMod 62986559) ^ 334 = 2379495 := by
        calc
          (11 : ZMod 62986559) ^ 334 = (11 : ZMod 62986559) ^ (167 + 167) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 167 * (11 : ZMod 62986559) ^ 167 := by rw [pow_add]
          _ = 2379495 := by rw [factor_2_7]; decide
      have factor_2_9 : (11 : ZMod 62986559) ^ 668 = 8693397 := by
        calc
          (11 : ZMod 62986559) ^ 668 = (11 : ZMod 62986559) ^ (334 + 334) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 334 * (11 : ZMod 62986559) ^ 334 := by rw [pow_add]
          _ = 8693397 := by rw [factor_2_8]; decide
      have factor_2_10 : (11 : ZMod 62986559) ^ 1337 = 15125056 := by
        calc
          (11 : ZMod 62986559) ^ 1337 = (11 : ZMod 62986559) ^ (668 + 668 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 668 * (11 : ZMod 62986559) ^ 668) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 15125056 := by rw [factor_2_9]; decide
      have factor_2_11 : (11 : ZMod 62986559) ^ 2674 = 10742018 := by
        calc
          (11 : ZMod 62986559) ^ 2674 = (11 : ZMod 62986559) ^ (1337 + 1337) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 1337 * (11 : ZMod 62986559) ^ 1337 := by rw [pow_add]
          _ = 10742018 := by rw [factor_2_10]; decide
      have factor_2_12 : (11 : ZMod 62986559) ^ 5348 = 15530237 := by
        calc
          (11 : ZMod 62986559) ^ 5348 = (11 : ZMod 62986559) ^ (2674 + 2674) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 2674 * (11 : ZMod 62986559) ^ 2674 := by rw [pow_add]
          _ = 15530237 := by rw [factor_2_11]; decide
      have factor_2_13 : (11 : ZMod 62986559) ^ 10697 = 39382761 := by
        calc
          (11 : ZMod 62986559) ^ 10697 = (11 : ZMod 62986559) ^ (5348 + 5348 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 5348 * (11 : ZMod 62986559) ^ 5348) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 39382761 := by rw [factor_2_12]; decide
      have factor_2_14 : (11 : ZMod 62986559) ^ 21394 = 49602651 := by
        calc
          (11 : ZMod 62986559) ^ 21394 = (11 : ZMod 62986559) ^ (10697 + 10697) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 10697 * (11 : ZMod 62986559) ^ 10697 := by rw [pow_add]
          _ = 49602651 := by rw [factor_2_13]; decide
      have factor_2_15 : (11 : ZMod 62986559) ^ 42789 = 8897869 := by
        calc
          (11 : ZMod 62986559) ^ 42789 = (11 : ZMod 62986559) ^ (21394 + 21394 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 21394 * (11 : ZMod 62986559) ^ 21394) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 8897869 := by rw [factor_2_14]; decide
      have factor_2_16 : (11 : ZMod 62986559) ^ 85579 = 9088216 := by
        calc
          (11 : ZMod 62986559) ^ 85579 = (11 : ZMod 62986559) ^ (42789 + 42789 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 42789 * (11 : ZMod 62986559) ^ 42789) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 9088216 := by rw [factor_2_15]; decide
      have factor_2_17 : (11 : ZMod 62986559) ^ 171159 = 41971679 := by
        calc
          (11 : ZMod 62986559) ^ 171159 = (11 : ZMod 62986559) ^ (85579 + 85579 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 85579 * (11 : ZMod 62986559) ^ 85579) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 41971679 := by rw [factor_2_16]; decide
      have factor_2_18 : (11 : ZMod 62986559) ^ 342318 = 24897179 := by
        calc
          (11 : ZMod 62986559) ^ 342318 = (11 : ZMod 62986559) ^ (171159 + 171159) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 171159 * (11 : ZMod 62986559) ^ 171159 := by rw [pow_add]
          _ = 24897179 := by rw [factor_2_17]; decide
      have factor_2_19 : (11 : ZMod 62986559) ^ 684636 = 25044459 := by
        calc
          (11 : ZMod 62986559) ^ 684636 = (11 : ZMod 62986559) ^ (342318 + 342318) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 342318 * (11 : ZMod 62986559) ^ 342318 := by rw [pow_add]
          _ = 25044459 := by rw [factor_2_18]; decide
      have factor_2_20 : (11 : ZMod 62986559) ^ 1369273 = 25083844 := by
        calc
          (11 : ZMod 62986559) ^ 1369273 = (11 : ZMod 62986559) ^ (684636 + 684636 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 684636 * (11 : ZMod 62986559) ^ 684636) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 25083844 := by rw [factor_2_19]; decide
      have factor_2_21 : (11 : ZMod 62986559) ^ 2738546 = 37610556 := by
        calc
          (11 : ZMod 62986559) ^ 2738546 = (11 : ZMod 62986559) ^ (1369273 + 1369273) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 1369273 * (11 : ZMod 62986559) ^ 1369273 := by rw [pow_add]
          _ = 37610556 := by rw [factor_2_20]; decide
      change (11 : ZMod 62986559) ^ 2738546 ≠ 1
      rw [factor_2_21]
      decide
    ·
      have factor_3_0 : (11 : ZMod 62986559) ^ 1 = 11 := by norm_num
      have factor_3_1 : (11 : ZMod 62986559) ^ 2 = 121 := by
        calc
          (11 : ZMod 62986559) ^ 2 = (11 : ZMod 62986559) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 1 * (11 : ZMod 62986559) ^ 1 := by rw [pow_add]
          _ = 121 := by rw [factor_3_0]; decide
      have factor_3_2 : (11 : ZMod 62986559) ^ 4 = 14641 := by
        calc
          (11 : ZMod 62986559) ^ 4 = (11 : ZMod 62986559) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 2 * (11 : ZMod 62986559) ^ 2 := by rw [pow_add]
          _ = 14641 := by rw [factor_3_1]; decide
      have factor_3_3 : (11 : ZMod 62986559) ^ 8 = 25399204 := by
        calc
          (11 : ZMod 62986559) ^ 8 = (11 : ZMod 62986559) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 4 * (11 : ZMod 62986559) ^ 4 := by rw [pow_add]
          _ = 25399204 := by rw [factor_3_2]; decide
      have factor_3_4 : (11 : ZMod 62986559) ^ 16 = 14948114 := by
        calc
          (11 : ZMod 62986559) ^ 16 = (11 : ZMod 62986559) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 8 * (11 : ZMod 62986559) ^ 8 := by rw [pow_add]
          _ = 14948114 := by rw [factor_3_3]; decide
      have factor_3_5 : (11 : ZMod 62986559) ^ 32 = 34373316 := by
        calc
          (11 : ZMod 62986559) ^ 32 = (11 : ZMod 62986559) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 16 * (11 : ZMod 62986559) ^ 16 := by rw [pow_add]
          _ = 34373316 := by rw [factor_3_4]; decide
      have factor_3_6 : (11 : ZMod 62986559) ^ 64 = 52006380 := by
        calc
          (11 : ZMod 62986559) ^ 64 = (11 : ZMod 62986559) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 32 * (11 : ZMod 62986559) ^ 32 := by rw [pow_add]
          _ = 52006380 := by rw [factor_3_5]; decide
      have factor_3_7 : (11 : ZMod 62986559) ^ 129 = 4317938 := by
        calc
          (11 : ZMod 62986559) ^ 129 = (11 : ZMod 62986559) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 64 * (11 : ZMod 62986559) ^ 64) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 4317938 := by rw [factor_3_6]; decide
      have factor_3_8 : (11 : ZMod 62986559) ^ 259 = 2516943 := by
        calc
          (11 : ZMod 62986559) ^ 259 = (11 : ZMod 62986559) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 129 * (11 : ZMod 62986559) ^ 129) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 2516943 := by rw [factor_3_7]; decide
      have factor_3_9 : (11 : ZMod 62986559) ^ 518 = 2920706 := by
        calc
          (11 : ZMod 62986559) ^ 518 = (11 : ZMod 62986559) ^ (259 + 259) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 259 * (11 : ZMod 62986559) ^ 259 := by rw [pow_add]
          _ = 2920706 := by rw [factor_3_8]; decide
      have factor_3_10 : (11 : ZMod 62986559) ^ 1037 = 20975130 := by
        calc
          (11 : ZMod 62986559) ^ 1037 = (11 : ZMod 62986559) ^ (518 + 518 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 518 * (11 : ZMod 62986559) ^ 518) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 20975130 := by rw [factor_3_9]; decide
      have factor_3_11 : (11 : ZMod 62986559) ^ 2075 = 31092820 := by
        calc
          (11 : ZMod 62986559) ^ 2075 = (11 : ZMod 62986559) ^ (1037 + 1037 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 1037 * (11 : ZMod 62986559) ^ 1037) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 31092820 := by rw [factor_3_10]; decide
      have factor_3_12 : (11 : ZMod 62986559) ^ 4151 = 28604549 := by
        calc
          (11 : ZMod 62986559) ^ 4151 = (11 : ZMod 62986559) ^ (2075 + 2075 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 2075 * (11 : ZMod 62986559) ^ 2075) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 28604549 := by rw [factor_3_11]; decide
      have factor_3_13 : (11 : ZMod 62986559) ^ 8303 = 59170705 := by
        calc
          (11 : ZMod 62986559) ^ 8303 = (11 : ZMod 62986559) ^ (4151 + 4151 + 1) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = ((11 : ZMod 62986559) ^ 4151 * (11 : ZMod 62986559) ^ 4151) * (11 : ZMod 62986559) := by rw [pow_succ, pow_add]
          _ = 59170705 := by rw [factor_3_12]; decide
      have factor_3_14 : (11 : ZMod 62986559) ^ 16606 = 12932168 := by
        calc
          (11 : ZMod 62986559) ^ 16606 = (11 : ZMod 62986559) ^ (8303 + 8303) :=
            congrArg (fun n : ℕ => (11 : ZMod 62986559) ^ n) (by norm_num)
          _ = (11 : ZMod 62986559) ^ 8303 * (11 : ZMod 62986559) ^ 8303 := by rw [pow_add]
          _ = 12932168 := by rw [factor_3_13]; decide
      change (11 : ZMod 62986559) ^ 16606 ≠ 1
      rw [factor_3_14]
      decide

#print axioms prime_lucas_62986559

end TotientTailPeriodKiller
end Erdos249257
