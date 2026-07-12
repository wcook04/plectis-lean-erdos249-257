import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_254963281 : Nat.Prime 254963281 := by
  apply lucas_primality 254963281 (7 : ZMod 254963281)
  ·
      have fermat_0 : (7 : ZMod 254963281) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 254963281) ^ 3 = 343 := by
        calc
          (7 : ZMod 254963281) ^ 3 = (7 : ZMod 254963281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1 * (7 : ZMod 254963281) ^ 1) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 254963281) ^ 7 = 823543 := by
        calc
          (7 : ZMod 254963281) ^ 7 = (7 : ZMod 254963281) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 3 * (7 : ZMod 254963281) ^ 3) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 254963281) ^ 15 = 145217723 := by
        calc
          (7 : ZMod 254963281) ^ 15 = (7 : ZMod 254963281) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 7 * (7 : ZMod 254963281) ^ 7) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 145217723 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 254963281) ^ 30 = 216837087 := by
        calc
          (7 : ZMod 254963281) ^ 30 = (7 : ZMod 254963281) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 15 * (7 : ZMod 254963281) ^ 15 := by rw [pow_add]
          _ = 216837087 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 254963281) ^ 60 = 67720477 := by
        calc
          (7 : ZMod 254963281) ^ 60 = (7 : ZMod 254963281) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 30 * (7 : ZMod 254963281) ^ 30 := by rw [pow_add]
          _ = 67720477 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 254963281) ^ 121 = 47098967 := by
        calc
          (7 : ZMod 254963281) ^ 121 = (7 : ZMod 254963281) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 60 * (7 : ZMod 254963281) ^ 60) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 47098967 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 254963281) ^ 243 = 27586155 := by
        calc
          (7 : ZMod 254963281) ^ 243 = (7 : ZMod 254963281) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 121 * (7 : ZMod 254963281) ^ 121) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 27586155 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 254963281) ^ 486 = 158874738 := by
        calc
          (7 : ZMod 254963281) ^ 486 = (7 : ZMod 254963281) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 243 * (7 : ZMod 254963281) ^ 243 := by rw [pow_add]
          _ = 158874738 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 254963281) ^ 972 = 109277840 := by
        calc
          (7 : ZMod 254963281) ^ 972 = (7 : ZMod 254963281) ^ (486 + 486) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 486 * (7 : ZMod 254963281) ^ 486 := by rw [pow_add]
          _ = 109277840 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 254963281) ^ 1945 = 250607852 := by
        calc
          (7 : ZMod 254963281) ^ 1945 = (7 : ZMod 254963281) ^ (972 + 972 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 972 * (7 : ZMod 254963281) ^ 972) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 250607852 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 254963281) ^ 3890 = 238704360 := by
        calc
          (7 : ZMod 254963281) ^ 3890 = (7 : ZMod 254963281) ^ (1945 + 1945) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1945 * (7 : ZMod 254963281) ^ 1945 := by rw [pow_add]
          _ = 238704360 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 254963281) ^ 7780 = 208261416 := by
        calc
          (7 : ZMod 254963281) ^ 7780 = (7 : ZMod 254963281) ^ (3890 + 3890) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3890 * (7 : ZMod 254963281) ^ 3890 := by rw [pow_add]
          _ = 208261416 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 254963281) ^ 15561 = 15795162 := by
        calc
          (7 : ZMod 254963281) ^ 15561 = (7 : ZMod 254963281) ^ (7780 + 7780 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 7780 * (7 : ZMod 254963281) ^ 7780) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 15795162 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 254963281) ^ 31123 = 250615496 := by
        calc
          (7 : ZMod 254963281) ^ 31123 = (7 : ZMod 254963281) ^ (15561 + 15561 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 15561 * (7 : ZMod 254963281) ^ 15561) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 250615496 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 254963281) ^ 62246 = 1789604 := by
        calc
          (7 : ZMod 254963281) ^ 62246 = (7 : ZMod 254963281) ^ (31123 + 31123) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 31123 * (7 : ZMod 254963281) ^ 31123 := by rw [pow_add]
          _ = 1789604 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 254963281) ^ 124493 = 111002663 := by
        calc
          (7 : ZMod 254963281) ^ 124493 = (7 : ZMod 254963281) ^ (62246 + 62246 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 62246 * (7 : ZMod 254963281) ^ 62246) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 111002663 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 254963281) ^ 248987 = 115970913 := by
        calc
          (7 : ZMod 254963281) ^ 248987 = (7 : ZMod 254963281) ^ (124493 + 124493 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 124493 * (7 : ZMod 254963281) ^ 124493) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 115970913 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 254963281) ^ 497975 = 109208162 := by
        calc
          (7 : ZMod 254963281) ^ 497975 = (7 : ZMod 254963281) ^ (248987 + 248987 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 248987 * (7 : ZMod 254963281) ^ 248987) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 109208162 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 254963281) ^ 995950 = 152815624 := by
        calc
          (7 : ZMod 254963281) ^ 995950 = (7 : ZMod 254963281) ^ (497975 + 497975) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 497975 * (7 : ZMod 254963281) ^ 497975 := by rw [pow_add]
          _ = 152815624 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 254963281) ^ 1991900 = 2764425 := by
        calc
          (7 : ZMod 254963281) ^ 1991900 = (7 : ZMod 254963281) ^ (995950 + 995950) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 995950 * (7 : ZMod 254963281) ^ 995950 := by rw [pow_add]
          _ = 2764425 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 254963281) ^ 3983801 = 218114484 := by
        calc
          (7 : ZMod 254963281) ^ 3983801 = (7 : ZMod 254963281) ^ (1991900 + 1991900 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1991900 * (7 : ZMod 254963281) ^ 1991900) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 218114484 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 254963281) ^ 7967602 = 116237204 := by
        calc
          (7 : ZMod 254963281) ^ 7967602 = (7 : ZMod 254963281) ^ (3983801 + 3983801) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3983801 * (7 : ZMod 254963281) ^ 3983801 := by rw [pow_add]
          _ = 116237204 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 254963281) ^ 15935205 = 97888097 := by
        calc
          (7 : ZMod 254963281) ^ 15935205 = (7 : ZMod 254963281) ^ (7967602 + 7967602 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 7967602 * (7 : ZMod 254963281) ^ 7967602) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 97888097 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 254963281) ^ 31870410 = 44862895 := by
        calc
          (7 : ZMod 254963281) ^ 31870410 = (7 : ZMod 254963281) ^ (15935205 + 15935205) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 15935205 * (7 : ZMod 254963281) ^ 15935205 := by rw [pow_add]
          _ = 44862895 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 254963281) ^ 63740820 = 227420149 := by
        calc
          (7 : ZMod 254963281) ^ 63740820 = (7 : ZMod 254963281) ^ (31870410 + 31870410) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 31870410 * (7 : ZMod 254963281) ^ 31870410 := by rw [pow_add]
          _ = 227420149 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 254963281) ^ 127481640 = 254963280 := by
        calc
          (7 : ZMod 254963281) ^ 127481640 = (7 : ZMod 254963281) ^ (63740820 + 63740820) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 63740820 * (7 : ZMod 254963281) ^ 63740820 := by rw [pow_add]
          _ = 254963280 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 254963281) ^ 254963280 = 1 := by
        calc
          (7 : ZMod 254963281) ^ 254963280 = (7 : ZMod 254963281) ^ (127481640 + 127481640) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 127481640 * (7 : ZMod 254963281) ^ 127481640 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 254963281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 254963281) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 254963281) ^ 3 = 343 := by
        calc
          (7 : ZMod 254963281) ^ 3 = (7 : ZMod 254963281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1 * (7 : ZMod 254963281) ^ 1) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 254963281) ^ 7 = 823543 := by
        calc
          (7 : ZMod 254963281) ^ 7 = (7 : ZMod 254963281) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 3 * (7 : ZMod 254963281) ^ 3) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 254963281) ^ 15 = 145217723 := by
        calc
          (7 : ZMod 254963281) ^ 15 = (7 : ZMod 254963281) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 7 * (7 : ZMod 254963281) ^ 7) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 145217723 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 254963281) ^ 30 = 216837087 := by
        calc
          (7 : ZMod 254963281) ^ 30 = (7 : ZMod 254963281) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 15 * (7 : ZMod 254963281) ^ 15 := by rw [pow_add]
          _ = 216837087 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 254963281) ^ 60 = 67720477 := by
        calc
          (7 : ZMod 254963281) ^ 60 = (7 : ZMod 254963281) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 30 * (7 : ZMod 254963281) ^ 30 := by rw [pow_add]
          _ = 67720477 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 254963281) ^ 121 = 47098967 := by
        calc
          (7 : ZMod 254963281) ^ 121 = (7 : ZMod 254963281) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 60 * (7 : ZMod 254963281) ^ 60) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 47098967 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 254963281) ^ 243 = 27586155 := by
        calc
          (7 : ZMod 254963281) ^ 243 = (7 : ZMod 254963281) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 121 * (7 : ZMod 254963281) ^ 121) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 27586155 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 254963281) ^ 486 = 158874738 := by
        calc
          (7 : ZMod 254963281) ^ 486 = (7 : ZMod 254963281) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 243 * (7 : ZMod 254963281) ^ 243 := by rw [pow_add]
          _ = 158874738 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 254963281) ^ 972 = 109277840 := by
        calc
          (7 : ZMod 254963281) ^ 972 = (7 : ZMod 254963281) ^ (486 + 486) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 486 * (7 : ZMod 254963281) ^ 486 := by rw [pow_add]
          _ = 109277840 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 254963281) ^ 1945 = 250607852 := by
        calc
          (7 : ZMod 254963281) ^ 1945 = (7 : ZMod 254963281) ^ (972 + 972 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 972 * (7 : ZMod 254963281) ^ 972) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 250607852 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 254963281) ^ 3890 = 238704360 := by
        calc
          (7 : ZMod 254963281) ^ 3890 = (7 : ZMod 254963281) ^ (1945 + 1945) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1945 * (7 : ZMod 254963281) ^ 1945 := by rw [pow_add]
          _ = 238704360 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 254963281) ^ 7780 = 208261416 := by
        calc
          (7 : ZMod 254963281) ^ 7780 = (7 : ZMod 254963281) ^ (3890 + 3890) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3890 * (7 : ZMod 254963281) ^ 3890 := by rw [pow_add]
          _ = 208261416 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 254963281) ^ 15561 = 15795162 := by
        calc
          (7 : ZMod 254963281) ^ 15561 = (7 : ZMod 254963281) ^ (7780 + 7780 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 7780 * (7 : ZMod 254963281) ^ 7780) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 15795162 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 254963281) ^ 31123 = 250615496 := by
        calc
          (7 : ZMod 254963281) ^ 31123 = (7 : ZMod 254963281) ^ (15561 + 15561 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 15561 * (7 : ZMod 254963281) ^ 15561) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 250615496 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 254963281) ^ 62246 = 1789604 := by
        calc
          (7 : ZMod 254963281) ^ 62246 = (7 : ZMod 254963281) ^ (31123 + 31123) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 31123 * (7 : ZMod 254963281) ^ 31123 := by rw [pow_add]
          _ = 1789604 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 254963281) ^ 124493 = 111002663 := by
        calc
          (7 : ZMod 254963281) ^ 124493 = (7 : ZMod 254963281) ^ (62246 + 62246 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 62246 * (7 : ZMod 254963281) ^ 62246) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 111002663 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 254963281) ^ 248987 = 115970913 := by
        calc
          (7 : ZMod 254963281) ^ 248987 = (7 : ZMod 254963281) ^ (124493 + 124493 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 124493 * (7 : ZMod 254963281) ^ 124493) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 115970913 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 254963281) ^ 497975 = 109208162 := by
        calc
          (7 : ZMod 254963281) ^ 497975 = (7 : ZMod 254963281) ^ (248987 + 248987 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 248987 * (7 : ZMod 254963281) ^ 248987) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 109208162 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 254963281) ^ 995950 = 152815624 := by
        calc
          (7 : ZMod 254963281) ^ 995950 = (7 : ZMod 254963281) ^ (497975 + 497975) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 497975 * (7 : ZMod 254963281) ^ 497975 := by rw [pow_add]
          _ = 152815624 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 254963281) ^ 1991900 = 2764425 := by
        calc
          (7 : ZMod 254963281) ^ 1991900 = (7 : ZMod 254963281) ^ (995950 + 995950) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 995950 * (7 : ZMod 254963281) ^ 995950 := by rw [pow_add]
          _ = 2764425 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 254963281) ^ 3983801 = 218114484 := by
        calc
          (7 : ZMod 254963281) ^ 3983801 = (7 : ZMod 254963281) ^ (1991900 + 1991900 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1991900 * (7 : ZMod 254963281) ^ 1991900) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 218114484 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 254963281) ^ 7967602 = 116237204 := by
        calc
          (7 : ZMod 254963281) ^ 7967602 = (7 : ZMod 254963281) ^ (3983801 + 3983801) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3983801 * (7 : ZMod 254963281) ^ 3983801 := by rw [pow_add]
          _ = 116237204 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 254963281) ^ 15935205 = 97888097 := by
        calc
          (7 : ZMod 254963281) ^ 15935205 = (7 : ZMod 254963281) ^ (7967602 + 7967602 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 7967602 * (7 : ZMod 254963281) ^ 7967602) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 97888097 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 254963281) ^ 31870410 = 44862895 := by
        calc
          (7 : ZMod 254963281) ^ 31870410 = (7 : ZMod 254963281) ^ (15935205 + 15935205) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 15935205 * (7 : ZMod 254963281) ^ 15935205 := by rw [pow_add]
          _ = 44862895 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 254963281) ^ 63740820 = 227420149 := by
        calc
          (7 : ZMod 254963281) ^ 63740820 = (7 : ZMod 254963281) ^ (31870410 + 31870410) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 31870410 * (7 : ZMod 254963281) ^ 31870410 := by rw [pow_add]
          _ = 227420149 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 254963281) ^ 127481640 = 254963280 := by
        calc
          (7 : ZMod 254963281) ^ 127481640 = (7 : ZMod 254963281) ^ (63740820 + 63740820) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 63740820 * (7 : ZMod 254963281) ^ 63740820 := by rw [pow_add]
          _ = 254963280 := by rw [factor_0_25]; decide
      change (7 : ZMod 254963281) ^ 127481640 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (7 : ZMod 254963281) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 254963281) ^ 2 = 49 := by
        calc
          (7 : ZMod 254963281) ^ 2 = (7 : ZMod 254963281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1 * (7 : ZMod 254963281) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 254963281) ^ 5 = 16807 := by
        calc
          (7 : ZMod 254963281) ^ 5 = (7 : ZMod 254963281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 2 * (7 : ZMod 254963281) ^ 2) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 254963281) ^ 10 = 27511968 := by
        calc
          (7 : ZMod 254963281) ^ 10 = (7 : ZMod 254963281) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 5 * (7 : ZMod 254963281) ^ 5 := by rw [pow_add]
          _ = 27511968 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 254963281) ^ 20 = 165744729 := by
        calc
          (7 : ZMod 254963281) ^ 20 = (7 : ZMod 254963281) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 10 * (7 : ZMod 254963281) ^ 10 := by rw [pow_add]
          _ = 165744729 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 254963281) ^ 40 = 212605919 := by
        calc
          (7 : ZMod 254963281) ^ 40 = (7 : ZMod 254963281) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 20 * (7 : ZMod 254963281) ^ 20 := by rw [pow_add]
          _ = 212605919 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 254963281) ^ 81 = 209643786 := by
        calc
          (7 : ZMod 254963281) ^ 81 = (7 : ZMod 254963281) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 40 * (7 : ZMod 254963281) ^ 40) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 209643786 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 254963281) ^ 162 = 171922806 := by
        calc
          (7 : ZMod 254963281) ^ 162 = (7 : ZMod 254963281) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 81 * (7 : ZMod 254963281) ^ 81 := by rw [pow_add]
          _ = 171922806 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 254963281) ^ 324 = 162912890 := by
        calc
          (7 : ZMod 254963281) ^ 324 = (7 : ZMod 254963281) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 162 * (7 : ZMod 254963281) ^ 162 := by rw [pow_add]
          _ = 162912890 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 254963281) ^ 648 = 217236209 := by
        calc
          (7 : ZMod 254963281) ^ 648 = (7 : ZMod 254963281) ^ (324 + 324) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 324 * (7 : ZMod 254963281) ^ 324 := by rw [pow_add]
          _ = 217236209 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 254963281) ^ 1296 = 210400527 := by
        calc
          (7 : ZMod 254963281) ^ 1296 = (7 : ZMod 254963281) ^ (648 + 648) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 648 * (7 : ZMod 254963281) ^ 648 := by rw [pow_add]
          _ = 210400527 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 254963281) ^ 2593 = 122951413 := by
        calc
          (7 : ZMod 254963281) ^ 2593 = (7 : ZMod 254963281) ^ (1296 + 1296 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1296 * (7 : ZMod 254963281) ^ 1296) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 122951413 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 254963281) ^ 5187 = 201693978 := by
        calc
          (7 : ZMod 254963281) ^ 5187 = (7 : ZMod 254963281) ^ (2593 + 2593 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 2593 * (7 : ZMod 254963281) ^ 2593) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 201693978 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 254963281) ^ 10374 = 216877251 := by
        calc
          (7 : ZMod 254963281) ^ 10374 = (7 : ZMod 254963281) ^ (5187 + 5187) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 5187 * (7 : ZMod 254963281) ^ 5187 := by rw [pow_add]
          _ = 216877251 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 254963281) ^ 20748 = 169107427 := by
        calc
          (7 : ZMod 254963281) ^ 20748 = (7 : ZMod 254963281) ^ (10374 + 10374) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 10374 * (7 : ZMod 254963281) ^ 10374 := by rw [pow_add]
          _ = 169107427 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 254963281) ^ 41497 = 142648885 := by
        calc
          (7 : ZMod 254963281) ^ 41497 = (7 : ZMod 254963281) ^ (20748 + 20748 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 20748 * (7 : ZMod 254963281) ^ 20748) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 142648885 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 254963281) ^ 82995 = 226524564 := by
        calc
          (7 : ZMod 254963281) ^ 82995 = (7 : ZMod 254963281) ^ (41497 + 41497 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 41497 * (7 : ZMod 254963281) ^ 41497) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 226524564 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 254963281) ^ 165991 = 103139834 := by
        calc
          (7 : ZMod 254963281) ^ 165991 = (7 : ZMod 254963281) ^ (82995 + 82995 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 82995 * (7 : ZMod 254963281) ^ 82995) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 103139834 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 254963281) ^ 331983 = 232980902 := by
        calc
          (7 : ZMod 254963281) ^ 331983 = (7 : ZMod 254963281) ^ (165991 + 165991 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 165991 * (7 : ZMod 254963281) ^ 165991) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 232980902 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 254963281) ^ 663966 = 218992209 := by
        calc
          (7 : ZMod 254963281) ^ 663966 = (7 : ZMod 254963281) ^ (331983 + 331983) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 331983 * (7 : ZMod 254963281) ^ 331983 := by rw [pow_add]
          _ = 218992209 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 254963281) ^ 1327933 = 152459615 := by
        calc
          (7 : ZMod 254963281) ^ 1327933 = (7 : ZMod 254963281) ^ (663966 + 663966 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 663966 * (7 : ZMod 254963281) ^ 663966) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 152459615 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 254963281) ^ 2655867 = 193426181 := by
        calc
          (7 : ZMod 254963281) ^ 2655867 = (7 : ZMod 254963281) ^ (1327933 + 1327933 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1327933 * (7 : ZMod 254963281) ^ 1327933) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 193426181 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 254963281) ^ 5311735 = 59816374 := by
        calc
          (7 : ZMod 254963281) ^ 5311735 = (7 : ZMod 254963281) ^ (2655867 + 2655867 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 2655867 * (7 : ZMod 254963281) ^ 2655867) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 59816374 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 254963281) ^ 10623470 = 205445129 := by
        calc
          (7 : ZMod 254963281) ^ 10623470 = (7 : ZMod 254963281) ^ (5311735 + 5311735) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 5311735 * (7 : ZMod 254963281) ^ 5311735 := by rw [pow_add]
          _ = 205445129 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 254963281) ^ 21246940 = 233518168 := by
        calc
          (7 : ZMod 254963281) ^ 21246940 = (7 : ZMod 254963281) ^ (10623470 + 10623470) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 10623470 * (7 : ZMod 254963281) ^ 10623470 := by rw [pow_add]
          _ = 233518168 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 254963281) ^ 42493880 = 48882928 := by
        calc
          (7 : ZMod 254963281) ^ 42493880 = (7 : ZMod 254963281) ^ (21246940 + 21246940) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 21246940 * (7 : ZMod 254963281) ^ 21246940 := by rw [pow_add]
          _ = 48882928 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 254963281) ^ 84987760 = 48882927 := by
        calc
          (7 : ZMod 254963281) ^ 84987760 = (7 : ZMod 254963281) ^ (42493880 + 42493880) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 42493880 * (7 : ZMod 254963281) ^ 42493880 := by rw [pow_add]
          _ = 48882927 := by rw [factor_1_25]; decide
      change (7 : ZMod 254963281) ^ 84987760 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (7 : ZMod 254963281) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 254963281) ^ 3 = 343 := by
        calc
          (7 : ZMod 254963281) ^ 3 = (7 : ZMod 254963281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1 * (7 : ZMod 254963281) ^ 1) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 254963281) ^ 6 = 117649 := by
        calc
          (7 : ZMod 254963281) ^ 6 = (7 : ZMod 254963281) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3 * (7 : ZMod 254963281) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 254963281) ^ 12 = 73270027 := by
        calc
          (7 : ZMod 254963281) ^ 12 = (7 : ZMod 254963281) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 6 * (7 : ZMod 254963281) ^ 6 := by rw [pow_add]
          _ = 73270027 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 254963281) ^ 24 = 210375969 := by
        calc
          (7 : ZMod 254963281) ^ 24 = (7 : ZMod 254963281) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 12 * (7 : ZMod 254963281) ^ 12 := by rw [pow_add]
          _ = 210375969 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 254963281) ^ 48 = 140884672 := by
        calc
          (7 : ZMod 254963281) ^ 48 = (7 : ZMod 254963281) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 24 * (7 : ZMod 254963281) ^ 24 := by rw [pow_add]
          _ = 140884672 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 254963281) ^ 97 = 246974088 := by
        calc
          (7 : ZMod 254963281) ^ 97 = (7 : ZMod 254963281) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 48 * (7 : ZMod 254963281) ^ 48) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 246974088 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 254963281) ^ 194 = 206952271 := by
        calc
          (7 : ZMod 254963281) ^ 194 = (7 : ZMod 254963281) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 97 * (7 : ZMod 254963281) ^ 97 := by rw [pow_add]
          _ = 206952271 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 254963281) ^ 389 = 142395591 := by
        calc
          (7 : ZMod 254963281) ^ 389 = (7 : ZMod 254963281) ^ (194 + 194 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 194 * (7 : ZMod 254963281) ^ 194) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 142395591 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 254963281) ^ 778 = 223807007 := by
        calc
          (7 : ZMod 254963281) ^ 778 = (7 : ZMod 254963281) ^ (389 + 389) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 389 * (7 : ZMod 254963281) ^ 389 := by rw [pow_add]
          _ = 223807007 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 254963281) ^ 1556 = 123600049 := by
        calc
          (7 : ZMod 254963281) ^ 1556 = (7 : ZMod 254963281) ^ (778 + 778) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 778 * (7 : ZMod 254963281) ^ 778 := by rw [pow_add]
          _ = 123600049 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 254963281) ^ 3112 = 143667919 := by
        calc
          (7 : ZMod 254963281) ^ 3112 = (7 : ZMod 254963281) ^ (1556 + 1556) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1556 * (7 : ZMod 254963281) ^ 1556 := by rw [pow_add]
          _ = 143667919 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 254963281) ^ 6224 = 124685481 := by
        calc
          (7 : ZMod 254963281) ^ 6224 = (7 : ZMod 254963281) ^ (3112 + 3112) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3112 * (7 : ZMod 254963281) ^ 3112 := by rw [pow_add]
          _ = 124685481 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 254963281) ^ 12449 = 221340566 := by
        calc
          (7 : ZMod 254963281) ^ 12449 = (7 : ZMod 254963281) ^ (6224 + 6224 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 6224 * (7 : ZMod 254963281) ^ 6224) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 221340566 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 254963281) ^ 24898 = 173079705 := by
        calc
          (7 : ZMod 254963281) ^ 24898 = (7 : ZMod 254963281) ^ (12449 + 12449) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 12449 * (7 : ZMod 254963281) ^ 12449 := by rw [pow_add]
          _ = 173079705 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 254963281) ^ 49797 = 53468497 := by
        calc
          (7 : ZMod 254963281) ^ 49797 = (7 : ZMod 254963281) ^ (24898 + 24898 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 24898 * (7 : ZMod 254963281) ^ 24898) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 53468497 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 254963281) ^ 99595 = 212785498 := by
        calc
          (7 : ZMod 254963281) ^ 99595 = (7 : ZMod 254963281) ^ (49797 + 49797 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 49797 * (7 : ZMod 254963281) ^ 49797) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 212785498 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 254963281) ^ 199190 = 134705830 := by
        calc
          (7 : ZMod 254963281) ^ 199190 = (7 : ZMod 254963281) ^ (99595 + 99595) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 99595 * (7 : ZMod 254963281) ^ 99595 := by rw [pow_add]
          _ = 134705830 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 254963281) ^ 398380 = 161239919 := by
        calc
          (7 : ZMod 254963281) ^ 398380 = (7 : ZMod 254963281) ^ (199190 + 199190) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 199190 * (7 : ZMod 254963281) ^ 199190 := by rw [pow_add]
          _ = 161239919 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 254963281) ^ 796760 = 198146116 := by
        calc
          (7 : ZMod 254963281) ^ 796760 = (7 : ZMod 254963281) ^ (398380 + 398380) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 398380 * (7 : ZMod 254963281) ^ 398380 := by rw [pow_add]
          _ = 198146116 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 254963281) ^ 1593520 = 192290073 := by
        calc
          (7 : ZMod 254963281) ^ 1593520 = (7 : ZMod 254963281) ^ (796760 + 796760) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 796760 * (7 : ZMod 254963281) ^ 796760 := by rw [pow_add]
          _ = 192290073 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 254963281) ^ 3187041 = 148878963 := by
        calc
          (7 : ZMod 254963281) ^ 3187041 = (7 : ZMod 254963281) ^ (1593520 + 1593520 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1593520 * (7 : ZMod 254963281) ^ 1593520) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 148878963 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 254963281) ^ 6374082 = 133838056 := by
        calc
          (7 : ZMod 254963281) ^ 6374082 = (7 : ZMod 254963281) ^ (3187041 + 3187041) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3187041 * (7 : ZMod 254963281) ^ 3187041 := by rw [pow_add]
          _ = 133838056 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 254963281) ^ 12748164 = 178091031 := by
        calc
          (7 : ZMod 254963281) ^ 12748164 = (7 : ZMod 254963281) ^ (6374082 + 6374082) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 6374082 * (7 : ZMod 254963281) ^ 6374082 := by rw [pow_add]
          _ = 178091031 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 254963281) ^ 25496328 = 214770870 := by
        calc
          (7 : ZMod 254963281) ^ 25496328 = (7 : ZMod 254963281) ^ (12748164 + 12748164) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 12748164 * (7 : ZMod 254963281) ^ 12748164 := by rw [pow_add]
          _ = 214770870 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 254963281) ^ 50992656 = 146043310 := by
        calc
          (7 : ZMod 254963281) ^ 50992656 = (7 : ZMod 254963281) ^ (25496328 + 25496328) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 25496328 * (7 : ZMod 254963281) ^ 25496328 := by rw [pow_add]
          _ = 146043310 := by rw [factor_2_24]; decide
      change (7 : ZMod 254963281) ^ 50992656 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (7 : ZMod 254963281) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 254963281) ^ 2 = 49 := by
        calc
          (7 : ZMod 254963281) ^ 2 = (7 : ZMod 254963281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1 * (7 : ZMod 254963281) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 254963281) ^ 5 = 16807 := by
        calc
          (7 : ZMod 254963281) ^ 5 = (7 : ZMod 254963281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 2 * (7 : ZMod 254963281) ^ 2) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 254963281) ^ 11 = 192583776 := by
        calc
          (7 : ZMod 254963281) ^ 11 = (7 : ZMod 254963281) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 5 * (7 : ZMod 254963281) ^ 5) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 192583776 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 254963281) ^ 22 = 217630010 := by
        calc
          (7 : ZMod 254963281) ^ 22 = (7 : ZMod 254963281) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 11 * (7 : ZMod 254963281) ^ 11 := by rw [pow_add]
          _ = 217630010 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 254963281) ^ 44 = 30322957 := by
        calc
          (7 : ZMod 254963281) ^ 44 = (7 : ZMod 254963281) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 22 * (7 : ZMod 254963281) ^ 22 := by rw [pow_add]
          _ = 30322957 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 254963281) ^ 88 = 247018400 := by
        calc
          (7 : ZMod 254963281) ^ 88 = (7 : ZMod 254963281) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 44 * (7 : ZMod 254963281) ^ 44 := by rw [pow_add]
          _ = 247018400 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 254963281) ^ 176 = 129590272 := by
        calc
          (7 : ZMod 254963281) ^ 176 = (7 : ZMod 254963281) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 88 * (7 : ZMod 254963281) ^ 88 := by rw [pow_add]
          _ = 129590272 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 254963281) ^ 353 = 218758853 := by
        calc
          (7 : ZMod 254963281) ^ 353 = (7 : ZMod 254963281) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 176 * (7 : ZMod 254963281) ^ 176) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 218758853 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 254963281) ^ 707 = 173611843 := by
        calc
          (7 : ZMod 254963281) ^ 707 = (7 : ZMod 254963281) ^ (353 + 353 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 353 * (7 : ZMod 254963281) ^ 353) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 173611843 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 254963281) ^ 1414 = 76078944 := by
        calc
          (7 : ZMod 254963281) ^ 1414 = (7 : ZMod 254963281) ^ (707 + 707) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 707 * (7 : ZMod 254963281) ^ 707 := by rw [pow_add]
          _ = 76078944 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 254963281) ^ 2829 = 217149999 := by
        calc
          (7 : ZMod 254963281) ^ 2829 = (7 : ZMod 254963281) ^ (1414 + 1414 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1414 * (7 : ZMod 254963281) ^ 1414) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 217149999 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 254963281) ^ 5658 = 17232284 := by
        calc
          (7 : ZMod 254963281) ^ 5658 = (7 : ZMod 254963281) ^ (2829 + 2829) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 2829 * (7 : ZMod 254963281) ^ 2829 := by rw [pow_add]
          _ = 17232284 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 254963281) ^ 11317 = 215145726 := by
        calc
          (7 : ZMod 254963281) ^ 11317 = (7 : ZMod 254963281) ^ (5658 + 5658 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 5658 * (7 : ZMod 254963281) ^ 5658) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 215145726 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 254963281) ^ 22635 = 181036009 := by
        calc
          (7 : ZMod 254963281) ^ 22635 = (7 : ZMod 254963281) ^ (11317 + 11317 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 11317 * (7 : ZMod 254963281) ^ 11317) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 181036009 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 254963281) ^ 45270 = 102034898 := by
        calc
          (7 : ZMod 254963281) ^ 45270 = (7 : ZMod 254963281) ^ (22635 + 22635) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 22635 * (7 : ZMod 254963281) ^ 22635 := by rw [pow_add]
          _ = 102034898 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 254963281) ^ 90540 = 21282761 := by
        calc
          (7 : ZMod 254963281) ^ 90540 = (7 : ZMod 254963281) ^ (45270 + 45270) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 45270 * (7 : ZMod 254963281) ^ 45270 := by rw [pow_add]
          _ = 21282761 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 254963281) ^ 181081 = 173339253 := by
        calc
          (7 : ZMod 254963281) ^ 181081 = (7 : ZMod 254963281) ^ (90540 + 90540 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 90540 * (7 : ZMod 254963281) ^ 90540) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 173339253 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 254963281) ^ 362163 = 194655488 := by
        calc
          (7 : ZMod 254963281) ^ 362163 = (7 : ZMod 254963281) ^ (181081 + 181081 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 181081 * (7 : ZMod 254963281) ^ 181081) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 194655488 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 254963281) ^ 724327 = 4980328 := by
        calc
          (7 : ZMod 254963281) ^ 724327 = (7 : ZMod 254963281) ^ (362163 + 362163 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 362163 * (7 : ZMod 254963281) ^ 362163) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 4980328 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 254963281) ^ 1448655 = 8927865 := by
        calc
          (7 : ZMod 254963281) ^ 1448655 = (7 : ZMod 254963281) ^ (724327 + 724327 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 724327 * (7 : ZMod 254963281) ^ 724327) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 8927865 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 254963281) ^ 2897310 = 152552005 := by
        calc
          (7 : ZMod 254963281) ^ 2897310 = (7 : ZMod 254963281) ^ (1448655 + 1448655) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1448655 * (7 : ZMod 254963281) ^ 1448655 := by rw [pow_add]
          _ = 152552005 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 254963281) ^ 5794620 = 125301609 := by
        calc
          (7 : ZMod 254963281) ^ 5794620 = (7 : ZMod 254963281) ^ (2897310 + 2897310) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 2897310 * (7 : ZMod 254963281) ^ 2897310 := by rw [pow_add]
          _ = 125301609 := by rw [factor_3_21]; decide
      have factor_3_23 : (7 : ZMod 254963281) ^ 11589240 = 213005613 := by
        calc
          (7 : ZMod 254963281) ^ 11589240 = (7 : ZMod 254963281) ^ (5794620 + 5794620) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 5794620 * (7 : ZMod 254963281) ^ 5794620 := by rw [pow_add]
          _ = 213005613 := by rw [factor_3_22]; decide
      have factor_3_24 : (7 : ZMod 254963281) ^ 23178480 = 172787681 := by
        calc
          (7 : ZMod 254963281) ^ 23178480 = (7 : ZMod 254963281) ^ (11589240 + 11589240) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 11589240 * (7 : ZMod 254963281) ^ 11589240 := by rw [pow_add]
          _ = 172787681 := by rw [factor_3_23]; decide
      change (7 : ZMod 254963281) ^ 23178480 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (7 : ZMod 254963281) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 254963281) ^ 2 = 49 := by
        calc
          (7 : ZMod 254963281) ^ 2 = (7 : ZMod 254963281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1 * (7 : ZMod 254963281) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 254963281) ^ 4 = 2401 := by
        calc
          (7 : ZMod 254963281) ^ 4 = (7 : ZMod 254963281) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 2 * (7 : ZMod 254963281) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 254963281) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 254963281) ^ 9 = (7 : ZMod 254963281) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 4 * (7 : ZMod 254963281) ^ 4) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 254963281) ^ 18 = 91839194 := by
        calc
          (7 : ZMod 254963281) ^ 18 = (7 : ZMod 254963281) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 9 * (7 : ZMod 254963281) ^ 9 := by rw [pow_add]
          _ = 91839194 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 254963281) ^ 37 = 167869808 := by
        calc
          (7 : ZMod 254963281) ^ 37 = (7 : ZMod 254963281) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 18 * (7 : ZMod 254963281) ^ 18) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 167869808 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 254963281) ^ 74 = 186048717 := by
        calc
          (7 : ZMod 254963281) ^ 74 = (7 : ZMod 254963281) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 37 * (7 : ZMod 254963281) ^ 37 := by rw [pow_add]
          _ = 186048717 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 254963281) ^ 149 = 234054751 := by
        calc
          (7 : ZMod 254963281) ^ 149 = (7 : ZMod 254963281) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 74 * (7 : ZMod 254963281) ^ 74) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 234054751 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 254963281) ^ 299 = 202717520 := by
        calc
          (7 : ZMod 254963281) ^ 299 = (7 : ZMod 254963281) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 149 * (7 : ZMod 254963281) ^ 149) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 202717520 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 254963281) ^ 598 = 248549510 := by
        calc
          (7 : ZMod 254963281) ^ 598 = (7 : ZMod 254963281) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 299 * (7 : ZMod 254963281) ^ 299 := by rw [pow_add]
          _ = 248549510 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 254963281) ^ 1197 = 189448249 := by
        calc
          (7 : ZMod 254963281) ^ 1197 = (7 : ZMod 254963281) ^ (598 + 598 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 598 * (7 : ZMod 254963281) ^ 598) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 189448249 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 254963281) ^ 2394 = 34731407 := by
        calc
          (7 : ZMod 254963281) ^ 2394 = (7 : ZMod 254963281) ^ (1197 + 1197) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1197 * (7 : ZMod 254963281) ^ 1197 := by rw [pow_add]
          _ = 34731407 := by rw [factor_4_10]; decide
      have factor_4_12 : (7 : ZMod 254963281) ^ 4788 = 85443375 := by
        calc
          (7 : ZMod 254963281) ^ 4788 = (7 : ZMod 254963281) ^ (2394 + 2394) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 2394 * (7 : ZMod 254963281) ^ 2394 := by rw [pow_add]
          _ = 85443375 := by rw [factor_4_11]; decide
      have factor_4_13 : (7 : ZMod 254963281) ^ 9576 = 186260015 := by
        calc
          (7 : ZMod 254963281) ^ 9576 = (7 : ZMod 254963281) ^ (4788 + 4788) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 4788 * (7 : ZMod 254963281) ^ 4788 := by rw [pow_add]
          _ = 186260015 := by rw [factor_4_12]; decide
      have factor_4_14 : (7 : ZMod 254963281) ^ 19152 = 223391103 := by
        calc
          (7 : ZMod 254963281) ^ 19152 = (7 : ZMod 254963281) ^ (9576 + 9576) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 9576 * (7 : ZMod 254963281) ^ 9576 := by rw [pow_add]
          _ = 223391103 := by rw [factor_4_13]; decide
      have factor_4_15 : (7 : ZMod 254963281) ^ 38305 = 139806324 := by
        calc
          (7 : ZMod 254963281) ^ 38305 = (7 : ZMod 254963281) ^ (19152 + 19152 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 19152 * (7 : ZMod 254963281) ^ 19152) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 139806324 := by rw [factor_4_14]; decide
      have factor_4_16 : (7 : ZMod 254963281) ^ 76611 = 238228362 := by
        calc
          (7 : ZMod 254963281) ^ 76611 = (7 : ZMod 254963281) ^ (38305 + 38305 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 38305 * (7 : ZMod 254963281) ^ 38305) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 238228362 := by rw [factor_4_15]; decide
      have factor_4_17 : (7 : ZMod 254963281) ^ 153223 = 128478167 := by
        calc
          (7 : ZMod 254963281) ^ 153223 = (7 : ZMod 254963281) ^ (76611 + 76611 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 76611 * (7 : ZMod 254963281) ^ 76611) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 128478167 := by rw [factor_4_16]; decide
      have factor_4_18 : (7 : ZMod 254963281) ^ 306446 = 174308168 := by
        calc
          (7 : ZMod 254963281) ^ 306446 = (7 : ZMod 254963281) ^ (153223 + 153223) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 153223 * (7 : ZMod 254963281) ^ 153223 := by rw [pow_add]
          _ = 174308168 := by rw [factor_4_17]; decide
      have factor_4_19 : (7 : ZMod 254963281) ^ 612892 = 133022162 := by
        calc
          (7 : ZMod 254963281) ^ 612892 = (7 : ZMod 254963281) ^ (306446 + 306446) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 306446 * (7 : ZMod 254963281) ^ 306446 := by rw [pow_add]
          _ = 133022162 := by rw [factor_4_18]; decide
      have factor_4_20 : (7 : ZMod 254963281) ^ 1225785 = 189737442 := by
        calc
          (7 : ZMod 254963281) ^ 1225785 = (7 : ZMod 254963281) ^ (612892 + 612892 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 612892 * (7 : ZMod 254963281) ^ 612892) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 189737442 := by rw [factor_4_19]; decide
      have factor_4_21 : (7 : ZMod 254963281) ^ 2451570 = 214816918 := by
        calc
          (7 : ZMod 254963281) ^ 2451570 = (7 : ZMod 254963281) ^ (1225785 + 1225785) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1225785 * (7 : ZMod 254963281) ^ 1225785 := by rw [pow_add]
          _ = 214816918 := by rw [factor_4_20]; decide
      have factor_4_22 : (7 : ZMod 254963281) ^ 4903140 = 223385468 := by
        calc
          (7 : ZMod 254963281) ^ 4903140 = (7 : ZMod 254963281) ^ (2451570 + 2451570) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 2451570 * (7 : ZMod 254963281) ^ 2451570 := by rw [pow_add]
          _ = 223385468 := by rw [factor_4_21]; decide
      have factor_4_23 : (7 : ZMod 254963281) ^ 9806280 = 196394622 := by
        calc
          (7 : ZMod 254963281) ^ 9806280 = (7 : ZMod 254963281) ^ (4903140 + 4903140) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 4903140 * (7 : ZMod 254963281) ^ 4903140 := by rw [pow_add]
          _ = 196394622 := by rw [factor_4_22]; decide
      have factor_4_24 : (7 : ZMod 254963281) ^ 19612560 = 106173355 := by
        calc
          (7 : ZMod 254963281) ^ 19612560 = (7 : ZMod 254963281) ^ (9806280 + 9806280) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 9806280 * (7 : ZMod 254963281) ^ 9806280 := by rw [pow_add]
          _ = 106173355 := by rw [factor_4_23]; decide
      change (7 : ZMod 254963281) ^ 19612560 ≠ 1
      rw [factor_4_24]
      decide
    ·
      have factor_5_0 : (7 : ZMod 254963281) ^ 1 = 7 := by norm_num
      have factor_5_1 : (7 : ZMod 254963281) ^ 3 = 343 := by
        calc
          (7 : ZMod 254963281) ^ 3 = (7 : ZMod 254963281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1 * (7 : ZMod 254963281) ^ 1) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_5_0]; decide
      have factor_5_2 : (7 : ZMod 254963281) ^ 7 = 823543 := by
        calc
          (7 : ZMod 254963281) ^ 7 = (7 : ZMod 254963281) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 3 * (7 : ZMod 254963281) ^ 3) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_5_1]; decide
      have factor_5_3 : (7 : ZMod 254963281) ^ 14 = 20745389 := by
        calc
          (7 : ZMod 254963281) ^ 14 = (7 : ZMod 254963281) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 7 * (7 : ZMod 254963281) ^ 7 := by rw [pow_add]
          _ = 20745389 := by rw [factor_5_2]; decide
      have factor_5_4 : (7 : ZMod 254963281) ^ 28 = 30441908 := by
        calc
          (7 : ZMod 254963281) ^ 28 = (7 : ZMod 254963281) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 14 * (7 : ZMod 254963281) ^ 14 := by rw [pow_add]
          _ = 30441908 := by rw [factor_5_3]; decide
      have factor_5_5 : (7 : ZMod 254963281) ^ 57 = 46284093 := by
        calc
          (7 : ZMod 254963281) ^ 57 = (7 : ZMod 254963281) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 28 * (7 : ZMod 254963281) ^ 28) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 46284093 := by rw [factor_5_4]; decide
      have factor_5_6 : (7 : ZMod 254963281) ^ 114 = 225110508 := by
        calc
          (7 : ZMod 254963281) ^ 114 = (7 : ZMod 254963281) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 57 * (7 : ZMod 254963281) ^ 57 := by rw [pow_add]
          _ = 225110508 := by rw [factor_5_5]; decide
      have factor_5_7 : (7 : ZMod 254963281) ^ 228 = 111839931 := by
        calc
          (7 : ZMod 254963281) ^ 228 = (7 : ZMod 254963281) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 114 * (7 : ZMod 254963281) ^ 114 := by rw [pow_add]
          _ = 111839931 := by rw [factor_5_6]; decide
      have factor_5_8 : (7 : ZMod 254963281) ^ 457 = 205478104 := by
        calc
          (7 : ZMod 254963281) ^ 457 = (7 : ZMod 254963281) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 228 * (7 : ZMod 254963281) ^ 228) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 205478104 := by rw [factor_5_7]; decide
      have factor_5_9 : (7 : ZMod 254963281) ^ 915 = 20307095 := by
        calc
          (7 : ZMod 254963281) ^ 915 = (7 : ZMod 254963281) ^ (457 + 457 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 457 * (7 : ZMod 254963281) ^ 457) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 20307095 := by rw [factor_5_8]; decide
      have factor_5_10 : (7 : ZMod 254963281) ^ 1830 = 241686344 := by
        calc
          (7 : ZMod 254963281) ^ 1830 = (7 : ZMod 254963281) ^ (915 + 915) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 915 * (7 : ZMod 254963281) ^ 915 := by rw [pow_add]
          _ = 241686344 := by rw [factor_5_9]; decide
      have factor_5_11 : (7 : ZMod 254963281) ^ 3661 = 230703389 := by
        calc
          (7 : ZMod 254963281) ^ 3661 = (7 : ZMod 254963281) ^ (1830 + 1830 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1830 * (7 : ZMod 254963281) ^ 1830) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 230703389 := by rw [factor_5_10]; decide
      have factor_5_12 : (7 : ZMod 254963281) ^ 7323 = 133920777 := by
        calc
          (7 : ZMod 254963281) ^ 7323 = (7 : ZMod 254963281) ^ (3661 + 3661 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 3661 * (7 : ZMod 254963281) ^ 3661) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 133920777 := by rw [factor_5_11]; decide
      have factor_5_13 : (7 : ZMod 254963281) ^ 14646 = 31405311 := by
        calc
          (7 : ZMod 254963281) ^ 14646 = (7 : ZMod 254963281) ^ (7323 + 7323) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 7323 * (7 : ZMod 254963281) ^ 7323 := by rw [pow_add]
          _ = 31405311 := by rw [factor_5_12]; decide
      have factor_5_14 : (7 : ZMod 254963281) ^ 29292 = 231831627 := by
        calc
          (7 : ZMod 254963281) ^ 29292 = (7 : ZMod 254963281) ^ (14646 + 14646) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 14646 * (7 : ZMod 254963281) ^ 14646 := by rw [pow_add]
          _ = 231831627 := by rw [factor_5_13]; decide
      have factor_5_15 : (7 : ZMod 254963281) ^ 58585 = 59411207 := by
        calc
          (7 : ZMod 254963281) ^ 58585 = (7 : ZMod 254963281) ^ (29292 + 29292 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 29292 * (7 : ZMod 254963281) ^ 29292) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 59411207 := by rw [factor_5_14]; decide
      have factor_5_16 : (7 : ZMod 254963281) ^ 117170 = 252095329 := by
        calc
          (7 : ZMod 254963281) ^ 117170 = (7 : ZMod 254963281) ^ (58585 + 58585) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 58585 * (7 : ZMod 254963281) ^ 58585 := by rw [pow_add]
          _ = 252095329 := by rw [factor_5_15]; decide
      have factor_5_17 : (7 : ZMod 254963281) ^ 234341 = 232604708 := by
        calc
          (7 : ZMod 254963281) ^ 234341 = (7 : ZMod 254963281) ^ (117170 + 117170 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 117170 * (7 : ZMod 254963281) ^ 117170) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 232604708 := by rw [factor_5_16]; decide
      have factor_5_18 : (7 : ZMod 254963281) ^ 468682 = 46429472 := by
        calc
          (7 : ZMod 254963281) ^ 468682 = (7 : ZMod 254963281) ^ (234341 + 234341) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 234341 * (7 : ZMod 254963281) ^ 234341 := by rw [pow_add]
          _ = 46429472 := by rw [factor_5_17]; decide
      have factor_5_19 : (7 : ZMod 254963281) ^ 937365 = 101569641 := by
        calc
          (7 : ZMod 254963281) ^ 937365 = (7 : ZMod 254963281) ^ (468682 + 468682 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 468682 * (7 : ZMod 254963281) ^ 468682) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 101569641 := by rw [factor_5_18]; decide
      have factor_5_20 : (7 : ZMod 254963281) ^ 1874730 = 131777416 := by
        calc
          (7 : ZMod 254963281) ^ 1874730 = (7 : ZMod 254963281) ^ (937365 + 937365) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 937365 * (7 : ZMod 254963281) ^ 937365 := by rw [pow_add]
          _ = 131777416 := by rw [factor_5_19]; decide
      have factor_5_21 : (7 : ZMod 254963281) ^ 3749460 = 146016643 := by
        calc
          (7 : ZMod 254963281) ^ 3749460 = (7 : ZMod 254963281) ^ (1874730 + 1874730) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1874730 * (7 : ZMod 254963281) ^ 1874730 := by rw [pow_add]
          _ = 146016643 := by rw [factor_5_20]; decide
      have factor_5_22 : (7 : ZMod 254963281) ^ 7498920 = 60363232 := by
        calc
          (7 : ZMod 254963281) ^ 7498920 = (7 : ZMod 254963281) ^ (3749460 + 3749460) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3749460 * (7 : ZMod 254963281) ^ 3749460 := by rw [pow_add]
          _ = 60363232 := by rw [factor_5_21]; decide
      have factor_5_23 : (7 : ZMod 254963281) ^ 14997840 = 9406269 := by
        calc
          (7 : ZMod 254963281) ^ 14997840 = (7 : ZMod 254963281) ^ (7498920 + 7498920) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 7498920 * (7 : ZMod 254963281) ^ 7498920 := by rw [pow_add]
          _ = 9406269 := by rw [factor_5_22]; decide
      change (7 : ZMod 254963281) ^ 14997840 ≠ 1
      rw [factor_5_23]
      decide
    ·
      have factor_6_0 : (7 : ZMod 254963281) ^ 1 = 7 := by norm_num
      have factor_6_1 : (7 : ZMod 254963281) ^ 3 = 343 := by
        calc
          (7 : ZMod 254963281) ^ 3 = (7 : ZMod 254963281) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 1 * (7 : ZMod 254963281) ^ 1) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_6_0]; decide
      have factor_6_2 : (7 : ZMod 254963281) ^ 6 = 117649 := by
        calc
          (7 : ZMod 254963281) ^ 6 = (7 : ZMod 254963281) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3 * (7 : ZMod 254963281) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_6_1]; decide
      have factor_6_3 : (7 : ZMod 254963281) ^ 12 = 73270027 := by
        calc
          (7 : ZMod 254963281) ^ 12 = (7 : ZMod 254963281) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 6 * (7 : ZMod 254963281) ^ 6 := by rw [pow_add]
          _ = 73270027 := by rw [factor_6_2]; decide
      have factor_6_4 : (7 : ZMod 254963281) ^ 25 = 197815378 := by
        calc
          (7 : ZMod 254963281) ^ 25 = (7 : ZMod 254963281) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 12 * (7 : ZMod 254963281) ^ 12) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 197815378 := by rw [factor_6_3]; decide
      have factor_6_5 : (7 : ZMod 254963281) ^ 51 = 135382387 := by
        calc
          (7 : ZMod 254963281) ^ 51 = (7 : ZMod 254963281) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 25 * (7 : ZMod 254963281) ^ 25) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 135382387 := by rw [factor_6_4]; decide
      have factor_6_6 : (7 : ZMod 254963281) ^ 102 = 91282336 := by
        calc
          (7 : ZMod 254963281) ^ 102 = (7 : ZMod 254963281) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 51 * (7 : ZMod 254963281) ^ 51 := by rw [pow_add]
          _ = 91282336 := by rw [factor_6_5]; decide
      have factor_6_7 : (7 : ZMod 254963281) ^ 204 = 190651218 := by
        calc
          (7 : ZMod 254963281) ^ 204 = (7 : ZMod 254963281) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 102 * (7 : ZMod 254963281) ^ 102 := by rw [pow_add]
          _ = 190651218 := by rw [factor_6_6]; decide
      have factor_6_8 : (7 : ZMod 254963281) ^ 409 = 27856719 := by
        calc
          (7 : ZMod 254963281) ^ 409 = (7 : ZMod 254963281) ^ (204 + 204 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 204 * (7 : ZMod 254963281) ^ 204) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 27856719 := by rw [factor_6_7]; decide
      have factor_6_9 : (7 : ZMod 254963281) ^ 819 = 150206587 := by
        calc
          (7 : ZMod 254963281) ^ 819 = (7 : ZMod 254963281) ^ (409 + 409 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 409 * (7 : ZMod 254963281) ^ 409) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 150206587 := by rw [factor_6_8]; decide
      have factor_6_10 : (7 : ZMod 254963281) ^ 1638 = 103287162 := by
        calc
          (7 : ZMod 254963281) ^ 1638 = (7 : ZMod 254963281) ^ (819 + 819) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 819 * (7 : ZMod 254963281) ^ 819 := by rw [pow_add]
          _ = 103287162 := by rw [factor_6_9]; decide
      have factor_6_11 : (7 : ZMod 254963281) ^ 3276 = 234628713 := by
        calc
          (7 : ZMod 254963281) ^ 3276 = (7 : ZMod 254963281) ^ (1638 + 1638) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1638 * (7 : ZMod 254963281) ^ 1638 := by rw [pow_add]
          _ = 234628713 := by rw [factor_6_10]; decide
      have factor_6_12 : (7 : ZMod 254963281) ^ 6552 = 50923163 := by
        calc
          (7 : ZMod 254963281) ^ 6552 = (7 : ZMod 254963281) ^ (3276 + 3276) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3276 * (7 : ZMod 254963281) ^ 3276 := by rw [pow_add]
          _ = 50923163 := by rw [factor_6_11]; decide
      have factor_6_13 : (7 : ZMod 254963281) ^ 13104 = 229767257 := by
        calc
          (7 : ZMod 254963281) ^ 13104 = (7 : ZMod 254963281) ^ (6552 + 6552) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 6552 * (7 : ZMod 254963281) ^ 6552 := by rw [pow_add]
          _ = 229767257 := by rw [factor_6_12]; decide
      have factor_6_14 : (7 : ZMod 254963281) ^ 26209 = 225899433 := by
        calc
          (7 : ZMod 254963281) ^ 26209 = (7 : ZMod 254963281) ^ (13104 + 13104 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 13104 * (7 : ZMod 254963281) ^ 13104) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 225899433 := by rw [factor_6_13]; decide
      have factor_6_15 : (7 : ZMod 254963281) ^ 52418 = 142596930 := by
        calc
          (7 : ZMod 254963281) ^ 52418 = (7 : ZMod 254963281) ^ (26209 + 26209) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 26209 * (7 : ZMod 254963281) ^ 26209 := by rw [pow_add]
          _ = 142596930 := by rw [factor_6_14]; decide
      have factor_6_16 : (7 : ZMod 254963281) ^ 104836 = 81713733 := by
        calc
          (7 : ZMod 254963281) ^ 104836 = (7 : ZMod 254963281) ^ (52418 + 52418) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 52418 * (7 : ZMod 254963281) ^ 52418 := by rw [pow_add]
          _ = 81713733 := by rw [factor_6_15]; decide
      have factor_6_17 : (7 : ZMod 254963281) ^ 209673 = 82781467 := by
        calc
          (7 : ZMod 254963281) ^ 209673 = (7 : ZMod 254963281) ^ (104836 + 104836 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 104836 * (7 : ZMod 254963281) ^ 104836) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 82781467 := by rw [factor_6_16]; decide
      have factor_6_18 : (7 : ZMod 254963281) ^ 419347 = 195792562 := by
        calc
          (7 : ZMod 254963281) ^ 419347 = (7 : ZMod 254963281) ^ (209673 + 209673 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 209673 * (7 : ZMod 254963281) ^ 209673) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 195792562 := by rw [factor_6_17]; decide
      have factor_6_19 : (7 : ZMod 254963281) ^ 838695 = 4354227 := by
        calc
          (7 : ZMod 254963281) ^ 838695 = (7 : ZMod 254963281) ^ (419347 + 419347 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 419347 * (7 : ZMod 254963281) ^ 419347) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 4354227 := by rw [factor_6_18]; decide
      have factor_6_20 : (7 : ZMod 254963281) ^ 1677390 = 223192369 := by
        calc
          (7 : ZMod 254963281) ^ 1677390 = (7 : ZMod 254963281) ^ (838695 + 838695) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 838695 * (7 : ZMod 254963281) ^ 838695 := by rw [pow_add]
          _ = 223192369 := by rw [factor_6_19]; decide
      have factor_6_21 : (7 : ZMod 254963281) ^ 3354780 = 143547579 := by
        calc
          (7 : ZMod 254963281) ^ 3354780 = (7 : ZMod 254963281) ^ (1677390 + 1677390) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1677390 * (7 : ZMod 254963281) ^ 1677390 := by rw [pow_add]
          _ = 143547579 := by rw [factor_6_20]; decide
      have factor_6_22 : (7 : ZMod 254963281) ^ 6709560 = 198918364 := by
        calc
          (7 : ZMod 254963281) ^ 6709560 = (7 : ZMod 254963281) ^ (3354780 + 3354780) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 3354780 * (7 : ZMod 254963281) ^ 3354780 := by rw [pow_add]
          _ = 198918364 := by rw [factor_6_21]; decide
      have factor_6_23 : (7 : ZMod 254963281) ^ 13419120 = 88056620 := by
        calc
          (7 : ZMod 254963281) ^ 13419120 = (7 : ZMod 254963281) ^ (6709560 + 6709560) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 6709560 * (7 : ZMod 254963281) ^ 6709560 := by rw [pow_add]
          _ = 88056620 := by rw [factor_6_22]; decide
      change (7 : ZMod 254963281) ^ 13419120 ≠ 1
      rw [factor_6_23]
      decide
    ·
      have factor_7_0 : (7 : ZMod 254963281) ^ 1 = 7 := by norm_num
      have factor_7_1 : (7 : ZMod 254963281) ^ 2 = 49 := by
        calc
          (7 : ZMod 254963281) ^ 2 = (7 : ZMod 254963281) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1 * (7 : ZMod 254963281) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_7_0]; decide
      have factor_7_2 : (7 : ZMod 254963281) ^ 5 = 16807 := by
        calc
          (7 : ZMod 254963281) ^ 5 = (7 : ZMod 254963281) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 2 * (7 : ZMod 254963281) ^ 2) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_7_1]; decide
      have factor_7_3 : (7 : ZMod 254963281) ^ 10 = 27511968 := by
        calc
          (7 : ZMod 254963281) ^ 10 = (7 : ZMod 254963281) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 5 * (7 : ZMod 254963281) ^ 5 := by rw [pow_add]
          _ = 27511968 := by rw [factor_7_2]; decide
      have factor_7_4 : (7 : ZMod 254963281) ^ 21 = 140359979 := by
        calc
          (7 : ZMod 254963281) ^ 21 = (7 : ZMod 254963281) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 10 * (7 : ZMod 254963281) ^ 10) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 140359979 := by rw [factor_7_3]; decide
      have factor_7_5 : (7 : ZMod 254963281) ^ 42 = 219158791 := by
        calc
          (7 : ZMod 254963281) ^ 42 = (7 : ZMod 254963281) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 21 * (7 : ZMod 254963281) ^ 21 := by rw [pow_add]
          _ = 219158791 := by rw [factor_7_4]; decide
      have factor_7_6 : (7 : ZMod 254963281) ^ 84 = 8173356 := by
        calc
          (7 : ZMod 254963281) ^ 84 = (7 : ZMod 254963281) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 42 * (7 : ZMod 254963281) ^ 42 := by rw [pow_add]
          _ = 8173356 := by rw [factor_7_5]; decide
      have factor_7_7 : (7 : ZMod 254963281) ^ 169 = 124143300 := by
        calc
          (7 : ZMod 254963281) ^ 169 = (7 : ZMod 254963281) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 84 * (7 : ZMod 254963281) ^ 84) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 124143300 := by rw [factor_7_6]; decide
      have factor_7_8 : (7 : ZMod 254963281) ^ 338 = 8540610 := by
        calc
          (7 : ZMod 254963281) ^ 338 = (7 : ZMod 254963281) ^ (169 + 169) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 169 * (7 : ZMod 254963281) ^ 169 := by rw [pow_add]
          _ = 8540610 := by rw [factor_7_7]; decide
      have factor_7_9 : (7 : ZMod 254963281) ^ 676 = 84037372 := by
        calc
          (7 : ZMod 254963281) ^ 676 = (7 : ZMod 254963281) ^ (338 + 338) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 338 * (7 : ZMod 254963281) ^ 338 := by rw [pow_add]
          _ = 84037372 := by rw [factor_7_8]; decide
      have factor_7_10 : (7 : ZMod 254963281) ^ 1353 = 228092982 := by
        calc
          (7 : ZMod 254963281) ^ 1353 = (7 : ZMod 254963281) ^ (676 + 676 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 676 * (7 : ZMod 254963281) ^ 676) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 228092982 := by rw [factor_7_9]; decide
      have factor_7_11 : (7 : ZMod 254963281) ^ 2706 = 45351890 := by
        calc
          (7 : ZMod 254963281) ^ 2706 = (7 : ZMod 254963281) ^ (1353 + 1353) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1353 * (7 : ZMod 254963281) ^ 1353 := by rw [pow_add]
          _ = 45351890 := by rw [factor_7_10]; decide
      have factor_7_12 : (7 : ZMod 254963281) ^ 5412 = 39479480 := by
        calc
          (7 : ZMod 254963281) ^ 5412 = (7 : ZMod 254963281) ^ (2706 + 2706) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 2706 * (7 : ZMod 254963281) ^ 2706 := by rw [pow_add]
          _ = 39479480 := by rw [factor_7_11]; decide
      have factor_7_13 : (7 : ZMod 254963281) ^ 10825 = 94327535 := by
        calc
          (7 : ZMod 254963281) ^ 10825 = (7 : ZMod 254963281) ^ (5412 + 5412 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 5412 * (7 : ZMod 254963281) ^ 5412) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 94327535 := by rw [factor_7_12]; decide
      have factor_7_14 : (7 : ZMod 254963281) ^ 21651 = 71935374 := by
        calc
          (7 : ZMod 254963281) ^ 21651 = (7 : ZMod 254963281) ^ (10825 + 10825 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 10825 * (7 : ZMod 254963281) ^ 10825) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 71935374 := by rw [factor_7_13]; decide
      have factor_7_15 : (7 : ZMod 254963281) ^ 43302 = 251019621 := by
        calc
          (7 : ZMod 254963281) ^ 43302 = (7 : ZMod 254963281) ^ (21651 + 21651) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 21651 * (7 : ZMod 254963281) ^ 21651 := by rw [pow_add]
          _ = 251019621 := by rw [factor_7_14]; decide
      have factor_7_16 : (7 : ZMod 254963281) ^ 86604 = 203981162 := by
        calc
          (7 : ZMod 254963281) ^ 86604 = (7 : ZMod 254963281) ^ (43302 + 43302) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 43302 * (7 : ZMod 254963281) ^ 43302 := by rw [pow_add]
          _ = 203981162 := by rw [factor_7_15]; decide
      have factor_7_17 : (7 : ZMod 254963281) ^ 173208 = 202819365 := by
        calc
          (7 : ZMod 254963281) ^ 173208 = (7 : ZMod 254963281) ^ (86604 + 86604) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 86604 * (7 : ZMod 254963281) ^ 86604 := by rw [pow_add]
          _ = 202819365 := by rw [factor_7_16]; decide
      have factor_7_18 : (7 : ZMod 254963281) ^ 346417 = 220616238 := by
        calc
          (7 : ZMod 254963281) ^ 346417 = (7 : ZMod 254963281) ^ (173208 + 173208 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 173208 * (7 : ZMod 254963281) ^ 173208) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 220616238 := by rw [factor_7_17]; decide
      have factor_7_19 : (7 : ZMod 254963281) ^ 692835 = 894066 := by
        calc
          (7 : ZMod 254963281) ^ 692835 = (7 : ZMod 254963281) ^ (346417 + 346417 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = ((7 : ZMod 254963281) ^ 346417 * (7 : ZMod 254963281) ^ 346417) * (7 : ZMod 254963281) := by rw [pow_succ, pow_add]
          _ = 894066 := by rw [factor_7_18]; decide
      have factor_7_20 : (7 : ZMod 254963281) ^ 1385670 = 44126421 := by
        calc
          (7 : ZMod 254963281) ^ 1385670 = (7 : ZMod 254963281) ^ (692835 + 692835) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 692835 * (7 : ZMod 254963281) ^ 692835 := by rw [pow_add]
          _ = 44126421 := by rw [factor_7_19]; decide
      have factor_7_21 : (7 : ZMod 254963281) ^ 2771340 = 221289415 := by
        calc
          (7 : ZMod 254963281) ^ 2771340 = (7 : ZMod 254963281) ^ (1385670 + 1385670) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 1385670 * (7 : ZMod 254963281) ^ 1385670 := by rw [pow_add]
          _ = 221289415 := by rw [factor_7_20]; decide
      have factor_7_22 : (7 : ZMod 254963281) ^ 5542680 = 201237655 := by
        calc
          (7 : ZMod 254963281) ^ 5542680 = (7 : ZMod 254963281) ^ (2771340 + 2771340) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 2771340 * (7 : ZMod 254963281) ^ 2771340 := by rw [pow_add]
          _ = 201237655 := by rw [factor_7_21]; decide
      have factor_7_23 : (7 : ZMod 254963281) ^ 11085360 = 15404942 := by
        calc
          (7 : ZMod 254963281) ^ 11085360 = (7 : ZMod 254963281) ^ (5542680 + 5542680) :=
            congrArg (fun n : ℕ => (7 : ZMod 254963281) ^ n) (by norm_num)
          _ = (7 : ZMod 254963281) ^ 5542680 * (7 : ZMod 254963281) ^ 5542680 := by rw [pow_add]
          _ = 15404942 := by rw [factor_7_22]; decide
      change (7 : ZMod 254963281) ^ 11085360 ≠ 1
      rw [factor_7_23]
      decide

#print axioms prime_lucas_254963281

end TotientTailPeriodKiller
end Erdos249257
