import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_797025869 : Nat.Prime 797025869 := by
  apply lucas_primality 797025869 (2 : ZMod 797025869)
  ·
      have fermat_0 : (2 : ZMod 797025869) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 797025869) ^ 2 = 4 := by
        calc
          (2 : ZMod 797025869) ^ 2 = (2 : ZMod 797025869) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 1 * (2 : ZMod 797025869) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 797025869) ^ 5 = 32 := by
        calc
          (2 : ZMod 797025869) ^ 5 = (2 : ZMod 797025869) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 2 * (2 : ZMod 797025869) ^ 2) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 797025869) ^ 11 = 2048 := by
        calc
          (2 : ZMod 797025869) ^ 11 = (2 : ZMod 797025869) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 5 * (2 : ZMod 797025869) ^ 5) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 797025869) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 797025869) ^ 23 = (2 : ZMod 797025869) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 11 * (2 : ZMod 797025869) ^ 11) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 797025869) ^ 47 = 254459046 := by
        calc
          (2 : ZMod 797025869) ^ 47 = (2 : ZMod 797025869) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 23 * (2 : ZMod 797025869) ^ 23) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 254459046 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 797025869) ^ 95 = 106667544 := by
        calc
          (2 : ZMod 797025869) ^ 95 = (2 : ZMod 797025869) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 47 * (2 : ZMod 797025869) ^ 47) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 106667544 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 797025869) ^ 190 = 630383973 := by
        calc
          (2 : ZMod 797025869) ^ 190 = (2 : ZMod 797025869) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 95 * (2 : ZMod 797025869) ^ 95 := by rw [pow_add]
          _ = 630383973 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 797025869) ^ 380 = 479522146 := by
        calc
          (2 : ZMod 797025869) ^ 380 = (2 : ZMod 797025869) ^ (190 + 190) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 190 * (2 : ZMod 797025869) ^ 190 := by rw [pow_add]
          _ = 479522146 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 797025869) ^ 760 = 325363240 := by
        calc
          (2 : ZMod 797025869) ^ 760 = (2 : ZMod 797025869) ^ (380 + 380) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 380 * (2 : ZMod 797025869) ^ 380 := by rw [pow_add]
          _ = 325363240 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 797025869) ^ 1520 = 598232568 := by
        calc
          (2 : ZMod 797025869) ^ 1520 = (2 : ZMod 797025869) ^ (760 + 760) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 760 * (2 : ZMod 797025869) ^ 760 := by rw [pow_add]
          _ = 598232568 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 797025869) ^ 3040 = 670971663 := by
        calc
          (2 : ZMod 797025869) ^ 3040 = (2 : ZMod 797025869) ^ (1520 + 1520) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 1520 * (2 : ZMod 797025869) ^ 1520 := by rw [pow_add]
          _ = 670971663 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 797025869) ^ 6080 = 502887850 := by
        calc
          (2 : ZMod 797025869) ^ 6080 = (2 : ZMod 797025869) ^ (3040 + 3040) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 3040 * (2 : ZMod 797025869) ^ 3040 := by rw [pow_add]
          _ = 502887850 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 797025869) ^ 12161 = 401553962 := by
        calc
          (2 : ZMod 797025869) ^ 12161 = (2 : ZMod 797025869) ^ (6080 + 6080 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 6080 * (2 : ZMod 797025869) ^ 6080) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 401553962 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 797025869) ^ 24323 = 312708433 := by
        calc
          (2 : ZMod 797025869) ^ 24323 = (2 : ZMod 797025869) ^ (12161 + 12161 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 12161 * (2 : ZMod 797025869) ^ 12161) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 312708433 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 797025869) ^ 48646 = 585244671 := by
        calc
          (2 : ZMod 797025869) ^ 48646 = (2 : ZMod 797025869) ^ (24323 + 24323) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 24323 * (2 : ZMod 797025869) ^ 24323 := by rw [pow_add]
          _ = 585244671 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 797025869) ^ 97293 = 781660877 := by
        calc
          (2 : ZMod 797025869) ^ 97293 = (2 : ZMod 797025869) ^ (48646 + 48646 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 48646 * (2 : ZMod 797025869) ^ 48646) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 781660877 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 797025869) ^ 194586 = 728658788 := by
        calc
          (2 : ZMod 797025869) ^ 194586 = (2 : ZMod 797025869) ^ (97293 + 97293) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 97293 * (2 : ZMod 797025869) ^ 97293 := by rw [pow_add]
          _ = 728658788 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 797025869) ^ 389172 = 777995424 := by
        calc
          (2 : ZMod 797025869) ^ 389172 = (2 : ZMod 797025869) ^ (194586 + 194586) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 194586 * (2 : ZMod 797025869) ^ 194586 := by rw [pow_add]
          _ = 777995424 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 797025869) ^ 778345 = 83747313 := by
        calc
          (2 : ZMod 797025869) ^ 778345 = (2 : ZMod 797025869) ^ (389172 + 389172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 389172 * (2 : ZMod 797025869) ^ 389172) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 83747313 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 797025869) ^ 1556691 = 766035067 := by
        calc
          (2 : ZMod 797025869) ^ 1556691 = (2 : ZMod 797025869) ^ (778345 + 778345 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 778345 * (2 : ZMod 797025869) ^ 778345) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 766035067 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 797025869) ^ 3113382 = 87018431 := by
        calc
          (2 : ZMod 797025869) ^ 3113382 = (2 : ZMod 797025869) ^ (1556691 + 1556691) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 1556691 * (2 : ZMod 797025869) ^ 1556691 := by rw [pow_add]
          _ = 87018431 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 797025869) ^ 6226764 = 100223610 := by
        calc
          (2 : ZMod 797025869) ^ 6226764 = (2 : ZMod 797025869) ^ (3113382 + 3113382) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 3113382 * (2 : ZMod 797025869) ^ 3113382 := by rw [pow_add]
          _ = 100223610 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 797025869) ^ 12453529 = 66266516 := by
        calc
          (2 : ZMod 797025869) ^ 12453529 = (2 : ZMod 797025869) ^ (6226764 + 6226764 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 6226764 * (2 : ZMod 797025869) ^ 6226764) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 66266516 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 797025869) ^ 24907058 = 454332782 := by
        calc
          (2 : ZMod 797025869) ^ 24907058 = (2 : ZMod 797025869) ^ (12453529 + 12453529) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 12453529 * (2 : ZMod 797025869) ^ 12453529 := by rw [pow_add]
          _ = 454332782 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 797025869) ^ 49814116 = 500639901 := by
        calc
          (2 : ZMod 797025869) ^ 49814116 = (2 : ZMod 797025869) ^ (24907058 + 24907058) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 24907058 * (2 : ZMod 797025869) ^ 24907058 := by rw [pow_add]
          _ = 500639901 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 797025869) ^ 99628233 = 601649231 := by
        calc
          (2 : ZMod 797025869) ^ 99628233 = (2 : ZMod 797025869) ^ (49814116 + 49814116 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 49814116 * (2 : ZMod 797025869) ^ 49814116) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 601649231 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 797025869) ^ 199256467 = 390753275 := by
        calc
          (2 : ZMod 797025869) ^ 199256467 = (2 : ZMod 797025869) ^ (99628233 + 99628233 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 99628233 * (2 : ZMod 797025869) ^ 99628233) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 390753275 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 797025869) ^ 398512934 = 797025868 := by
        calc
          (2 : ZMod 797025869) ^ 398512934 = (2 : ZMod 797025869) ^ (199256467 + 199256467) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 199256467 * (2 : ZMod 797025869) ^ 199256467 := by rw [pow_add]
          _ = 797025868 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 797025869) ^ 797025868 = 1 := by
        calc
          (2 : ZMod 797025869) ^ 797025868 = (2 : ZMod 797025869) ^ (398512934 + 398512934) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 398512934 * (2 : ZMod 797025869) ^ 398512934 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (661, 1), (301447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (661, 1), (301447, 1)] : List FactorBlock).map factorBlockValue).prod = 797025869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 797025869) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 797025869) ^ 2 = 4 := by
        calc
          (2 : ZMod 797025869) ^ 2 = (2 : ZMod 797025869) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 1 * (2 : ZMod 797025869) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 797025869) ^ 5 = 32 := by
        calc
          (2 : ZMod 797025869) ^ 5 = (2 : ZMod 797025869) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 2 * (2 : ZMod 797025869) ^ 2) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 797025869) ^ 11 = 2048 := by
        calc
          (2 : ZMod 797025869) ^ 11 = (2 : ZMod 797025869) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 5 * (2 : ZMod 797025869) ^ 5) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 797025869) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 797025869) ^ 23 = (2 : ZMod 797025869) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 11 * (2 : ZMod 797025869) ^ 11) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 797025869) ^ 47 = 254459046 := by
        calc
          (2 : ZMod 797025869) ^ 47 = (2 : ZMod 797025869) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 23 * (2 : ZMod 797025869) ^ 23) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 254459046 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 797025869) ^ 95 = 106667544 := by
        calc
          (2 : ZMod 797025869) ^ 95 = (2 : ZMod 797025869) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 47 * (2 : ZMod 797025869) ^ 47) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 106667544 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 797025869) ^ 190 = 630383973 := by
        calc
          (2 : ZMod 797025869) ^ 190 = (2 : ZMod 797025869) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 95 * (2 : ZMod 797025869) ^ 95 := by rw [pow_add]
          _ = 630383973 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 797025869) ^ 380 = 479522146 := by
        calc
          (2 : ZMod 797025869) ^ 380 = (2 : ZMod 797025869) ^ (190 + 190) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 190 * (2 : ZMod 797025869) ^ 190 := by rw [pow_add]
          _ = 479522146 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 797025869) ^ 760 = 325363240 := by
        calc
          (2 : ZMod 797025869) ^ 760 = (2 : ZMod 797025869) ^ (380 + 380) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 380 * (2 : ZMod 797025869) ^ 380 := by rw [pow_add]
          _ = 325363240 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 797025869) ^ 1520 = 598232568 := by
        calc
          (2 : ZMod 797025869) ^ 1520 = (2 : ZMod 797025869) ^ (760 + 760) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 760 * (2 : ZMod 797025869) ^ 760 := by rw [pow_add]
          _ = 598232568 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 797025869) ^ 3040 = 670971663 := by
        calc
          (2 : ZMod 797025869) ^ 3040 = (2 : ZMod 797025869) ^ (1520 + 1520) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 1520 * (2 : ZMod 797025869) ^ 1520 := by rw [pow_add]
          _ = 670971663 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 797025869) ^ 6080 = 502887850 := by
        calc
          (2 : ZMod 797025869) ^ 6080 = (2 : ZMod 797025869) ^ (3040 + 3040) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 3040 * (2 : ZMod 797025869) ^ 3040 := by rw [pow_add]
          _ = 502887850 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 797025869) ^ 12161 = 401553962 := by
        calc
          (2 : ZMod 797025869) ^ 12161 = (2 : ZMod 797025869) ^ (6080 + 6080 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 6080 * (2 : ZMod 797025869) ^ 6080) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 401553962 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 797025869) ^ 24323 = 312708433 := by
        calc
          (2 : ZMod 797025869) ^ 24323 = (2 : ZMod 797025869) ^ (12161 + 12161 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 12161 * (2 : ZMod 797025869) ^ 12161) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 312708433 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 797025869) ^ 48646 = 585244671 := by
        calc
          (2 : ZMod 797025869) ^ 48646 = (2 : ZMod 797025869) ^ (24323 + 24323) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 24323 * (2 : ZMod 797025869) ^ 24323 := by rw [pow_add]
          _ = 585244671 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 797025869) ^ 97293 = 781660877 := by
        calc
          (2 : ZMod 797025869) ^ 97293 = (2 : ZMod 797025869) ^ (48646 + 48646 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 48646 * (2 : ZMod 797025869) ^ 48646) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 781660877 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 797025869) ^ 194586 = 728658788 := by
        calc
          (2 : ZMod 797025869) ^ 194586 = (2 : ZMod 797025869) ^ (97293 + 97293) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 97293 * (2 : ZMod 797025869) ^ 97293 := by rw [pow_add]
          _ = 728658788 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 797025869) ^ 389172 = 777995424 := by
        calc
          (2 : ZMod 797025869) ^ 389172 = (2 : ZMod 797025869) ^ (194586 + 194586) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 194586 * (2 : ZMod 797025869) ^ 194586 := by rw [pow_add]
          _ = 777995424 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 797025869) ^ 778345 = 83747313 := by
        calc
          (2 : ZMod 797025869) ^ 778345 = (2 : ZMod 797025869) ^ (389172 + 389172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 389172 * (2 : ZMod 797025869) ^ 389172) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 83747313 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 797025869) ^ 1556691 = 766035067 := by
        calc
          (2 : ZMod 797025869) ^ 1556691 = (2 : ZMod 797025869) ^ (778345 + 778345 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 778345 * (2 : ZMod 797025869) ^ 778345) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 766035067 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 797025869) ^ 3113382 = 87018431 := by
        calc
          (2 : ZMod 797025869) ^ 3113382 = (2 : ZMod 797025869) ^ (1556691 + 1556691) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 1556691 * (2 : ZMod 797025869) ^ 1556691 := by rw [pow_add]
          _ = 87018431 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 797025869) ^ 6226764 = 100223610 := by
        calc
          (2 : ZMod 797025869) ^ 6226764 = (2 : ZMod 797025869) ^ (3113382 + 3113382) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 3113382 * (2 : ZMod 797025869) ^ 3113382 := by rw [pow_add]
          _ = 100223610 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 797025869) ^ 12453529 = 66266516 := by
        calc
          (2 : ZMod 797025869) ^ 12453529 = (2 : ZMod 797025869) ^ (6226764 + 6226764 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 6226764 * (2 : ZMod 797025869) ^ 6226764) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 66266516 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 797025869) ^ 24907058 = 454332782 := by
        calc
          (2 : ZMod 797025869) ^ 24907058 = (2 : ZMod 797025869) ^ (12453529 + 12453529) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 12453529 * (2 : ZMod 797025869) ^ 12453529 := by rw [pow_add]
          _ = 454332782 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 797025869) ^ 49814116 = 500639901 := by
        calc
          (2 : ZMod 797025869) ^ 49814116 = (2 : ZMod 797025869) ^ (24907058 + 24907058) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 24907058 * (2 : ZMod 797025869) ^ 24907058 := by rw [pow_add]
          _ = 500639901 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 797025869) ^ 99628233 = 601649231 := by
        calc
          (2 : ZMod 797025869) ^ 99628233 = (2 : ZMod 797025869) ^ (49814116 + 49814116 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 49814116 * (2 : ZMod 797025869) ^ 49814116) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 601649231 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 797025869) ^ 199256467 = 390753275 := by
        calc
          (2 : ZMod 797025869) ^ 199256467 = (2 : ZMod 797025869) ^ (99628233 + 99628233 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 99628233 * (2 : ZMod 797025869) ^ 99628233) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 390753275 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 797025869) ^ 398512934 = 797025868 := by
        calc
          (2 : ZMod 797025869) ^ 398512934 = (2 : ZMod 797025869) ^ (199256467 + 199256467) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 199256467 * (2 : ZMod 797025869) ^ 199256467 := by rw [pow_add]
          _ = 797025868 := by rw [factor_0_27]; decide
      change (2 : ZMod 797025869) ^ 398512934 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 797025869) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 797025869) ^ 2 = 4 := by
        calc
          (2 : ZMod 797025869) ^ 2 = (2 : ZMod 797025869) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 1 * (2 : ZMod 797025869) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 797025869) ^ 4 = 16 := by
        calc
          (2 : ZMod 797025869) ^ 4 = (2 : ZMod 797025869) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 2 * (2 : ZMod 797025869) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 797025869) ^ 9 = 512 := by
        calc
          (2 : ZMod 797025869) ^ 9 = (2 : ZMod 797025869) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 4 * (2 : ZMod 797025869) ^ 4) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 797025869) ^ 18 = 262144 := by
        calc
          (2 : ZMod 797025869) ^ 18 = (2 : ZMod 797025869) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 9 * (2 : ZMod 797025869) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 797025869) ^ 36 = 175252002 := by
        calc
          (2 : ZMod 797025869) ^ 36 = (2 : ZMod 797025869) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 18 * (2 : ZMod 797025869) ^ 18 := by rw [pow_add]
          _ = 175252002 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 797025869) ^ 73 = 531489957 := by
        calc
          (2 : ZMod 797025869) ^ 73 = (2 : ZMod 797025869) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 36 * (2 : ZMod 797025869) ^ 36) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 531489957 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 797025869) ^ 147 = 506467789 := by
        calc
          (2 : ZMod 797025869) ^ 147 = (2 : ZMod 797025869) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 73 * (2 : ZMod 797025869) ^ 73) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 506467789 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 797025869) ^ 294 = 268866366 := by
        calc
          (2 : ZMod 797025869) ^ 294 = (2 : ZMod 797025869) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 147 * (2 : ZMod 797025869) ^ 147 := by rw [pow_add]
          _ = 268866366 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 797025869) ^ 588 = 254221246 := by
        calc
          (2 : ZMod 797025869) ^ 588 = (2 : ZMod 797025869) ^ (294 + 294) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 294 * (2 : ZMod 797025869) ^ 294 := by rw [pow_add]
          _ = 254221246 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 797025869) ^ 1177 = 195042735 := by
        calc
          (2 : ZMod 797025869) ^ 1177 = (2 : ZMod 797025869) ^ (588 + 588 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 588 * (2 : ZMod 797025869) ^ 588) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 195042735 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 797025869) ^ 2355 = 687266655 := by
        calc
          (2 : ZMod 797025869) ^ 2355 = (2 : ZMod 797025869) ^ (1177 + 1177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 1177 * (2 : ZMod 797025869) ^ 1177) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 687266655 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 797025869) ^ 4710 = 790721084 := by
        calc
          (2 : ZMod 797025869) ^ 4710 = (2 : ZMod 797025869) ^ (2355 + 2355) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 2355 * (2 : ZMod 797025869) ^ 2355 := by rw [pow_add]
          _ = 790721084 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 797025869) ^ 9420 = 242731588 := by
        calc
          (2 : ZMod 797025869) ^ 9420 = (2 : ZMod 797025869) ^ (4710 + 4710) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 4710 * (2 : ZMod 797025869) ^ 4710 := by rw [pow_add]
          _ = 242731588 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 797025869) ^ 18840 = 796327844 := by
        calc
          (2 : ZMod 797025869) ^ 18840 = (2 : ZMod 797025869) ^ (9420 + 9420) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 9420 * (2 : ZMod 797025869) ^ 9420 := by rw [pow_add]
          _ = 796327844 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 797025869) ^ 37680 = 256094666 := by
        calc
          (2 : ZMod 797025869) ^ 37680 = (2 : ZMod 797025869) ^ (18840 + 18840) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 18840 * (2 : ZMod 797025869) ^ 18840 := by rw [pow_add]
          _ = 256094666 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 797025869) ^ 75361 = 33796994 := by
        calc
          (2 : ZMod 797025869) ^ 75361 = (2 : ZMod 797025869) ^ (37680 + 37680 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 37680 * (2 : ZMod 797025869) ^ 37680) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 33796994 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 797025869) ^ 150723 = 600928429 := by
        calc
          (2 : ZMod 797025869) ^ 150723 = (2 : ZMod 797025869) ^ (75361 + 75361 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 75361 * (2 : ZMod 797025869) ^ 75361) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 600928429 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 797025869) ^ 301447 = 83405688 := by
        calc
          (2 : ZMod 797025869) ^ 301447 = (2 : ZMod 797025869) ^ (150723 + 150723 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 150723 * (2 : ZMod 797025869) ^ 150723) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 83405688 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 797025869) ^ 602894 = 55948348 := by
        calc
          (2 : ZMod 797025869) ^ 602894 = (2 : ZMod 797025869) ^ (301447 + 301447) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 301447 * (2 : ZMod 797025869) ^ 301447 := by rw [pow_add]
          _ = 55948348 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 797025869) ^ 1205788 = 562742836 := by
        calc
          (2 : ZMod 797025869) ^ 1205788 = (2 : ZMod 797025869) ^ (602894 + 602894) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 602894 * (2 : ZMod 797025869) ^ 602894 := by rw [pow_add]
          _ = 562742836 := by rw [factor_1_19]; decide
      change (2 : ZMod 797025869) ^ 1205788 ≠ 1
      rw [factor_1_20]
      decide
    ·
      have factor_2_0 : (2 : ZMod 797025869) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 797025869) ^ 2 = 4 := by
        calc
          (2 : ZMod 797025869) ^ 2 = (2 : ZMod 797025869) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 1 * (2 : ZMod 797025869) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 797025869) ^ 5 = 32 := by
        calc
          (2 : ZMod 797025869) ^ 5 = (2 : ZMod 797025869) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 2 * (2 : ZMod 797025869) ^ 2) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 797025869) ^ 10 = 1024 := by
        calc
          (2 : ZMod 797025869) ^ 10 = (2 : ZMod 797025869) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 5 * (2 : ZMod 797025869) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 797025869) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 797025869) ^ 20 = (2 : ZMod 797025869) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 10 * (2 : ZMod 797025869) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 797025869) ^ 41 = 28882981 := by
        calc
          (2 : ZMod 797025869) ^ 41 = (2 : ZMod 797025869) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 20 * (2 : ZMod 797025869) ^ 20) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 28882981 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 797025869) ^ 82 = 337036655 := by
        calc
          (2 : ZMod 797025869) ^ 82 = (2 : ZMod 797025869) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 41 * (2 : ZMod 797025869) ^ 41 := by rw [pow_add]
          _ = 337036655 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 797025869) ^ 165 = 516873334 := by
        calc
          (2 : ZMod 797025869) ^ 165 = (2 : ZMod 797025869) ^ (82 + 82 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 82 * (2 : ZMod 797025869) ^ 82) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 516873334 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 797025869) ^ 330 = 547683077 := by
        calc
          (2 : ZMod 797025869) ^ 330 = (2 : ZMod 797025869) ^ (165 + 165) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 165 * (2 : ZMod 797025869) ^ 165 := by rw [pow_add]
          _ = 547683077 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 797025869) ^ 661 = 713402888 := by
        calc
          (2 : ZMod 797025869) ^ 661 = (2 : ZMod 797025869) ^ (330 + 330 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = ((2 : ZMod 797025869) ^ 330 * (2 : ZMod 797025869) ^ 330) * (2 : ZMod 797025869) := by rw [pow_succ, pow_add]
          _ = 713402888 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 797025869) ^ 1322 = 49524712 := by
        calc
          (2 : ZMod 797025869) ^ 1322 = (2 : ZMod 797025869) ^ (661 + 661) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 661 * (2 : ZMod 797025869) ^ 661 := by rw [pow_add]
          _ = 49524712 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 797025869) ^ 2644 = 624724685 := by
        calc
          (2 : ZMod 797025869) ^ 2644 = (2 : ZMod 797025869) ^ (1322 + 1322) :=
            congrArg (fun n : ℕ => (2 : ZMod 797025869) ^ n) (by norm_num)
          _ = (2 : ZMod 797025869) ^ 1322 * (2 : ZMod 797025869) ^ 1322 := by rw [pow_add]
          _ = 624724685 := by rw [factor_2_10]; decide
      change (2 : ZMod 797025869) ^ 2644 ≠ 1
      rw [factor_2_11]
      decide

#print axioms prime_lucas_797025869

end TotientTailPeriodKiller
end Erdos249257
