import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_912793213 : Nat.Prime 912793213 := by
  apply lucas_primality 912793213 (2 : ZMod 912793213)
  ·
      have fermat_0 : (2 : ZMod 912793213) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 912793213) ^ 3 = 8 := by
        calc
          (2 : ZMod 912793213) ^ 3 = (2 : ZMod 912793213) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 1 * (2 : ZMod 912793213) ^ 1) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 912793213) ^ 6 = 64 := by
        calc
          (2 : ZMod 912793213) ^ 6 = (2 : ZMod 912793213) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 3 * (2 : ZMod 912793213) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 912793213) ^ 13 = 8192 := by
        calc
          (2 : ZMod 912793213) ^ 13 = (2 : ZMod 912793213) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 6 * (2 : ZMod 912793213) ^ 6) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 912793213) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 912793213) ^ 27 = (2 : ZMod 912793213) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 13 * (2 : ZMod 912793213) ^ 13) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 912793213) ^ 54 = 2082939 := by
        calc
          (2 : ZMod 912793213) ^ 54 = (2 : ZMod 912793213) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 27 * (2 : ZMod 912793213) ^ 27 := by rw [pow_add]
          _ = 2082939 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 912793213) ^ 108 = 128736332 := by
        calc
          (2 : ZMod 912793213) ^ 108 = (2 : ZMod 912793213) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 54 * (2 : ZMod 912793213) ^ 54 := by rw [pow_add]
          _ = 128736332 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 912793213) ^ 217 = 753463131 := by
        calc
          (2 : ZMod 912793213) ^ 217 = (2 : ZMod 912793213) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 108 * (2 : ZMod 912793213) ^ 108) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 753463131 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 912793213) ^ 435 = 133261741 := by
        calc
          (2 : ZMod 912793213) ^ 435 = (2 : ZMod 912793213) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 217 * (2 : ZMod 912793213) ^ 217) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 133261741 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 912793213) ^ 870 = 259262217 := by
        calc
          (2 : ZMod 912793213) ^ 870 = (2 : ZMod 912793213) ^ (435 + 435) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 435 * (2 : ZMod 912793213) ^ 435 := by rw [pow_add]
          _ = 259262217 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 912793213) ^ 1741 = 522295025 := by
        calc
          (2 : ZMod 912793213) ^ 1741 = (2 : ZMod 912793213) ^ (870 + 870 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 870 * (2 : ZMod 912793213) ^ 870) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 522295025 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 912793213) ^ 3482 = 400860321 := by
        calc
          (2 : ZMod 912793213) ^ 3482 = (2 : ZMod 912793213) ^ (1741 + 1741) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 1741 * (2 : ZMod 912793213) ^ 1741 := by rw [pow_add]
          _ = 400860321 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 912793213) ^ 6964 = 715838922 := by
        calc
          (2 : ZMod 912793213) ^ 6964 = (2 : ZMod 912793213) ^ (3482 + 3482) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 3482 * (2 : ZMod 912793213) ^ 3482 := by rw [pow_add]
          _ = 715838922 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 912793213) ^ 13928 = 401794208 := by
        calc
          (2 : ZMod 912793213) ^ 13928 = (2 : ZMod 912793213) ^ (6964 + 6964) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 6964 * (2 : ZMod 912793213) ^ 6964 := by rw [pow_add]
          _ = 401794208 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 912793213) ^ 27856 = 821067906 := by
        calc
          (2 : ZMod 912793213) ^ 27856 = (2 : ZMod 912793213) ^ (13928 + 13928) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 13928 * (2 : ZMod 912793213) ^ 13928 := by rw [pow_add]
          _ = 821067906 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 912793213) ^ 55712 = 160778338 := by
        calc
          (2 : ZMod 912793213) ^ 55712 = (2 : ZMod 912793213) ^ (27856 + 27856) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 27856 * (2 : ZMod 912793213) ^ 27856 := by rw [pow_add]
          _ = 160778338 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 912793213) ^ 111424 = 5199214 := by
        calc
          (2 : ZMod 912793213) ^ 111424 = (2 : ZMod 912793213) ^ (55712 + 55712) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 55712 * (2 : ZMod 912793213) ^ 55712 := by rw [pow_add]
          _ = 5199214 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 912793213) ^ 222849 = 736016028 := by
        calc
          (2 : ZMod 912793213) ^ 222849 = (2 : ZMod 912793213) ^ (111424 + 111424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 111424 * (2 : ZMod 912793213) ^ 111424) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 736016028 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 912793213) ^ 445699 = 230908986 := by
        calc
          (2 : ZMod 912793213) ^ 445699 = (2 : ZMod 912793213) ^ (222849 + 222849 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 222849 * (2 : ZMod 912793213) ^ 222849) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 230908986 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 912793213) ^ 891399 = 886303663 := by
        calc
          (2 : ZMod 912793213) ^ 891399 = (2 : ZMod 912793213) ^ (445699 + 445699 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 445699 * (2 : ZMod 912793213) ^ 445699) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 886303663 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 912793213) ^ 1782799 = 337213890 := by
        calc
          (2 : ZMod 912793213) ^ 1782799 = (2 : ZMod 912793213) ^ (891399 + 891399 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 891399 * (2 : ZMod 912793213) ^ 891399) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 337213890 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 912793213) ^ 3565598 = 471873121 := by
        calc
          (2 : ZMod 912793213) ^ 3565598 = (2 : ZMod 912793213) ^ (1782799 + 1782799) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 1782799 * (2 : ZMod 912793213) ^ 1782799 := by rw [pow_add]
          _ = 471873121 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 912793213) ^ 7131196 = 769813142 := by
        calc
          (2 : ZMod 912793213) ^ 7131196 = (2 : ZMod 912793213) ^ (3565598 + 3565598) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 3565598 * (2 : ZMod 912793213) ^ 3565598 := by rw [pow_add]
          _ = 769813142 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 912793213) ^ 14262393 = 150541949 := by
        calc
          (2 : ZMod 912793213) ^ 14262393 = (2 : ZMod 912793213) ^ (7131196 + 7131196 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 7131196 * (2 : ZMod 912793213) ^ 7131196) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 150541949 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 912793213) ^ 28524787 = 276628624 := by
        calc
          (2 : ZMod 912793213) ^ 28524787 = (2 : ZMod 912793213) ^ (14262393 + 14262393 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 14262393 * (2 : ZMod 912793213) ^ 14262393) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 276628624 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 912793213) ^ 57049575 = 84085710 := by
        calc
          (2 : ZMod 912793213) ^ 57049575 = (2 : ZMod 912793213) ^ (28524787 + 28524787 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 28524787 * (2 : ZMod 912793213) ^ 28524787) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 84085710 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 912793213) ^ 114099151 = 616875161 := by
        calc
          (2 : ZMod 912793213) ^ 114099151 = (2 : ZMod 912793213) ^ (57049575 + 57049575 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 57049575 * (2 : ZMod 912793213) ^ 57049575) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 616875161 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 912793213) ^ 228198303 = 320957108 := by
        calc
          (2 : ZMod 912793213) ^ 228198303 = (2 : ZMod 912793213) ^ (114099151 + 114099151 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 114099151 * (2 : ZMod 912793213) ^ 114099151) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 320957108 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 912793213) ^ 456396606 = 912793212 := by
        calc
          (2 : ZMod 912793213) ^ 456396606 = (2 : ZMod 912793213) ^ (228198303 + 228198303) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 228198303 * (2 : ZMod 912793213) ^ 228198303 := by rw [pow_add]
          _ = 912793212 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 912793213) ^ 912793212 = 1 := by
        calc
          (2 : ZMod 912793213) ^ 912793212 = (2 : ZMod 912793213) ^ (456396606 + 456396606) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 456396606 * (2 : ZMod 912793213) ^ 456396606 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 4), (19, 1), (29, 1), (5113, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 4), (19, 1), (29, 1), (5113, 1)] : List FactorBlock).map factorBlockValue).prod = 912793213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 912793213) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 912793213) ^ 3 = 8 := by
        calc
          (2 : ZMod 912793213) ^ 3 = (2 : ZMod 912793213) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 1 * (2 : ZMod 912793213) ^ 1) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 912793213) ^ 6 = 64 := by
        calc
          (2 : ZMod 912793213) ^ 6 = (2 : ZMod 912793213) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 3 * (2 : ZMod 912793213) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 912793213) ^ 13 = 8192 := by
        calc
          (2 : ZMod 912793213) ^ 13 = (2 : ZMod 912793213) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 6 * (2 : ZMod 912793213) ^ 6) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 912793213) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 912793213) ^ 27 = (2 : ZMod 912793213) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 13 * (2 : ZMod 912793213) ^ 13) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 912793213) ^ 54 = 2082939 := by
        calc
          (2 : ZMod 912793213) ^ 54 = (2 : ZMod 912793213) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 27 * (2 : ZMod 912793213) ^ 27 := by rw [pow_add]
          _ = 2082939 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 912793213) ^ 108 = 128736332 := by
        calc
          (2 : ZMod 912793213) ^ 108 = (2 : ZMod 912793213) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 54 * (2 : ZMod 912793213) ^ 54 := by rw [pow_add]
          _ = 128736332 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 912793213) ^ 217 = 753463131 := by
        calc
          (2 : ZMod 912793213) ^ 217 = (2 : ZMod 912793213) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 108 * (2 : ZMod 912793213) ^ 108) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 753463131 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 912793213) ^ 435 = 133261741 := by
        calc
          (2 : ZMod 912793213) ^ 435 = (2 : ZMod 912793213) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 217 * (2 : ZMod 912793213) ^ 217) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 133261741 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 912793213) ^ 870 = 259262217 := by
        calc
          (2 : ZMod 912793213) ^ 870 = (2 : ZMod 912793213) ^ (435 + 435) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 435 * (2 : ZMod 912793213) ^ 435 := by rw [pow_add]
          _ = 259262217 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 912793213) ^ 1741 = 522295025 := by
        calc
          (2 : ZMod 912793213) ^ 1741 = (2 : ZMod 912793213) ^ (870 + 870 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 870 * (2 : ZMod 912793213) ^ 870) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 522295025 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 912793213) ^ 3482 = 400860321 := by
        calc
          (2 : ZMod 912793213) ^ 3482 = (2 : ZMod 912793213) ^ (1741 + 1741) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 1741 * (2 : ZMod 912793213) ^ 1741 := by rw [pow_add]
          _ = 400860321 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 912793213) ^ 6964 = 715838922 := by
        calc
          (2 : ZMod 912793213) ^ 6964 = (2 : ZMod 912793213) ^ (3482 + 3482) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 3482 * (2 : ZMod 912793213) ^ 3482 := by rw [pow_add]
          _ = 715838922 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 912793213) ^ 13928 = 401794208 := by
        calc
          (2 : ZMod 912793213) ^ 13928 = (2 : ZMod 912793213) ^ (6964 + 6964) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 6964 * (2 : ZMod 912793213) ^ 6964 := by rw [pow_add]
          _ = 401794208 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 912793213) ^ 27856 = 821067906 := by
        calc
          (2 : ZMod 912793213) ^ 27856 = (2 : ZMod 912793213) ^ (13928 + 13928) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 13928 * (2 : ZMod 912793213) ^ 13928 := by rw [pow_add]
          _ = 821067906 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 912793213) ^ 55712 = 160778338 := by
        calc
          (2 : ZMod 912793213) ^ 55712 = (2 : ZMod 912793213) ^ (27856 + 27856) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 27856 * (2 : ZMod 912793213) ^ 27856 := by rw [pow_add]
          _ = 160778338 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 912793213) ^ 111424 = 5199214 := by
        calc
          (2 : ZMod 912793213) ^ 111424 = (2 : ZMod 912793213) ^ (55712 + 55712) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 55712 * (2 : ZMod 912793213) ^ 55712 := by rw [pow_add]
          _ = 5199214 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 912793213) ^ 222849 = 736016028 := by
        calc
          (2 : ZMod 912793213) ^ 222849 = (2 : ZMod 912793213) ^ (111424 + 111424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 111424 * (2 : ZMod 912793213) ^ 111424) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 736016028 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 912793213) ^ 445699 = 230908986 := by
        calc
          (2 : ZMod 912793213) ^ 445699 = (2 : ZMod 912793213) ^ (222849 + 222849 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 222849 * (2 : ZMod 912793213) ^ 222849) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 230908986 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 912793213) ^ 891399 = 886303663 := by
        calc
          (2 : ZMod 912793213) ^ 891399 = (2 : ZMod 912793213) ^ (445699 + 445699 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 445699 * (2 : ZMod 912793213) ^ 445699) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 886303663 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 912793213) ^ 1782799 = 337213890 := by
        calc
          (2 : ZMod 912793213) ^ 1782799 = (2 : ZMod 912793213) ^ (891399 + 891399 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 891399 * (2 : ZMod 912793213) ^ 891399) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 337213890 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 912793213) ^ 3565598 = 471873121 := by
        calc
          (2 : ZMod 912793213) ^ 3565598 = (2 : ZMod 912793213) ^ (1782799 + 1782799) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 1782799 * (2 : ZMod 912793213) ^ 1782799 := by rw [pow_add]
          _ = 471873121 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 912793213) ^ 7131196 = 769813142 := by
        calc
          (2 : ZMod 912793213) ^ 7131196 = (2 : ZMod 912793213) ^ (3565598 + 3565598) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 3565598 * (2 : ZMod 912793213) ^ 3565598 := by rw [pow_add]
          _ = 769813142 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 912793213) ^ 14262393 = 150541949 := by
        calc
          (2 : ZMod 912793213) ^ 14262393 = (2 : ZMod 912793213) ^ (7131196 + 7131196 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 7131196 * (2 : ZMod 912793213) ^ 7131196) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 150541949 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 912793213) ^ 28524787 = 276628624 := by
        calc
          (2 : ZMod 912793213) ^ 28524787 = (2 : ZMod 912793213) ^ (14262393 + 14262393 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 14262393 * (2 : ZMod 912793213) ^ 14262393) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 276628624 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 912793213) ^ 57049575 = 84085710 := by
        calc
          (2 : ZMod 912793213) ^ 57049575 = (2 : ZMod 912793213) ^ (28524787 + 28524787 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 28524787 * (2 : ZMod 912793213) ^ 28524787) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 84085710 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 912793213) ^ 114099151 = 616875161 := by
        calc
          (2 : ZMod 912793213) ^ 114099151 = (2 : ZMod 912793213) ^ (57049575 + 57049575 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 57049575 * (2 : ZMod 912793213) ^ 57049575) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 616875161 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 912793213) ^ 228198303 = 320957108 := by
        calc
          (2 : ZMod 912793213) ^ 228198303 = (2 : ZMod 912793213) ^ (114099151 + 114099151 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 114099151 * (2 : ZMod 912793213) ^ 114099151) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 320957108 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 912793213) ^ 456396606 = 912793212 := by
        calc
          (2 : ZMod 912793213) ^ 456396606 = (2 : ZMod 912793213) ^ (228198303 + 228198303) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 228198303 * (2 : ZMod 912793213) ^ 228198303 := by rw [pow_add]
          _ = 912793212 := by rw [factor_0_27]; decide
      change (2 : ZMod 912793213) ^ 456396606 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 912793213) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 912793213) ^ 2 = 4 := by
        calc
          (2 : ZMod 912793213) ^ 2 = (2 : ZMod 912793213) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 1 * (2 : ZMod 912793213) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 912793213) ^ 4 = 16 := by
        calc
          (2 : ZMod 912793213) ^ 4 = (2 : ZMod 912793213) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 2 * (2 : ZMod 912793213) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 912793213) ^ 9 = 512 := by
        calc
          (2 : ZMod 912793213) ^ 9 = (2 : ZMod 912793213) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 4 * (2 : ZMod 912793213) ^ 4) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 912793213) ^ 18 = 262144 := by
        calc
          (2 : ZMod 912793213) ^ 18 = (2 : ZMod 912793213) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 9 * (2 : ZMod 912793213) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 912793213) ^ 36 = 259985761 := by
        calc
          (2 : ZMod 912793213) ^ 36 = (2 : ZMod 912793213) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 18 * (2 : ZMod 912793213) ^ 18 := by rw [pow_add]
          _ = 259985761 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 912793213) ^ 72 = 179619842 := by
        calc
          (2 : ZMod 912793213) ^ 72 = (2 : ZMod 912793213) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 36 * (2 : ZMod 912793213) ^ 36 := by rw [pow_add]
          _ = 179619842 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 912793213) ^ 145 = 823127721 := by
        calc
          (2 : ZMod 912793213) ^ 145 = (2 : ZMod 912793213) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 72 * (2 : ZMod 912793213) ^ 72) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 823127721 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 912793213) ^ 290 = 492427017 := by
        calc
          (2 : ZMod 912793213) ^ 290 = (2 : ZMod 912793213) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 145 * (2 : ZMod 912793213) ^ 145 := by rw [pow_add]
          _ = 492427017 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 912793213) ^ 580 = 227586986 := by
        calc
          (2 : ZMod 912793213) ^ 580 = (2 : ZMod 912793213) ^ (290 + 290) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 290 * (2 : ZMod 912793213) ^ 290 := by rw [pow_add]
          _ = 227586986 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 912793213) ^ 1160 = 547504758 := by
        calc
          (2 : ZMod 912793213) ^ 1160 = (2 : ZMod 912793213) ^ (580 + 580) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 580 * (2 : ZMod 912793213) ^ 580 := by rw [pow_add]
          _ = 547504758 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 912793213) ^ 2321 = 33388318 := by
        calc
          (2 : ZMod 912793213) ^ 2321 = (2 : ZMod 912793213) ^ (1160 + 1160 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 1160 * (2 : ZMod 912793213) ^ 1160) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 33388318 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 912793213) ^ 4642 = 32523632 := by
        calc
          (2 : ZMod 912793213) ^ 4642 = (2 : ZMod 912793213) ^ (2321 + 2321) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 2321 * (2 : ZMod 912793213) ^ 2321 := by rw [pow_add]
          _ = 32523632 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 912793213) ^ 9285 = 662311665 := by
        calc
          (2 : ZMod 912793213) ^ 9285 = (2 : ZMod 912793213) ^ (4642 + 4642 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 4642 * (2 : ZMod 912793213) ^ 4642) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 662311665 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 912793213) ^ 18570 = 90142964 := by
        calc
          (2 : ZMod 912793213) ^ 18570 = (2 : ZMod 912793213) ^ (9285 + 9285) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 9285 * (2 : ZMod 912793213) ^ 9285 := by rw [pow_add]
          _ = 90142964 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 912793213) ^ 37141 = 634176642 := by
        calc
          (2 : ZMod 912793213) ^ 37141 = (2 : ZMod 912793213) ^ (18570 + 18570 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 18570 * (2 : ZMod 912793213) ^ 18570) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 634176642 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 912793213) ^ 74283 = 261015262 := by
        calc
          (2 : ZMod 912793213) ^ 74283 = (2 : ZMod 912793213) ^ (37141 + 37141 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 37141 * (2 : ZMod 912793213) ^ 37141) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 261015262 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 912793213) ^ 148566 = 269942370 := by
        calc
          (2 : ZMod 912793213) ^ 148566 = (2 : ZMod 912793213) ^ (74283 + 74283) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 74283 * (2 : ZMod 912793213) ^ 74283 := by rw [pow_add]
          _ = 269942370 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 912793213) ^ 297133 = 618985492 := by
        calc
          (2 : ZMod 912793213) ^ 297133 = (2 : ZMod 912793213) ^ (148566 + 148566 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 148566 * (2 : ZMod 912793213) ^ 148566) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 618985492 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 912793213) ^ 594266 = 451513299 := by
        calc
          (2 : ZMod 912793213) ^ 594266 = (2 : ZMod 912793213) ^ (297133 + 297133) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 297133 * (2 : ZMod 912793213) ^ 297133 := by rw [pow_add]
          _ = 451513299 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 912793213) ^ 1188532 = 654044841 := by
        calc
          (2 : ZMod 912793213) ^ 1188532 = (2 : ZMod 912793213) ^ (594266 + 594266) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 594266 * (2 : ZMod 912793213) ^ 594266 := by rw [pow_add]
          _ = 654044841 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 912793213) ^ 2377065 = 1012197 := by
        calc
          (2 : ZMod 912793213) ^ 2377065 = (2 : ZMod 912793213) ^ (1188532 + 1188532 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 1188532 * (2 : ZMod 912793213) ^ 1188532) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 1012197 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 912793213) ^ 4754131 = 777563646 := by
        calc
          (2 : ZMod 912793213) ^ 4754131 = (2 : ZMod 912793213) ^ (2377065 + 2377065 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 2377065 * (2 : ZMod 912793213) ^ 2377065) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 777563646 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 912793213) ^ 9508262 = 555576752 := by
        calc
          (2 : ZMod 912793213) ^ 9508262 = (2 : ZMod 912793213) ^ (4754131 + 4754131) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 4754131 * (2 : ZMod 912793213) ^ 4754131 := by rw [pow_add]
          _ = 555576752 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 912793213) ^ 19016525 = 68792763 := by
        calc
          (2 : ZMod 912793213) ^ 19016525 = (2 : ZMod 912793213) ^ (9508262 + 9508262 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 9508262 * (2 : ZMod 912793213) ^ 9508262) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 68792763 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 912793213) ^ 38033050 = 281677907 := by
        calc
          (2 : ZMod 912793213) ^ 38033050 = (2 : ZMod 912793213) ^ (19016525 + 19016525) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 19016525 * (2 : ZMod 912793213) ^ 19016525 := by rw [pow_add]
          _ = 281677907 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 912793213) ^ 76066101 = 870015719 := by
        calc
          (2 : ZMod 912793213) ^ 76066101 = (2 : ZMod 912793213) ^ (38033050 + 38033050 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 38033050 * (2 : ZMod 912793213) ^ 38033050) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 870015719 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 912793213) ^ 152132202 = 14297203 := by
        calc
          (2 : ZMod 912793213) ^ 152132202 = (2 : ZMod 912793213) ^ (76066101 + 76066101) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 76066101 * (2 : ZMod 912793213) ^ 76066101 := by rw [pow_add]
          _ = 14297203 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 912793213) ^ 304264404 = 14297202 := by
        calc
          (2 : ZMod 912793213) ^ 304264404 = (2 : ZMod 912793213) ^ (152132202 + 152132202) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 152132202 * (2 : ZMod 912793213) ^ 152132202 := by rw [pow_add]
          _ = 14297202 := by rw [factor_1_27]; decide
      change (2 : ZMod 912793213) ^ 304264404 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (2 : ZMod 912793213) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 912793213) ^ 2 = 4 := by
        calc
          (2 : ZMod 912793213) ^ 2 = (2 : ZMod 912793213) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 1 * (2 : ZMod 912793213) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 912793213) ^ 5 = 32 := by
        calc
          (2 : ZMod 912793213) ^ 5 = (2 : ZMod 912793213) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 2 * (2 : ZMod 912793213) ^ 2) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 912793213) ^ 11 = 2048 := by
        calc
          (2 : ZMod 912793213) ^ 11 = (2 : ZMod 912793213) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 5 * (2 : ZMod 912793213) ^ 5) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 912793213) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 912793213) ^ 22 = (2 : ZMod 912793213) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 11 * (2 : ZMod 912793213) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 912793213) ^ 45 = 757693747 := by
        calc
          (2 : ZMod 912793213) ^ 45 = (2 : ZMod 912793213) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 22 * (2 : ZMod 912793213) ^ 22) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 757693747 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 912793213) ^ 91 = 564730499 := by
        calc
          (2 : ZMod 912793213) ^ 91 = (2 : ZMod 912793213) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 45 * (2 : ZMod 912793213) ^ 45) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 564730499 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 912793213) ^ 183 = 291609701 := by
        calc
          (2 : ZMod 912793213) ^ 183 = (2 : ZMod 912793213) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 91 * (2 : ZMod 912793213) ^ 91) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 291609701 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 912793213) ^ 366 = 365215681 := by
        calc
          (2 : ZMod 912793213) ^ 366 = (2 : ZMod 912793213) ^ (183 + 183) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 183 * (2 : ZMod 912793213) ^ 183 := by rw [pow_add]
          _ = 365215681 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 912793213) ^ 733 = 596438456 := by
        calc
          (2 : ZMod 912793213) ^ 733 = (2 : ZMod 912793213) ^ (366 + 366 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 366 * (2 : ZMod 912793213) ^ 366) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 596438456 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 912793213) ^ 1466 = 299731064 := by
        calc
          (2 : ZMod 912793213) ^ 1466 = (2 : ZMod 912793213) ^ (733 + 733) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 733 * (2 : ZMod 912793213) ^ 733 := by rw [pow_add]
          _ = 299731064 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 912793213) ^ 2932 = 751023281 := by
        calc
          (2 : ZMod 912793213) ^ 2932 = (2 : ZMod 912793213) ^ (1466 + 1466) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 1466 * (2 : ZMod 912793213) ^ 1466 := by rw [pow_add]
          _ = 751023281 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 912793213) ^ 5864 = 582158885 := by
        calc
          (2 : ZMod 912793213) ^ 5864 = (2 : ZMod 912793213) ^ (2932 + 2932) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 2932 * (2 : ZMod 912793213) ^ 2932 := by rw [pow_add]
          _ = 582158885 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 912793213) ^ 11728 = 817812872 := by
        calc
          (2 : ZMod 912793213) ^ 11728 = (2 : ZMod 912793213) ^ (5864 + 5864) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 5864 * (2 : ZMod 912793213) ^ 5864 := by rw [pow_add]
          _ = 817812872 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 912793213) ^ 23457 = 471522070 := by
        calc
          (2 : ZMod 912793213) ^ 23457 = (2 : ZMod 912793213) ^ (11728 + 11728 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 11728 * (2 : ZMod 912793213) ^ 11728) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 471522070 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 912793213) ^ 46915 = 243522909 := by
        calc
          (2 : ZMod 912793213) ^ 46915 = (2 : ZMod 912793213) ^ (23457 + 23457 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 23457 * (2 : ZMod 912793213) ^ 23457) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 243522909 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 912793213) ^ 93831 = 549402041 := by
        calc
          (2 : ZMod 912793213) ^ 93831 = (2 : ZMod 912793213) ^ (46915 + 46915 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 46915 * (2 : ZMod 912793213) ^ 46915) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 549402041 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 912793213) ^ 187663 = 255975693 := by
        calc
          (2 : ZMod 912793213) ^ 187663 = (2 : ZMod 912793213) ^ (93831 + 93831 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 93831 * (2 : ZMod 912793213) ^ 93831) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 255975693 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 912793213) ^ 375326 = 818713052 := by
        calc
          (2 : ZMod 912793213) ^ 375326 = (2 : ZMod 912793213) ^ (187663 + 187663) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 187663 * (2 : ZMod 912793213) ^ 187663 := by rw [pow_add]
          _ = 818713052 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 912793213) ^ 750652 = 222048099 := by
        calc
          (2 : ZMod 912793213) ^ 750652 = (2 : ZMod 912793213) ^ (375326 + 375326) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 375326 * (2 : ZMod 912793213) ^ 375326 := by rw [pow_add]
          _ = 222048099 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 912793213) ^ 1501304 = 401908545 := by
        calc
          (2 : ZMod 912793213) ^ 1501304 = (2 : ZMod 912793213) ^ (750652 + 750652) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 750652 * (2 : ZMod 912793213) ^ 750652 := by rw [pow_add]
          _ = 401908545 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 912793213) ^ 3002609 = 303210636 := by
        calc
          (2 : ZMod 912793213) ^ 3002609 = (2 : ZMod 912793213) ^ (1501304 + 1501304 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 1501304 * (2 : ZMod 912793213) ^ 1501304) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 303210636 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 912793213) ^ 6005218 = 369731860 := by
        calc
          (2 : ZMod 912793213) ^ 6005218 = (2 : ZMod 912793213) ^ (3002609 + 3002609) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 3002609 * (2 : ZMod 912793213) ^ 3002609 := by rw [pow_add]
          _ = 369731860 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 912793213) ^ 12010437 = 262183735 := by
        calc
          (2 : ZMod 912793213) ^ 12010437 = (2 : ZMod 912793213) ^ (6005218 + 6005218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 6005218 * (2 : ZMod 912793213) ^ 6005218) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 262183735 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 912793213) ^ 24020874 = 4363988 := by
        calc
          (2 : ZMod 912793213) ^ 24020874 = (2 : ZMod 912793213) ^ (12010437 + 12010437) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 12010437 * (2 : ZMod 912793213) ^ 12010437 := by rw [pow_add]
          _ = 4363988 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 912793213) ^ 48041748 = 786461325 := by
        calc
          (2 : ZMod 912793213) ^ 48041748 = (2 : ZMod 912793213) ^ (24020874 + 24020874) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 24020874 * (2 : ZMod 912793213) ^ 24020874 := by rw [pow_add]
          _ = 786461325 := by rw [factor_2_24]; decide
      change (2 : ZMod 912793213) ^ 48041748 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (2 : ZMod 912793213) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 912793213) ^ 3 = 8 := by
        calc
          (2 : ZMod 912793213) ^ 3 = (2 : ZMod 912793213) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 1 * (2 : ZMod 912793213) ^ 1) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 912793213) ^ 7 = 128 := by
        calc
          (2 : ZMod 912793213) ^ 7 = (2 : ZMod 912793213) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 3 * (2 : ZMod 912793213) ^ 3) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 912793213) ^ 15 = 32768 := by
        calc
          (2 : ZMod 912793213) ^ 15 = (2 : ZMod 912793213) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 7 * (2 : ZMod 912793213) ^ 7) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 912793213) ^ 30 = 160948611 := by
        calc
          (2 : ZMod 912793213) ^ 30 = (2 : ZMod 912793213) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 15 * (2 : ZMod 912793213) ^ 15 := by rw [pow_add]
          _ = 160948611 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 912793213) ^ 60 = 133308096 := by
        calc
          (2 : ZMod 912793213) ^ 60 = (2 : ZMod 912793213) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 30 * (2 : ZMod 912793213) ^ 30 := by rw [pow_add]
          _ = 133308096 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 912793213) ^ 120 = 622331971 := by
        calc
          (2 : ZMod 912793213) ^ 120 = (2 : ZMod 912793213) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 60 * (2 : ZMod 912793213) ^ 60 := by rw [pow_add]
          _ = 622331971 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 912793213) ^ 240 = 774422607 := by
        calc
          (2 : ZMod 912793213) ^ 240 = (2 : ZMod 912793213) ^ (120 + 120) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 120 * (2 : ZMod 912793213) ^ 120 := by rw [pow_add]
          _ = 774422607 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 912793213) ^ 480 = 36096277 := by
        calc
          (2 : ZMod 912793213) ^ 480 = (2 : ZMod 912793213) ^ (240 + 240) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 240 * (2 : ZMod 912793213) ^ 240 := by rw [pow_add]
          _ = 36096277 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 912793213) ^ 960 = 99573843 := by
        calc
          (2 : ZMod 912793213) ^ 960 = (2 : ZMod 912793213) ^ (480 + 480) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 480 * (2 : ZMod 912793213) ^ 480 := by rw [pow_add]
          _ = 99573843 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 912793213) ^ 1921 = 25595477 := by
        calc
          (2 : ZMod 912793213) ^ 1921 = (2 : ZMod 912793213) ^ (960 + 960 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 960 * (2 : ZMod 912793213) ^ 960) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 25595477 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 912793213) ^ 3842 = 323609595 := by
        calc
          (2 : ZMod 912793213) ^ 3842 = (2 : ZMod 912793213) ^ (1921 + 1921) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 1921 * (2 : ZMod 912793213) ^ 1921 := by rw [pow_add]
          _ = 323609595 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 912793213) ^ 7684 = 211110349 := by
        calc
          (2 : ZMod 912793213) ^ 7684 = (2 : ZMod 912793213) ^ (3842 + 3842) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 3842 * (2 : ZMod 912793213) ^ 3842 := by rw [pow_add]
          _ = 211110349 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 912793213) ^ 15368 = 823122792 := by
        calc
          (2 : ZMod 912793213) ^ 15368 = (2 : ZMod 912793213) ^ (7684 + 7684) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 7684 * (2 : ZMod 912793213) ^ 7684 := by rw [pow_add]
          _ = 823122792 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 912793213) ^ 30737 = 797830807 := by
        calc
          (2 : ZMod 912793213) ^ 30737 = (2 : ZMod 912793213) ^ (15368 + 15368 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 15368 * (2 : ZMod 912793213) ^ 15368) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 797830807 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 912793213) ^ 61475 = 823282661 := by
        calc
          (2 : ZMod 912793213) ^ 61475 = (2 : ZMod 912793213) ^ (30737 + 30737 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 30737 * (2 : ZMod 912793213) ^ 30737) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 823282661 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 912793213) ^ 122951 = 385106465 := by
        calc
          (2 : ZMod 912793213) ^ 122951 = (2 : ZMod 912793213) ^ (61475 + 61475 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 61475 * (2 : ZMod 912793213) ^ 61475) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 385106465 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 912793213) ^ 245903 = 444402876 := by
        calc
          (2 : ZMod 912793213) ^ 245903 = (2 : ZMod 912793213) ^ (122951 + 122951 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 122951 * (2 : ZMod 912793213) ^ 122951) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 444402876 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 912793213) ^ 491806 = 435085231 := by
        calc
          (2 : ZMod 912793213) ^ 491806 = (2 : ZMod 912793213) ^ (245903 + 245903) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 245903 * (2 : ZMod 912793213) ^ 245903 := by rw [pow_add]
          _ = 435085231 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 912793213) ^ 983613 = 172161491 := by
        calc
          (2 : ZMod 912793213) ^ 983613 = (2 : ZMod 912793213) ^ (491806 + 491806 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 491806 * (2 : ZMod 912793213) ^ 491806) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 172161491 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 912793213) ^ 1967226 = 377229033 := by
        calc
          (2 : ZMod 912793213) ^ 1967226 = (2 : ZMod 912793213) ^ (983613 + 983613) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 983613 * (2 : ZMod 912793213) ^ 983613 := by rw [pow_add]
          _ = 377229033 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 912793213) ^ 3934453 = 372000019 := by
        calc
          (2 : ZMod 912793213) ^ 3934453 = (2 : ZMod 912793213) ^ (1967226 + 1967226 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 1967226 * (2 : ZMod 912793213) ^ 1967226) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 372000019 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 912793213) ^ 7868907 = 896650361 := by
        calc
          (2 : ZMod 912793213) ^ 7868907 = (2 : ZMod 912793213) ^ (3934453 + 3934453 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 3934453 * (2 : ZMod 912793213) ^ 3934453) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 896650361 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 912793213) ^ 15737814 = 161900960 := by
        calc
          (2 : ZMod 912793213) ^ 15737814 = (2 : ZMod 912793213) ^ (7868907 + 7868907) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 7868907 * (2 : ZMod 912793213) ^ 7868907 := by rw [pow_add]
          _ = 161900960 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 912793213) ^ 31475628 = 333533455 := by
        calc
          (2 : ZMod 912793213) ^ 31475628 = (2 : ZMod 912793213) ^ (15737814 + 15737814) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 15737814 * (2 : ZMod 912793213) ^ 15737814 := by rw [pow_add]
          _ = 333533455 := by rw [factor_3_23]; decide
      change (2 : ZMod 912793213) ^ 31475628 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (2 : ZMod 912793213) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 912793213) ^ 2 = 4 := by
        calc
          (2 : ZMod 912793213) ^ 2 = (2 : ZMod 912793213) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 1 * (2 : ZMod 912793213) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 912793213) ^ 5 = 32 := by
        calc
          (2 : ZMod 912793213) ^ 5 = (2 : ZMod 912793213) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 2 * (2 : ZMod 912793213) ^ 2) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 912793213) ^ 10 = 1024 := by
        calc
          (2 : ZMod 912793213) ^ 10 = (2 : ZMod 912793213) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 5 * (2 : ZMod 912793213) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 912793213) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 912793213) ^ 21 = (2 : ZMod 912793213) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 10 * (2 : ZMod 912793213) ^ 10) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 912793213) ^ 43 = 417621740 := by
        calc
          (2 : ZMod 912793213) ^ 43 = (2 : ZMod 912793213) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 21 * (2 : ZMod 912793213) ^ 21) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 417621740 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 912793213) ^ 87 = 92345232 := by
        calc
          (2 : ZMod 912793213) ^ 87 = (2 : ZMod 912793213) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 43 * (2 : ZMod 912793213) ^ 43) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 92345232 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 912793213) ^ 174 = 897317570 := by
        calc
          (2 : ZMod 912793213) ^ 174 = (2 : ZMod 912793213) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 87 * (2 : ZMod 912793213) ^ 87 := by rw [pow_add]
          _ = 897317570 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 912793213) ^ 348 = 494209361 := by
        calc
          (2 : ZMod 912793213) ^ 348 = (2 : ZMod 912793213) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 174 * (2 : ZMod 912793213) ^ 174 := by rw [pow_add]
          _ = 494209361 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 912793213) ^ 697 = 643739404 := by
        calc
          (2 : ZMod 912793213) ^ 697 = (2 : ZMod 912793213) ^ (348 + 348 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 348 * (2 : ZMod 912793213) ^ 348) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 643739404 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 912793213) ^ 1394 = 58233658 := by
        calc
          (2 : ZMod 912793213) ^ 1394 = (2 : ZMod 912793213) ^ (697 + 697) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 697 * (2 : ZMod 912793213) ^ 697 := by rw [pow_add]
          _ = 58233658 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 912793213) ^ 2789 = 478293371 := by
        calc
          (2 : ZMod 912793213) ^ 2789 = (2 : ZMod 912793213) ^ (1394 + 1394 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 1394 * (2 : ZMod 912793213) ^ 1394) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 478293371 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 912793213) ^ 5578 = 612411582 := by
        calc
          (2 : ZMod 912793213) ^ 5578 = (2 : ZMod 912793213) ^ (2789 + 2789) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 2789 * (2 : ZMod 912793213) ^ 2789 := by rw [pow_add]
          _ = 612411582 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 912793213) ^ 11157 = 573525741 := by
        calc
          (2 : ZMod 912793213) ^ 11157 = (2 : ZMod 912793213) ^ (5578 + 5578 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 5578 * (2 : ZMod 912793213) ^ 5578) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 573525741 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 912793213) ^ 22315 = 614342152 := by
        calc
          (2 : ZMod 912793213) ^ 22315 = (2 : ZMod 912793213) ^ (11157 + 11157 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 11157 * (2 : ZMod 912793213) ^ 11157) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 614342152 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 912793213) ^ 44631 = 119536475 := by
        calc
          (2 : ZMod 912793213) ^ 44631 = (2 : ZMod 912793213) ^ (22315 + 22315 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = ((2 : ZMod 912793213) ^ 22315 * (2 : ZMod 912793213) ^ 22315) * (2 : ZMod 912793213) := by rw [pow_succ, pow_add]
          _ = 119536475 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 912793213) ^ 89262 = 753490556 := by
        calc
          (2 : ZMod 912793213) ^ 89262 = (2 : ZMod 912793213) ^ (44631 + 44631) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 44631 * (2 : ZMod 912793213) ^ 44631 := by rw [pow_add]
          _ = 753490556 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 912793213) ^ 178524 = 189588451 := by
        calc
          (2 : ZMod 912793213) ^ 178524 = (2 : ZMod 912793213) ^ (89262 + 89262) :=
            congrArg (fun n : ℕ => (2 : ZMod 912793213) ^ n) (by norm_num)
          _ = (2 : ZMod 912793213) ^ 89262 * (2 : ZMod 912793213) ^ 89262 := by rw [pow_add]
          _ = 189588451 := by rw [factor_4_16]; decide
      change (2 : ZMod 912793213) ^ 178524 ≠ 1
      rw [factor_4_17]
      decide

#print axioms prime_lucas_912793213

end TotientTailPeriodKiller
end Erdos249257
