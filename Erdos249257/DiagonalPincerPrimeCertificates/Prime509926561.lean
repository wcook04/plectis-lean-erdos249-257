import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=23 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_509926561 : Nat.Prime 509926561 := by
  apply lucas_primality 509926561 (61 : ZMod 509926561)
  ·
      have fermat_0 : (61 : ZMod 509926561) ^ 1 = 61 := by norm_num
      have fermat_1 : (61 : ZMod 509926561) ^ 3 = 226981 := by
        calc
          (61 : ZMod 509926561) ^ 3 = (61 : ZMod 509926561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1 * (61 : ZMod 509926561) ^ 1) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 226981 := by rw [fermat_0]; decide
      have fermat_2 : (61 : ZMod 509926561) ^ 7 = 65440578 := by
        calc
          (61 : ZMod 509926561) ^ 7 = (61 : ZMod 509926561) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 3 * (61 : ZMod 509926561) ^ 3) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 65440578 := by rw [fermat_1]; decide
      have fermat_3 : (61 : ZMod 509926561) ^ 15 = 12594205 := by
        calc
          (61 : ZMod 509926561) ^ 15 = (61 : ZMod 509926561) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 7 * (61 : ZMod 509926561) ^ 7) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 12594205 := by rw [fermat_2]; decide
      have fermat_4 : (61 : ZMod 509926561) ^ 30 = 322929853 := by
        calc
          (61 : ZMod 509926561) ^ 30 = (61 : ZMod 509926561) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 15 * (61 : ZMod 509926561) ^ 15 := by rw [pow_add]
          _ = 322929853 := by rw [fermat_3]; decide
      have fermat_5 : (61 : ZMod 509926561) ^ 60 = 48150017 := by
        calc
          (61 : ZMod 509926561) ^ 60 = (61 : ZMod 509926561) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 30 * (61 : ZMod 509926561) ^ 30 := by rw [pow_add]
          _ = 48150017 := by rw [fermat_4]; decide
      have fermat_6 : (61 : ZMod 509926561) ^ 121 = 86331662 := by
        calc
          (61 : ZMod 509926561) ^ 121 = (61 : ZMod 509926561) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 60 * (61 : ZMod 509926561) ^ 60) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 86331662 := by rw [fermat_5]; decide
      have fermat_7 : (61 : ZMod 509926561) ^ 243 = 412776121 := by
        calc
          (61 : ZMod 509926561) ^ 243 = (61 : ZMod 509926561) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 121 * (61 : ZMod 509926561) ^ 121) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 412776121 := by rw [fermat_6]; decide
      have fermat_8 : (61 : ZMod 509926561) ^ 486 = 221339845 := by
        calc
          (61 : ZMod 509926561) ^ 486 = (61 : ZMod 509926561) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 243 * (61 : ZMod 509926561) ^ 243 := by rw [pow_add]
          _ = 221339845 := by rw [fermat_7]; decide
      have fermat_9 : (61 : ZMod 509926561) ^ 972 = 55643165 := by
        calc
          (61 : ZMod 509926561) ^ 972 = (61 : ZMod 509926561) ^ (486 + 486) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 486 * (61 : ZMod 509926561) ^ 486 := by rw [pow_add]
          _ = 55643165 := by rw [fermat_8]; decide
      have fermat_10 : (61 : ZMod 509926561) ^ 1945 = 16052955 := by
        calc
          (61 : ZMod 509926561) ^ 1945 = (61 : ZMod 509926561) ^ (972 + 972 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 972 * (61 : ZMod 509926561) ^ 972) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 16052955 := by rw [fermat_9]; decide
      have fermat_11 : (61 : ZMod 509926561) ^ 3890 = 367438504 := by
        calc
          (61 : ZMod 509926561) ^ 3890 = (61 : ZMod 509926561) ^ (1945 + 1945) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1945 * (61 : ZMod 509926561) ^ 1945 := by rw [pow_add]
          _ = 367438504 := by rw [fermat_10]; decide
      have fermat_12 : (61 : ZMod 509926561) ^ 7780 = 18751853 := by
        calc
          (61 : ZMod 509926561) ^ 7780 = (61 : ZMod 509926561) ^ (3890 + 3890) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3890 * (61 : ZMod 509926561) ^ 3890 := by rw [pow_add]
          _ = 18751853 := by rw [fermat_11]; decide
      have fermat_13 : (61 : ZMod 509926561) ^ 15561 = 75119588 := by
        calc
          (61 : ZMod 509926561) ^ 15561 = (61 : ZMod 509926561) ^ (7780 + 7780 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 7780 * (61 : ZMod 509926561) ^ 7780) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 75119588 := by rw [fermat_12]; decide
      have fermat_14 : (61 : ZMod 509926561) ^ 31123 = 427024443 := by
        calc
          (61 : ZMod 509926561) ^ 31123 = (61 : ZMod 509926561) ^ (15561 + 15561 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 15561 * (61 : ZMod 509926561) ^ 15561) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 427024443 := by rw [fermat_13]; decide
      have fermat_15 : (61 : ZMod 509926561) ^ 62246 = 45541901 := by
        calc
          (61 : ZMod 509926561) ^ 62246 = (61 : ZMod 509926561) ^ (31123 + 31123) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 31123 * (61 : ZMod 509926561) ^ 31123 := by rw [pow_add]
          _ = 45541901 := by rw [fermat_14]; decide
      have fermat_16 : (61 : ZMod 509926561) ^ 124493 = 128746443 := by
        calc
          (61 : ZMod 509926561) ^ 124493 = (61 : ZMod 509926561) ^ (62246 + 62246 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 62246 * (61 : ZMod 509926561) ^ 62246) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 128746443 := by rw [fermat_15]; decide
      have fermat_17 : (61 : ZMod 509926561) ^ 248987 = 10229924 := by
        calc
          (61 : ZMod 509926561) ^ 248987 = (61 : ZMod 509926561) ^ (124493 + 124493 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 124493 * (61 : ZMod 509926561) ^ 124493) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 10229924 := by rw [fermat_16]; decide
      have fermat_18 : (61 : ZMod 509926561) ^ 497975 = 185051972 := by
        calc
          (61 : ZMod 509926561) ^ 497975 = (61 : ZMod 509926561) ^ (248987 + 248987 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 248987 * (61 : ZMod 509926561) ^ 248987) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 185051972 := by rw [fermat_17]; decide
      have fermat_19 : (61 : ZMod 509926561) ^ 995950 = 423510681 := by
        calc
          (61 : ZMod 509926561) ^ 995950 = (61 : ZMod 509926561) ^ (497975 + 497975) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 497975 * (61 : ZMod 509926561) ^ 497975 := by rw [pow_add]
          _ = 423510681 := by rw [fermat_18]; decide
      have fermat_20 : (61 : ZMod 509926561) ^ 1991900 = 145800774 := by
        calc
          (61 : ZMod 509926561) ^ 1991900 = (61 : ZMod 509926561) ^ (995950 + 995950) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 995950 * (61 : ZMod 509926561) ^ 995950 := by rw [pow_add]
          _ = 145800774 := by rw [fermat_19]; decide
      have fermat_21 : (61 : ZMod 509926561) ^ 3983801 = 90752547 := by
        calc
          (61 : ZMod 509926561) ^ 3983801 = (61 : ZMod 509926561) ^ (1991900 + 1991900 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1991900 * (61 : ZMod 509926561) ^ 1991900) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 90752547 := by rw [fermat_20]; decide
      have fermat_22 : (61 : ZMod 509926561) ^ 7967602 = 499137736 := by
        calc
          (61 : ZMod 509926561) ^ 7967602 = (61 : ZMod 509926561) ^ (3983801 + 3983801) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3983801 * (61 : ZMod 509926561) ^ 3983801 := by rw [pow_add]
          _ = 499137736 := by rw [fermat_21]; decide
      have fermat_23 : (61 : ZMod 509926561) ^ 15935205 = 447555998 := by
        calc
          (61 : ZMod 509926561) ^ 15935205 = (61 : ZMod 509926561) ^ (7967602 + 7967602 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 7967602 * (61 : ZMod 509926561) ^ 7967602) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 447555998 := by rw [fermat_22]; decide
      have fermat_24 : (61 : ZMod 509926561) ^ 31870410 = 174505049 := by
        calc
          (61 : ZMod 509926561) ^ 31870410 = (61 : ZMod 509926561) ^ (15935205 + 15935205) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 15935205 * (61 : ZMod 509926561) ^ 15935205 := by rw [pow_add]
          _ = 174505049 := by rw [fermat_23]; decide
      have fermat_25 : (61 : ZMod 509926561) ^ 63740820 = 18052854 := by
        calc
          (61 : ZMod 509926561) ^ 63740820 = (61 : ZMod 509926561) ^ (31870410 + 31870410) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 31870410 * (61 : ZMod 509926561) ^ 31870410 := by rw [pow_add]
          _ = 18052854 := by rw [fermat_24]; decide
      have fermat_26 : (61 : ZMod 509926561) ^ 127481640 = 254025874 := by
        calc
          (61 : ZMod 509926561) ^ 127481640 = (61 : ZMod 509926561) ^ (63740820 + 63740820) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 63740820 * (61 : ZMod 509926561) ^ 63740820 := by rw [pow_add]
          _ = 254025874 := by rw [fermat_25]; decide
      have fermat_27 : (61 : ZMod 509926561) ^ 254963280 = 509926560 := by
        calc
          (61 : ZMod 509926561) ^ 254963280 = (61 : ZMod 509926561) ^ (127481640 + 127481640) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 127481640 * (61 : ZMod 509926561) ^ 127481640 := by rw [pow_add]
          _ = 509926560 := by rw [fermat_26]; decide
      have fermat_28 : (61 : ZMod 509926561) ^ 509926560 = 1 := by
        calc
          (61 : ZMod 509926561) ^ 509926560 = (61 : ZMod 509926561) ^ (254963280 + 254963280) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 254963280 * (61 : ZMod 509926561) ^ 254963280 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 509926561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (61 : ZMod 509926561) ^ 1 = 61 := by norm_num
      have factor_0_1 : (61 : ZMod 509926561) ^ 3 = 226981 := by
        calc
          (61 : ZMod 509926561) ^ 3 = (61 : ZMod 509926561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1 * (61 : ZMod 509926561) ^ 1) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 226981 := by rw [factor_0_0]; decide
      have factor_0_2 : (61 : ZMod 509926561) ^ 7 = 65440578 := by
        calc
          (61 : ZMod 509926561) ^ 7 = (61 : ZMod 509926561) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 3 * (61 : ZMod 509926561) ^ 3) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 65440578 := by rw [factor_0_1]; decide
      have factor_0_3 : (61 : ZMod 509926561) ^ 15 = 12594205 := by
        calc
          (61 : ZMod 509926561) ^ 15 = (61 : ZMod 509926561) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 7 * (61 : ZMod 509926561) ^ 7) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 12594205 := by rw [factor_0_2]; decide
      have factor_0_4 : (61 : ZMod 509926561) ^ 30 = 322929853 := by
        calc
          (61 : ZMod 509926561) ^ 30 = (61 : ZMod 509926561) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 15 * (61 : ZMod 509926561) ^ 15 := by rw [pow_add]
          _ = 322929853 := by rw [factor_0_3]; decide
      have factor_0_5 : (61 : ZMod 509926561) ^ 60 = 48150017 := by
        calc
          (61 : ZMod 509926561) ^ 60 = (61 : ZMod 509926561) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 30 * (61 : ZMod 509926561) ^ 30 := by rw [pow_add]
          _ = 48150017 := by rw [factor_0_4]; decide
      have factor_0_6 : (61 : ZMod 509926561) ^ 121 = 86331662 := by
        calc
          (61 : ZMod 509926561) ^ 121 = (61 : ZMod 509926561) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 60 * (61 : ZMod 509926561) ^ 60) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 86331662 := by rw [factor_0_5]; decide
      have factor_0_7 : (61 : ZMod 509926561) ^ 243 = 412776121 := by
        calc
          (61 : ZMod 509926561) ^ 243 = (61 : ZMod 509926561) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 121 * (61 : ZMod 509926561) ^ 121) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 412776121 := by rw [factor_0_6]; decide
      have factor_0_8 : (61 : ZMod 509926561) ^ 486 = 221339845 := by
        calc
          (61 : ZMod 509926561) ^ 486 = (61 : ZMod 509926561) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 243 * (61 : ZMod 509926561) ^ 243 := by rw [pow_add]
          _ = 221339845 := by rw [factor_0_7]; decide
      have factor_0_9 : (61 : ZMod 509926561) ^ 972 = 55643165 := by
        calc
          (61 : ZMod 509926561) ^ 972 = (61 : ZMod 509926561) ^ (486 + 486) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 486 * (61 : ZMod 509926561) ^ 486 := by rw [pow_add]
          _ = 55643165 := by rw [factor_0_8]; decide
      have factor_0_10 : (61 : ZMod 509926561) ^ 1945 = 16052955 := by
        calc
          (61 : ZMod 509926561) ^ 1945 = (61 : ZMod 509926561) ^ (972 + 972 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 972 * (61 : ZMod 509926561) ^ 972) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 16052955 := by rw [factor_0_9]; decide
      have factor_0_11 : (61 : ZMod 509926561) ^ 3890 = 367438504 := by
        calc
          (61 : ZMod 509926561) ^ 3890 = (61 : ZMod 509926561) ^ (1945 + 1945) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1945 * (61 : ZMod 509926561) ^ 1945 := by rw [pow_add]
          _ = 367438504 := by rw [factor_0_10]; decide
      have factor_0_12 : (61 : ZMod 509926561) ^ 7780 = 18751853 := by
        calc
          (61 : ZMod 509926561) ^ 7780 = (61 : ZMod 509926561) ^ (3890 + 3890) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3890 * (61 : ZMod 509926561) ^ 3890 := by rw [pow_add]
          _ = 18751853 := by rw [factor_0_11]; decide
      have factor_0_13 : (61 : ZMod 509926561) ^ 15561 = 75119588 := by
        calc
          (61 : ZMod 509926561) ^ 15561 = (61 : ZMod 509926561) ^ (7780 + 7780 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 7780 * (61 : ZMod 509926561) ^ 7780) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 75119588 := by rw [factor_0_12]; decide
      have factor_0_14 : (61 : ZMod 509926561) ^ 31123 = 427024443 := by
        calc
          (61 : ZMod 509926561) ^ 31123 = (61 : ZMod 509926561) ^ (15561 + 15561 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 15561 * (61 : ZMod 509926561) ^ 15561) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 427024443 := by rw [factor_0_13]; decide
      have factor_0_15 : (61 : ZMod 509926561) ^ 62246 = 45541901 := by
        calc
          (61 : ZMod 509926561) ^ 62246 = (61 : ZMod 509926561) ^ (31123 + 31123) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 31123 * (61 : ZMod 509926561) ^ 31123 := by rw [pow_add]
          _ = 45541901 := by rw [factor_0_14]; decide
      have factor_0_16 : (61 : ZMod 509926561) ^ 124493 = 128746443 := by
        calc
          (61 : ZMod 509926561) ^ 124493 = (61 : ZMod 509926561) ^ (62246 + 62246 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 62246 * (61 : ZMod 509926561) ^ 62246) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 128746443 := by rw [factor_0_15]; decide
      have factor_0_17 : (61 : ZMod 509926561) ^ 248987 = 10229924 := by
        calc
          (61 : ZMod 509926561) ^ 248987 = (61 : ZMod 509926561) ^ (124493 + 124493 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 124493 * (61 : ZMod 509926561) ^ 124493) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 10229924 := by rw [factor_0_16]; decide
      have factor_0_18 : (61 : ZMod 509926561) ^ 497975 = 185051972 := by
        calc
          (61 : ZMod 509926561) ^ 497975 = (61 : ZMod 509926561) ^ (248987 + 248987 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 248987 * (61 : ZMod 509926561) ^ 248987) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 185051972 := by rw [factor_0_17]; decide
      have factor_0_19 : (61 : ZMod 509926561) ^ 995950 = 423510681 := by
        calc
          (61 : ZMod 509926561) ^ 995950 = (61 : ZMod 509926561) ^ (497975 + 497975) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 497975 * (61 : ZMod 509926561) ^ 497975 := by rw [pow_add]
          _ = 423510681 := by rw [factor_0_18]; decide
      have factor_0_20 : (61 : ZMod 509926561) ^ 1991900 = 145800774 := by
        calc
          (61 : ZMod 509926561) ^ 1991900 = (61 : ZMod 509926561) ^ (995950 + 995950) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 995950 * (61 : ZMod 509926561) ^ 995950 := by rw [pow_add]
          _ = 145800774 := by rw [factor_0_19]; decide
      have factor_0_21 : (61 : ZMod 509926561) ^ 3983801 = 90752547 := by
        calc
          (61 : ZMod 509926561) ^ 3983801 = (61 : ZMod 509926561) ^ (1991900 + 1991900 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1991900 * (61 : ZMod 509926561) ^ 1991900) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 90752547 := by rw [factor_0_20]; decide
      have factor_0_22 : (61 : ZMod 509926561) ^ 7967602 = 499137736 := by
        calc
          (61 : ZMod 509926561) ^ 7967602 = (61 : ZMod 509926561) ^ (3983801 + 3983801) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3983801 * (61 : ZMod 509926561) ^ 3983801 := by rw [pow_add]
          _ = 499137736 := by rw [factor_0_21]; decide
      have factor_0_23 : (61 : ZMod 509926561) ^ 15935205 = 447555998 := by
        calc
          (61 : ZMod 509926561) ^ 15935205 = (61 : ZMod 509926561) ^ (7967602 + 7967602 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 7967602 * (61 : ZMod 509926561) ^ 7967602) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 447555998 := by rw [factor_0_22]; decide
      have factor_0_24 : (61 : ZMod 509926561) ^ 31870410 = 174505049 := by
        calc
          (61 : ZMod 509926561) ^ 31870410 = (61 : ZMod 509926561) ^ (15935205 + 15935205) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 15935205 * (61 : ZMod 509926561) ^ 15935205 := by rw [pow_add]
          _ = 174505049 := by rw [factor_0_23]; decide
      have factor_0_25 : (61 : ZMod 509926561) ^ 63740820 = 18052854 := by
        calc
          (61 : ZMod 509926561) ^ 63740820 = (61 : ZMod 509926561) ^ (31870410 + 31870410) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 31870410 * (61 : ZMod 509926561) ^ 31870410 := by rw [pow_add]
          _ = 18052854 := by rw [factor_0_24]; decide
      have factor_0_26 : (61 : ZMod 509926561) ^ 127481640 = 254025874 := by
        calc
          (61 : ZMod 509926561) ^ 127481640 = (61 : ZMod 509926561) ^ (63740820 + 63740820) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 63740820 * (61 : ZMod 509926561) ^ 63740820 := by rw [pow_add]
          _ = 254025874 := by rw [factor_0_25]; decide
      have factor_0_27 : (61 : ZMod 509926561) ^ 254963280 = 509926560 := by
        calc
          (61 : ZMod 509926561) ^ 254963280 = (61 : ZMod 509926561) ^ (127481640 + 127481640) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 127481640 * (61 : ZMod 509926561) ^ 127481640 := by rw [pow_add]
          _ = 509926560 := by rw [factor_0_26]; decide
      change (61 : ZMod 509926561) ^ 254963280 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (61 : ZMod 509926561) ^ 1 = 61 := by norm_num
      have factor_1_1 : (61 : ZMod 509926561) ^ 2 = 3721 := by
        calc
          (61 : ZMod 509926561) ^ 2 = (61 : ZMod 509926561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1 * (61 : ZMod 509926561) ^ 1 := by rw [pow_add]
          _ = 3721 := by rw [factor_1_0]; decide
      have factor_1_2 : (61 : ZMod 509926561) ^ 5 = 334669740 := by
        calc
          (61 : ZMod 509926561) ^ 5 = (61 : ZMod 509926561) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 2 * (61 : ZMod 509926561) ^ 2) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 334669740 := by rw [factor_1_1]; decide
      have factor_1_3 : (61 : ZMod 509926561) ^ 10 = 117039649 := by
        calc
          (61 : ZMod 509926561) ^ 10 = (61 : ZMod 509926561) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 5 * (61 : ZMod 509926561) ^ 5 := by rw [pow_add]
          _ = 117039649 := by rw [factor_1_2]; decide
      have factor_1_4 : (61 : ZMod 509926561) ^ 20 = 357452122 := by
        calc
          (61 : ZMod 509926561) ^ 20 = (61 : ZMod 509926561) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 10 * (61 : ZMod 509926561) ^ 10 := by rw [pow_add]
          _ = 357452122 := by rw [factor_1_3]; decide
      have factor_1_5 : (61 : ZMod 509926561) ^ 40 = 62361751 := by
        calc
          (61 : ZMod 509926561) ^ 40 = (61 : ZMod 509926561) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 20 * (61 : ZMod 509926561) ^ 20 := by rw [pow_add]
          _ = 62361751 := by rw [factor_1_4]; decide
      have factor_1_6 : (61 : ZMod 509926561) ^ 81 = 20014245 := by
        calc
          (61 : ZMod 509926561) ^ 81 = (61 : ZMod 509926561) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 40 * (61 : ZMod 509926561) ^ 40) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 20014245 := by rw [factor_1_5]; decide
      have factor_1_7 : (61 : ZMod 509926561) ^ 162 = 252485841 := by
        calc
          (61 : ZMod 509926561) ^ 162 = (61 : ZMod 509926561) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 81 * (61 : ZMod 509926561) ^ 81 := by rw [pow_add]
          _ = 252485841 := by rw [factor_1_6]; decide
      have factor_1_8 : (61 : ZMod 509926561) ^ 324 = 102906324 := by
        calc
          (61 : ZMod 509926561) ^ 324 = (61 : ZMod 509926561) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 162 * (61 : ZMod 509926561) ^ 162 := by rw [pow_add]
          _ = 102906324 := by rw [factor_1_7]; decide
      have factor_1_9 : (61 : ZMod 509926561) ^ 648 = 336453046 := by
        calc
          (61 : ZMod 509926561) ^ 648 = (61 : ZMod 509926561) ^ (324 + 324) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 324 * (61 : ZMod 509926561) ^ 324 := by rw [pow_add]
          _ = 336453046 := by rw [factor_1_8]; decide
      have factor_1_10 : (61 : ZMod 509926561) ^ 1296 = 392173847 := by
        calc
          (61 : ZMod 509926561) ^ 1296 = (61 : ZMod 509926561) ^ (648 + 648) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 648 * (61 : ZMod 509926561) ^ 648 := by rw [pow_add]
          _ = 392173847 := by rw [factor_1_9]; decide
      have factor_1_11 : (61 : ZMod 509926561) ^ 2593 = 471849641 := by
        calc
          (61 : ZMod 509926561) ^ 2593 = (61 : ZMod 509926561) ^ (1296 + 1296 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1296 * (61 : ZMod 509926561) ^ 1296) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 471849641 := by rw [factor_1_10]; decide
      have factor_1_12 : (61 : ZMod 509926561) ^ 5187 = 447051775 := by
        calc
          (61 : ZMod 509926561) ^ 5187 = (61 : ZMod 509926561) ^ (2593 + 2593 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 2593 * (61 : ZMod 509926561) ^ 2593) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 447051775 := by rw [factor_1_11]; decide
      have factor_1_13 : (61 : ZMod 509926561) ^ 10374 = 415093392 := by
        calc
          (61 : ZMod 509926561) ^ 10374 = (61 : ZMod 509926561) ^ (5187 + 5187) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 5187 * (61 : ZMod 509926561) ^ 5187 := by rw [pow_add]
          _ = 415093392 := by rw [factor_1_12]; decide
      have factor_1_14 : (61 : ZMod 509926561) ^ 20748 = 460901402 := by
        calc
          (61 : ZMod 509926561) ^ 20748 = (61 : ZMod 509926561) ^ (10374 + 10374) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 10374 * (61 : ZMod 509926561) ^ 10374 := by rw [pow_add]
          _ = 460901402 := by rw [factor_1_13]; decide
      have factor_1_15 : (61 : ZMod 509926561) ^ 41497 = 303697170 := by
        calc
          (61 : ZMod 509926561) ^ 41497 = (61 : ZMod 509926561) ^ (20748 + 20748 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 20748 * (61 : ZMod 509926561) ^ 20748) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 303697170 := by rw [factor_1_14]; decide
      have factor_1_16 : (61 : ZMod 509926561) ^ 82995 = 366142366 := by
        calc
          (61 : ZMod 509926561) ^ 82995 = (61 : ZMod 509926561) ^ (41497 + 41497 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 41497 * (61 : ZMod 509926561) ^ 41497) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 366142366 := by rw [factor_1_15]; decide
      have factor_1_17 : (61 : ZMod 509926561) ^ 165991 = 501552084 := by
        calc
          (61 : ZMod 509926561) ^ 165991 = (61 : ZMod 509926561) ^ (82995 + 82995 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 82995 * (61 : ZMod 509926561) ^ 82995) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 501552084 := by rw [factor_1_16]; decide
      have factor_1_18 : (61 : ZMod 509926561) ^ 331983 = 95055500 := by
        calc
          (61 : ZMod 509926561) ^ 331983 = (61 : ZMod 509926561) ^ (165991 + 165991 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 165991 * (61 : ZMod 509926561) ^ 165991) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 95055500 := by rw [factor_1_17]; decide
      have factor_1_19 : (61 : ZMod 509926561) ^ 663966 = 248803968 := by
        calc
          (61 : ZMod 509926561) ^ 663966 = (61 : ZMod 509926561) ^ (331983 + 331983) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 331983 * (61 : ZMod 509926561) ^ 331983 := by rw [pow_add]
          _ = 248803968 := by rw [factor_1_18]; decide
      have factor_1_20 : (61 : ZMod 509926561) ^ 1327933 = 304496800 := by
        calc
          (61 : ZMod 509926561) ^ 1327933 = (61 : ZMod 509926561) ^ (663966 + 663966 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 663966 * (61 : ZMod 509926561) ^ 663966) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 304496800 := by rw [factor_1_19]; decide
      have factor_1_21 : (61 : ZMod 509926561) ^ 2655867 = 375285069 := by
        calc
          (61 : ZMod 509926561) ^ 2655867 = (61 : ZMod 509926561) ^ (1327933 + 1327933 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1327933 * (61 : ZMod 509926561) ^ 1327933) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 375285069 := by rw [factor_1_20]; decide
      have factor_1_22 : (61 : ZMod 509926561) ^ 5311735 = 84715175 := by
        calc
          (61 : ZMod 509926561) ^ 5311735 = (61 : ZMod 509926561) ^ (2655867 + 2655867 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 2655867 * (61 : ZMod 509926561) ^ 2655867) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 84715175 := by rw [factor_1_21]; decide
      have factor_1_23 : (61 : ZMod 509926561) ^ 10623470 = 349157115 := by
        calc
          (61 : ZMod 509926561) ^ 10623470 = (61 : ZMod 509926561) ^ (5311735 + 5311735) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 5311735 * (61 : ZMod 509926561) ^ 5311735 := by rw [pow_add]
          _ = 349157115 := by rw [factor_1_22]; decide
      have factor_1_24 : (61 : ZMod 509926561) ^ 21246940 = 423754469 := by
        calc
          (61 : ZMod 509926561) ^ 21246940 = (61 : ZMod 509926561) ^ (10623470 + 10623470) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 10623470 * (61 : ZMod 509926561) ^ 10623470 := by rw [pow_add]
          _ = 423754469 := by rw [factor_1_23]; decide
      have factor_1_25 : (61 : ZMod 509926561) ^ 42493880 = 329684070 := by
        calc
          (61 : ZMod 509926561) ^ 42493880 = (61 : ZMod 509926561) ^ (21246940 + 21246940) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 21246940 * (61 : ZMod 509926561) ^ 21246940 := by rw [pow_add]
          _ = 329684070 := by rw [factor_1_24]; decide
      have factor_1_26 : (61 : ZMod 509926561) ^ 84987760 = 141101450 := by
        calc
          (61 : ZMod 509926561) ^ 84987760 = (61 : ZMod 509926561) ^ (42493880 + 42493880) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 42493880 * (61 : ZMod 509926561) ^ 42493880 := by rw [pow_add]
          _ = 141101450 := by rw [factor_1_25]; decide
      have factor_1_27 : (61 : ZMod 509926561) ^ 169975520 = 141101449 := by
        calc
          (61 : ZMod 509926561) ^ 169975520 = (61 : ZMod 509926561) ^ (84987760 + 84987760) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 84987760 * (61 : ZMod 509926561) ^ 84987760 := by rw [pow_add]
          _ = 141101449 := by rw [factor_1_26]; decide
      change (61 : ZMod 509926561) ^ 169975520 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (61 : ZMod 509926561) ^ 1 = 61 := by norm_num
      have factor_2_1 : (61 : ZMod 509926561) ^ 3 = 226981 := by
        calc
          (61 : ZMod 509926561) ^ 3 = (61 : ZMod 509926561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1 * (61 : ZMod 509926561) ^ 1) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 226981 := by rw [factor_2_0]; decide
      have factor_2_2 : (61 : ZMod 509926561) ^ 6 = 17791700 := by
        calc
          (61 : ZMod 509926561) ^ 6 = (61 : ZMod 509926561) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3 * (61 : ZMod 509926561) ^ 3 := by rw [pow_add]
          _ = 17791700 := by rw [factor_2_1]; decide
      have factor_2_3 : (61 : ZMod 509926561) ^ 12 = 27250835 := by
        calc
          (61 : ZMod 509926561) ^ 12 = (61 : ZMod 509926561) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 6 * (61 : ZMod 509926561) ^ 6 := by rw [pow_add]
          _ = 27250835 := by rw [factor_2_2]; decide
      have factor_2_4 : (61 : ZMod 509926561) ^ 24 = 427633242 := by
        calc
          (61 : ZMod 509926561) ^ 24 = (61 : ZMod 509926561) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 12 * (61 : ZMod 509926561) ^ 12 := by rw [pow_add]
          _ = 427633242 := by rw [factor_2_3]; decide
      have factor_2_5 : (61 : ZMod 509926561) ^ 48 = 4611524 := by
        calc
          (61 : ZMod 509926561) ^ 48 = (61 : ZMod 509926561) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 24 * (61 : ZMod 509926561) ^ 24 := by rw [pow_add]
          _ = 4611524 := by rw [factor_2_4]; decide
      have factor_2_6 : (61 : ZMod 509926561) ^ 97 = 46002771 := by
        calc
          (61 : ZMod 509926561) ^ 97 = (61 : ZMod 509926561) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 48 * (61 : ZMod 509926561) ^ 48) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 46002771 := by rw [factor_2_5]; decide
      have factor_2_7 : (61 : ZMod 509926561) ^ 194 = 50120804 := by
        calc
          (61 : ZMod 509926561) ^ 194 = (61 : ZMod 509926561) ^ (97 + 97) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 97 * (61 : ZMod 509926561) ^ 97 := by rw [pow_add]
          _ = 50120804 := by rw [factor_2_6]; decide
      have factor_2_8 : (61 : ZMod 509926561) ^ 389 = 369805680 := by
        calc
          (61 : ZMod 509926561) ^ 389 = (61 : ZMod 509926561) ^ (194 + 194 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 194 * (61 : ZMod 509926561) ^ 194) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 369805680 := by rw [factor_2_7]; decide
      have factor_2_9 : (61 : ZMod 509926561) ^ 778 = 326872690 := by
        calc
          (61 : ZMod 509926561) ^ 778 = (61 : ZMod 509926561) ^ (389 + 389) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 389 * (61 : ZMod 509926561) ^ 389 := by rw [pow_add]
          _ = 326872690 := by rw [factor_2_8]; decide
      have factor_2_10 : (61 : ZMod 509926561) ^ 1556 = 232900767 := by
        calc
          (61 : ZMod 509926561) ^ 1556 = (61 : ZMod 509926561) ^ (778 + 778) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 778 * (61 : ZMod 509926561) ^ 778 := by rw [pow_add]
          _ = 232900767 := by rw [factor_2_9]; decide
      have factor_2_11 : (61 : ZMod 509926561) ^ 3112 = 406167565 := by
        calc
          (61 : ZMod 509926561) ^ 3112 = (61 : ZMod 509926561) ^ (1556 + 1556) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1556 * (61 : ZMod 509926561) ^ 1556 := by rw [pow_add]
          _ = 406167565 := by rw [factor_2_10]; decide
      have factor_2_12 : (61 : ZMod 509926561) ^ 6224 = 196870511 := by
        calc
          (61 : ZMod 509926561) ^ 6224 = (61 : ZMod 509926561) ^ (3112 + 3112) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3112 * (61 : ZMod 509926561) ^ 3112 := by rw [pow_add]
          _ = 196870511 := by rw [factor_2_11]; decide
      have factor_2_13 : (61 : ZMod 509926561) ^ 12449 = 405534108 := by
        calc
          (61 : ZMod 509926561) ^ 12449 = (61 : ZMod 509926561) ^ (6224 + 6224 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 6224 * (61 : ZMod 509926561) ^ 6224) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 405534108 := by rw [factor_2_12]; decide
      have factor_2_14 : (61 : ZMod 509926561) ^ 24898 = 418862568 := by
        calc
          (61 : ZMod 509926561) ^ 24898 = (61 : ZMod 509926561) ^ (12449 + 12449) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 12449 * (61 : ZMod 509926561) ^ 12449 := by rw [pow_add]
          _ = 418862568 := by rw [factor_2_13]; decide
      have factor_2_15 : (61 : ZMod 509926561) ^ 49797 = 480790064 := by
        calc
          (61 : ZMod 509926561) ^ 49797 = (61 : ZMod 509926561) ^ (24898 + 24898 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 24898 * (61 : ZMod 509926561) ^ 24898) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 480790064 := by rw [factor_2_14]; decide
      have factor_2_16 : (61 : ZMod 509926561) ^ 99595 = 304706867 := by
        calc
          (61 : ZMod 509926561) ^ 99595 = (61 : ZMod 509926561) ^ (49797 + 49797 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 49797 * (61 : ZMod 509926561) ^ 49797) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 304706867 := by rw [factor_2_15]; decide
      have factor_2_17 : (61 : ZMod 509926561) ^ 199190 = 23956671 := by
        calc
          (61 : ZMod 509926561) ^ 199190 = (61 : ZMod 509926561) ^ (99595 + 99595) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 99595 * (61 : ZMod 509926561) ^ 99595 := by rw [pow_add]
          _ = 23956671 := by rw [factor_2_16]; decide
      have factor_2_18 : (61 : ZMod 509926561) ^ 398380 = 250923302 := by
        calc
          (61 : ZMod 509926561) ^ 398380 = (61 : ZMod 509926561) ^ (199190 + 199190) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 199190 * (61 : ZMod 509926561) ^ 199190 := by rw [pow_add]
          _ = 250923302 := by rw [factor_2_17]; decide
      have factor_2_19 : (61 : ZMod 509926561) ^ 796760 = 79360895 := by
        calc
          (61 : ZMod 509926561) ^ 796760 = (61 : ZMod 509926561) ^ (398380 + 398380) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 398380 * (61 : ZMod 509926561) ^ 398380 := by rw [pow_add]
          _ = 79360895 := by rw [factor_2_18]; decide
      have factor_2_20 : (61 : ZMod 509926561) ^ 1593520 = 257266730 := by
        calc
          (61 : ZMod 509926561) ^ 1593520 = (61 : ZMod 509926561) ^ (796760 + 796760) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 796760 * (61 : ZMod 509926561) ^ 796760 := by rw [pow_add]
          _ = 257266730 := by rw [factor_2_19]; decide
      have factor_2_21 : (61 : ZMod 509926561) ^ 3187041 = 490895310 := by
        calc
          (61 : ZMod 509926561) ^ 3187041 = (61 : ZMod 509926561) ^ (1593520 + 1593520 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1593520 * (61 : ZMod 509926561) ^ 1593520) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 490895310 := by rw [factor_2_20]; decide
      have factor_2_22 : (61 : ZMod 509926561) ^ 6374082 = 426510726 := by
        calc
          (61 : ZMod 509926561) ^ 6374082 = (61 : ZMod 509926561) ^ (3187041 + 3187041) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3187041 * (61 : ZMod 509926561) ^ 3187041 := by rw [pow_add]
          _ = 426510726 := by rw [factor_2_21]; decide
      have factor_2_23 : (61 : ZMod 509926561) ^ 12748164 = 170401408 := by
        calc
          (61 : ZMod 509926561) ^ 12748164 = (61 : ZMod 509926561) ^ (6374082 + 6374082) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 6374082 * (61 : ZMod 509926561) ^ 6374082 := by rw [pow_add]
          _ = 170401408 := by rw [factor_2_22]; decide
      have factor_2_24 : (61 : ZMod 509926561) ^ 25496328 = 299716957 := by
        calc
          (61 : ZMod 509926561) ^ 25496328 = (61 : ZMod 509926561) ^ (12748164 + 12748164) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 12748164 * (61 : ZMod 509926561) ^ 12748164 := by rw [pow_add]
          _ = 299716957 := by rw [factor_2_23]; decide
      have factor_2_25 : (61 : ZMod 509926561) ^ 50992656 = 356709529 := by
        calc
          (61 : ZMod 509926561) ^ 50992656 = (61 : ZMod 509926561) ^ (25496328 + 25496328) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 25496328 * (61 : ZMod 509926561) ^ 25496328 := by rw [pow_add]
          _ = 356709529 := by rw [factor_2_24]; decide
      have factor_2_26 : (61 : ZMod 509926561) ^ 101985312 = 401725684 := by
        calc
          (61 : ZMod 509926561) ^ 101985312 = (61 : ZMod 509926561) ^ (50992656 + 50992656) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 50992656 * (61 : ZMod 509926561) ^ 50992656 := by rw [pow_add]
          _ = 401725684 := by rw [factor_2_25]; decide
      change (61 : ZMod 509926561) ^ 101985312 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (61 : ZMod 509926561) ^ 1 = 61 := by norm_num
      have factor_3_1 : (61 : ZMod 509926561) ^ 2 = 3721 := by
        calc
          (61 : ZMod 509926561) ^ 2 = (61 : ZMod 509926561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1 * (61 : ZMod 509926561) ^ 1 := by rw [pow_add]
          _ = 3721 := by rw [factor_3_0]; decide
      have factor_3_2 : (61 : ZMod 509926561) ^ 5 = 334669740 := by
        calc
          (61 : ZMod 509926561) ^ 5 = (61 : ZMod 509926561) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 2 * (61 : ZMod 509926561) ^ 2) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 334669740 := by rw [factor_3_1]; decide
      have factor_3_3 : (61 : ZMod 509926561) ^ 11 = 446735 := by
        calc
          (61 : ZMod 509926561) ^ 11 = (61 : ZMod 509926561) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 5 * (61 : ZMod 509926561) ^ 5) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 446735 := by rw [factor_3_2]; decide
      have factor_3_4 : (61 : ZMod 509926561) ^ 22 = 190874874 := by
        calc
          (61 : ZMod 509926561) ^ 22 = (61 : ZMod 509926561) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 11 * (61 : ZMod 509926561) ^ 11 := by rw [pow_add]
          _ = 190874874 := by rw [factor_3_3]; decide
      have factor_3_5 : (61 : ZMod 509926561) ^ 44 = 401911267 := by
        calc
          (61 : ZMod 509926561) ^ 44 = (61 : ZMod 509926561) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 22 * (61 : ZMod 509926561) ^ 22 := by rw [pow_add]
          _ = 401911267 := by rw [factor_3_4]; decide
      have factor_3_6 : (61 : ZMod 509926561) ^ 88 = 448664476 := by
        calc
          (61 : ZMod 509926561) ^ 88 = (61 : ZMod 509926561) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 44 * (61 : ZMod 509926561) ^ 44 := by rw [pow_add]
          _ = 448664476 := by rw [factor_3_5]; decide
      have factor_3_7 : (61 : ZMod 509926561) ^ 176 = 397163738 := by
        calc
          (61 : ZMod 509926561) ^ 176 = (61 : ZMod 509926561) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 88 * (61 : ZMod 509926561) ^ 88 := by rw [pow_add]
          _ = 397163738 := by rw [factor_3_6]; decide
      have factor_3_8 : (61 : ZMod 509926561) ^ 353 = 11565018 := by
        calc
          (61 : ZMod 509926561) ^ 353 = (61 : ZMod 509926561) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 176 * (61 : ZMod 509926561) ^ 176) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 11565018 := by rw [factor_3_7]; decide
      have factor_3_9 : (61 : ZMod 509926561) ^ 707 = 31806354 := by
        calc
          (61 : ZMod 509926561) ^ 707 = (61 : ZMod 509926561) ^ (353 + 353 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 353 * (61 : ZMod 509926561) ^ 353) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 31806354 := by rw [factor_3_8]; decide
      have factor_3_10 : (61 : ZMod 509926561) ^ 1414 = 340478855 := by
        calc
          (61 : ZMod 509926561) ^ 1414 = (61 : ZMod 509926561) ^ (707 + 707) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 707 * (61 : ZMod 509926561) ^ 707 := by rw [pow_add]
          _ = 340478855 := by rw [factor_3_9]; decide
      have factor_3_11 : (61 : ZMod 509926561) ^ 2829 = 506894967 := by
        calc
          (61 : ZMod 509926561) ^ 2829 = (61 : ZMod 509926561) ^ (1414 + 1414 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1414 * (61 : ZMod 509926561) ^ 1414) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 506894967 := by rw [factor_3_10]; decide
      have factor_3_12 : (61 : ZMod 509926561) ^ 5658 = 155771933 := by
        calc
          (61 : ZMod 509926561) ^ 5658 = (61 : ZMod 509926561) ^ (2829 + 2829) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 2829 * (61 : ZMod 509926561) ^ 2829 := by rw [pow_add]
          _ = 155771933 := by rw [factor_3_11]; decide
      have factor_3_13 : (61 : ZMod 509926561) ^ 11317 = 386422640 := by
        calc
          (61 : ZMod 509926561) ^ 11317 = (61 : ZMod 509926561) ^ (5658 + 5658 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 5658 * (61 : ZMod 509926561) ^ 5658) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 386422640 := by rw [factor_3_12]; decide
      have factor_3_14 : (61 : ZMod 509926561) ^ 22635 = 247701547 := by
        calc
          (61 : ZMod 509926561) ^ 22635 = (61 : ZMod 509926561) ^ (11317 + 11317 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 11317 * (61 : ZMod 509926561) ^ 11317) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 247701547 := by rw [factor_3_13]; decide
      have factor_3_15 : (61 : ZMod 509926561) ^ 45270 = 120417250 := by
        calc
          (61 : ZMod 509926561) ^ 45270 = (61 : ZMod 509926561) ^ (22635 + 22635) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 22635 * (61 : ZMod 509926561) ^ 22635 := by rw [pow_add]
          _ = 120417250 := by rw [factor_3_14]; decide
      have factor_3_16 : (61 : ZMod 509926561) ^ 90540 = 85061937 := by
        calc
          (61 : ZMod 509926561) ^ 90540 = (61 : ZMod 509926561) ^ (45270 + 45270) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 45270 * (61 : ZMod 509926561) ^ 45270 := by rw [pow_add]
          _ = 85061937 := by rw [factor_3_15]; decide
      have factor_3_17 : (61 : ZMod 509926561) ^ 181081 = 428468081 := by
        calc
          (61 : ZMod 509926561) ^ 181081 = (61 : ZMod 509926561) ^ (90540 + 90540 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 90540 * (61 : ZMod 509926561) ^ 90540) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 428468081 := by rw [factor_3_16]; decide
      have factor_3_18 : (61 : ZMod 509926561) ^ 362163 = 230161614 := by
        calc
          (61 : ZMod 509926561) ^ 362163 = (61 : ZMod 509926561) ^ (181081 + 181081 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 181081 * (61 : ZMod 509926561) ^ 181081) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 230161614 := by rw [factor_3_17]; decide
      have factor_3_19 : (61 : ZMod 509926561) ^ 724327 = 246314427 := by
        calc
          (61 : ZMod 509926561) ^ 724327 = (61 : ZMod 509926561) ^ (362163 + 362163 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 362163 * (61 : ZMod 509926561) ^ 362163) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 246314427 := by rw [factor_3_18]; decide
      have factor_3_20 : (61 : ZMod 509926561) ^ 1448655 = 473471404 := by
        calc
          (61 : ZMod 509926561) ^ 1448655 = (61 : ZMod 509926561) ^ (724327 + 724327 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 724327 * (61 : ZMod 509926561) ^ 724327) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 473471404 := by rw [factor_3_19]; decide
      have factor_3_21 : (61 : ZMod 509926561) ^ 2897310 = 219718034 := by
        calc
          (61 : ZMod 509926561) ^ 2897310 = (61 : ZMod 509926561) ^ (1448655 + 1448655) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1448655 * (61 : ZMod 509926561) ^ 1448655 := by rw [pow_add]
          _ = 219718034 := by rw [factor_3_20]; decide
      have factor_3_22 : (61 : ZMod 509926561) ^ 5794620 = 277377632 := by
        calc
          (61 : ZMod 509926561) ^ 5794620 = (61 : ZMod 509926561) ^ (2897310 + 2897310) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 2897310 * (61 : ZMod 509926561) ^ 2897310 := by rw [pow_add]
          _ = 277377632 := by rw [factor_3_21]; decide
      have factor_3_23 : (61 : ZMod 509926561) ^ 11589240 = 431091467 := by
        calc
          (61 : ZMod 509926561) ^ 11589240 = (61 : ZMod 509926561) ^ (5794620 + 5794620) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 5794620 * (61 : ZMod 509926561) ^ 5794620 := by rw [pow_add]
          _ = 431091467 := by rw [factor_3_22]; decide
      have factor_3_24 : (61 : ZMod 509926561) ^ 23178480 = 378611422 := by
        calc
          (61 : ZMod 509926561) ^ 23178480 = (61 : ZMod 509926561) ^ (11589240 + 11589240) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 11589240 * (61 : ZMod 509926561) ^ 11589240 := by rw [pow_add]
          _ = 378611422 := by rw [factor_3_23]; decide
      have factor_3_25 : (61 : ZMod 509926561) ^ 46356960 = 362197663 := by
        calc
          (61 : ZMod 509926561) ^ 46356960 = (61 : ZMod 509926561) ^ (23178480 + 23178480) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 23178480 * (61 : ZMod 509926561) ^ 23178480 := by rw [pow_add]
          _ = 362197663 := by rw [factor_3_24]; decide
      change (61 : ZMod 509926561) ^ 46356960 ≠ 1
      rw [factor_3_25]
      decide
    ·
      have factor_4_0 : (61 : ZMod 509926561) ^ 1 = 61 := by norm_num
      have factor_4_1 : (61 : ZMod 509926561) ^ 2 = 3721 := by
        calc
          (61 : ZMod 509926561) ^ 2 = (61 : ZMod 509926561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1 * (61 : ZMod 509926561) ^ 1 := by rw [pow_add]
          _ = 3721 := by rw [factor_4_0]; decide
      have factor_4_2 : (61 : ZMod 509926561) ^ 4 = 13845841 := by
        calc
          (61 : ZMod 509926561) ^ 4 = (61 : ZMod 509926561) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 2 * (61 : ZMod 509926561) ^ 2 := by rw [pow_add]
          _ = 13845841 := by rw [factor_4_1]; decide
      have factor_4_3 : (61 : ZMod 509926561) ^ 9 = 269421141 := by
        calc
          (61 : ZMod 509926561) ^ 9 = (61 : ZMod 509926561) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 4 * (61 : ZMod 509926561) ^ 4) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 269421141 := by rw [factor_4_2]; decide
      have factor_4_4 : (61 : ZMod 509926561) ^ 18 = 506870700 := by
        calc
          (61 : ZMod 509926561) ^ 18 = (61 : ZMod 509926561) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 9 * (61 : ZMod 509926561) ^ 9 := by rw [pow_add]
          _ = 506870700 := by rw [factor_4_3]; decide
      have factor_4_5 : (61 : ZMod 509926561) ^ 37 = 81723408 := by
        calc
          (61 : ZMod 509926561) ^ 37 = (61 : ZMod 509926561) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 18 * (61 : ZMod 509926561) ^ 18) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 81723408 := by rw [factor_4_4]; decide
      have factor_4_6 : (61 : ZMod 509926561) ^ 74 = 215533698 := by
        calc
          (61 : ZMod 509926561) ^ 74 = (61 : ZMod 509926561) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 37 * (61 : ZMod 509926561) ^ 37 := by rw [pow_add]
          _ = 215533698 := by rw [factor_4_5]; decide
      have factor_4_7 : (61 : ZMod 509926561) ^ 149 = 271161867 := by
        calc
          (61 : ZMod 509926561) ^ 149 = (61 : ZMod 509926561) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 74 * (61 : ZMod 509926561) ^ 74) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 271161867 := by rw [factor_4_6]; decide
      have factor_4_8 : (61 : ZMod 509926561) ^ 299 = 284184913 := by
        calc
          (61 : ZMod 509926561) ^ 299 = (61 : ZMod 509926561) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 149 * (61 : ZMod 509926561) ^ 149) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 284184913 := by rw [factor_4_7]; decide
      have factor_4_9 : (61 : ZMod 509926561) ^ 598 = 36642134 := by
        calc
          (61 : ZMod 509926561) ^ 598 = (61 : ZMod 509926561) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 299 * (61 : ZMod 509926561) ^ 299 := by rw [pow_add]
          _ = 36642134 := by rw [factor_4_8]; decide
      have factor_4_10 : (61 : ZMod 509926561) ^ 1197 = 188723118 := by
        calc
          (61 : ZMod 509926561) ^ 1197 = (61 : ZMod 509926561) ^ (598 + 598 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 598 * (61 : ZMod 509926561) ^ 598) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 188723118 := by rw [factor_4_9]; decide
      have factor_4_11 : (61 : ZMod 509926561) ^ 2394 = 40226798 := by
        calc
          (61 : ZMod 509926561) ^ 2394 = (61 : ZMod 509926561) ^ (1197 + 1197) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1197 * (61 : ZMod 509926561) ^ 1197 := by rw [pow_add]
          _ = 40226798 := by rw [factor_4_10]; decide
      have factor_4_12 : (61 : ZMod 509926561) ^ 4788 = 447774136 := by
        calc
          (61 : ZMod 509926561) ^ 4788 = (61 : ZMod 509926561) ^ (2394 + 2394) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 2394 * (61 : ZMod 509926561) ^ 2394 := by rw [pow_add]
          _ = 447774136 := by rw [factor_4_11]; decide
      have factor_4_13 : (61 : ZMod 509926561) ^ 9576 = 256926614 := by
        calc
          (61 : ZMod 509926561) ^ 9576 = (61 : ZMod 509926561) ^ (4788 + 4788) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 4788 * (61 : ZMod 509926561) ^ 4788 := by rw [pow_add]
          _ = 256926614 := by rw [factor_4_12]; decide
      have factor_4_14 : (61 : ZMod 509926561) ^ 19152 = 16075983 := by
        calc
          (61 : ZMod 509926561) ^ 19152 = (61 : ZMod 509926561) ^ (9576 + 9576) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 9576 * (61 : ZMod 509926561) ^ 9576 := by rw [pow_add]
          _ = 16075983 := by rw [factor_4_13]; decide
      have factor_4_15 : (61 : ZMod 509926561) ^ 38305 = 193012298 := by
        calc
          (61 : ZMod 509926561) ^ 38305 = (61 : ZMod 509926561) ^ (19152 + 19152 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 19152 * (61 : ZMod 509926561) ^ 19152) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 193012298 := by rw [factor_4_14]; decide
      have factor_4_16 : (61 : ZMod 509926561) ^ 76611 = 290648091 := by
        calc
          (61 : ZMod 509926561) ^ 76611 = (61 : ZMod 509926561) ^ (38305 + 38305 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 38305 * (61 : ZMod 509926561) ^ 38305) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 290648091 := by rw [factor_4_15]; decide
      have factor_4_17 : (61 : ZMod 509926561) ^ 153223 = 212422001 := by
        calc
          (61 : ZMod 509926561) ^ 153223 = (61 : ZMod 509926561) ^ (76611 + 76611 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 76611 * (61 : ZMod 509926561) ^ 76611) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 212422001 := by rw [factor_4_16]; decide
      have factor_4_18 : (61 : ZMod 509926561) ^ 306446 = 373432820 := by
        calc
          (61 : ZMod 509926561) ^ 306446 = (61 : ZMod 509926561) ^ (153223 + 153223) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 153223 * (61 : ZMod 509926561) ^ 153223 := by rw [pow_add]
          _ = 373432820 := by rw [factor_4_17]; decide
      have factor_4_19 : (61 : ZMod 509926561) ^ 612892 = 139944307 := by
        calc
          (61 : ZMod 509926561) ^ 612892 = (61 : ZMod 509926561) ^ (306446 + 306446) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 306446 * (61 : ZMod 509926561) ^ 306446 := by rw [pow_add]
          _ = 139944307 := by rw [factor_4_18]; decide
      have factor_4_20 : (61 : ZMod 509926561) ^ 1225785 = 316162426 := by
        calc
          (61 : ZMod 509926561) ^ 1225785 = (61 : ZMod 509926561) ^ (612892 + 612892 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 612892 * (61 : ZMod 509926561) ^ 612892) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 316162426 := by rw [factor_4_19]; decide
      have factor_4_21 : (61 : ZMod 509926561) ^ 2451570 = 161034558 := by
        calc
          (61 : ZMod 509926561) ^ 2451570 = (61 : ZMod 509926561) ^ (1225785 + 1225785) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1225785 * (61 : ZMod 509926561) ^ 1225785 := by rw [pow_add]
          _ = 161034558 := by rw [factor_4_20]; decide
      have factor_4_22 : (61 : ZMod 509926561) ^ 4903140 = 243721690 := by
        calc
          (61 : ZMod 509926561) ^ 4903140 = (61 : ZMod 509926561) ^ (2451570 + 2451570) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 2451570 * (61 : ZMod 509926561) ^ 2451570 := by rw [pow_add]
          _ = 243721690 := by rw [factor_4_21]; decide
      have factor_4_23 : (61 : ZMod 509926561) ^ 9806280 = 169581664 := by
        calc
          (61 : ZMod 509926561) ^ 9806280 = (61 : ZMod 509926561) ^ (4903140 + 4903140) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 4903140 * (61 : ZMod 509926561) ^ 4903140 := by rw [pow_add]
          _ = 169581664 := by rw [factor_4_22]; decide
      have factor_4_24 : (61 : ZMod 509926561) ^ 19612560 = 48478256 := by
        calc
          (61 : ZMod 509926561) ^ 19612560 = (61 : ZMod 509926561) ^ (9806280 + 9806280) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 9806280 * (61 : ZMod 509926561) ^ 9806280 := by rw [pow_add]
          _ = 48478256 := by rw [factor_4_23]; decide
      have factor_4_25 : (61 : ZMod 509926561) ^ 39225120 = 439216273 := by
        calc
          (61 : ZMod 509926561) ^ 39225120 = (61 : ZMod 509926561) ^ (19612560 + 19612560) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 19612560 * (61 : ZMod 509926561) ^ 19612560 := by rw [pow_add]
          _ = 439216273 := by rw [factor_4_24]; decide
      change (61 : ZMod 509926561) ^ 39225120 ≠ 1
      rw [factor_4_25]
      decide
    ·
      have factor_5_0 : (61 : ZMod 509926561) ^ 1 = 61 := by norm_num
      have factor_5_1 : (61 : ZMod 509926561) ^ 3 = 226981 := by
        calc
          (61 : ZMod 509926561) ^ 3 = (61 : ZMod 509926561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1 * (61 : ZMod 509926561) ^ 1) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 226981 := by rw [factor_5_0]; decide
      have factor_5_2 : (61 : ZMod 509926561) ^ 7 = 65440578 := by
        calc
          (61 : ZMod 509926561) ^ 7 = (61 : ZMod 509926561) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 3 * (61 : ZMod 509926561) ^ 3) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 65440578 := by rw [factor_5_1]; decide
      have factor_5_3 : (61 : ZMod 509926561) ^ 14 = 434897957 := by
        calc
          (61 : ZMod 509926561) ^ 14 = (61 : ZMod 509926561) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 7 * (61 : ZMod 509926561) ^ 7 := by rw [pow_add]
          _ = 434897957 := by rw [factor_5_2]; decide
      have factor_5_4 : (61 : ZMod 509926561) ^ 28 = 491787001 := by
        calc
          (61 : ZMod 509926561) ^ 28 = (61 : ZMod 509926561) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 14 * (61 : ZMod 509926561) ^ 14 := by rw [pow_add]
          _ = 491787001 := by rw [factor_5_3]; decide
      have factor_5_5 : (61 : ZMod 509926561) ^ 57 = 382760213 := by
        calc
          (61 : ZMod 509926561) ^ 57 = (61 : ZMod 509926561) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 28 * (61 : ZMod 509926561) ^ 28) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 382760213 := by rw [factor_5_4]; decide
      have factor_5_6 : (61 : ZMod 509926561) ^ 114 = 451579666 := by
        calc
          (61 : ZMod 509926561) ^ 114 = (61 : ZMod 509926561) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 57 * (61 : ZMod 509926561) ^ 57 := by rw [pow_add]
          _ = 451579666 := by rw [factor_5_5]; decide
      have factor_5_7 : (61 : ZMod 509926561) ^ 228 = 177903728 := by
        calc
          (61 : ZMod 509926561) ^ 228 = (61 : ZMod 509926561) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 114 * (61 : ZMod 509926561) ^ 114 := by rw [pow_add]
          _ = 177903728 := by rw [factor_5_6]; decide
      have factor_5_8 : (61 : ZMod 509926561) ^ 457 = 131758002 := by
        calc
          (61 : ZMod 509926561) ^ 457 = (61 : ZMod 509926561) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 228 * (61 : ZMod 509926561) ^ 228) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 131758002 := by rw [factor_5_7]; decide
      have factor_5_9 : (61 : ZMod 509926561) ^ 915 = 50771301 := by
        calc
          (61 : ZMod 509926561) ^ 915 = (61 : ZMod 509926561) ^ (457 + 457 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 457 * (61 : ZMod 509926561) ^ 457) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 50771301 := by rw [factor_5_8]; decide
      have factor_5_10 : (61 : ZMod 509926561) ^ 1830 = 345987111 := by
        calc
          (61 : ZMod 509926561) ^ 1830 = (61 : ZMod 509926561) ^ (915 + 915) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 915 * (61 : ZMod 509926561) ^ 915 := by rw [pow_add]
          _ = 345987111 := by rw [factor_5_9]; decide
      have factor_5_11 : (61 : ZMod 509926561) ^ 3661 = 171777610 := by
        calc
          (61 : ZMod 509926561) ^ 3661 = (61 : ZMod 509926561) ^ (1830 + 1830 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1830 * (61 : ZMod 509926561) ^ 1830) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 171777610 := by rw [factor_5_10]; decide
      have factor_5_12 : (61 : ZMod 509926561) ^ 7323 = 450436042 := by
        calc
          (61 : ZMod 509926561) ^ 7323 = (61 : ZMod 509926561) ^ (3661 + 3661 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 3661 * (61 : ZMod 509926561) ^ 3661) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 450436042 := by rw [factor_5_11]; decide
      have factor_5_13 : (61 : ZMod 509926561) ^ 14646 = 10890667 := by
        calc
          (61 : ZMod 509926561) ^ 14646 = (61 : ZMod 509926561) ^ (7323 + 7323) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 7323 * (61 : ZMod 509926561) ^ 7323 := by rw [pow_add]
          _ = 10890667 := by rw [factor_5_12]; decide
      have factor_5_14 : (61 : ZMod 509926561) ^ 29292 = 259249094 := by
        calc
          (61 : ZMod 509926561) ^ 29292 = (61 : ZMod 509926561) ^ (14646 + 14646) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 14646 * (61 : ZMod 509926561) ^ 14646 := by rw [pow_add]
          _ = 259249094 := by rw [factor_5_13]; decide
      have factor_5_15 : (61 : ZMod 509926561) ^ 58585 = 318503021 := by
        calc
          (61 : ZMod 509926561) ^ 58585 = (61 : ZMod 509926561) ^ (29292 + 29292 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 29292 * (61 : ZMod 509926561) ^ 29292) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 318503021 := by rw [factor_5_14]; decide
      have factor_5_16 : (61 : ZMod 509926561) ^ 117170 = 332072129 := by
        calc
          (61 : ZMod 509926561) ^ 117170 = (61 : ZMod 509926561) ^ (58585 + 58585) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 58585 * (61 : ZMod 509926561) ^ 58585 := by rw [pow_add]
          _ = 332072129 := by rw [factor_5_15]; decide
      have factor_5_17 : (61 : ZMod 509926561) ^ 234341 = 43107601 := by
        calc
          (61 : ZMod 509926561) ^ 234341 = (61 : ZMod 509926561) ^ (117170 + 117170 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 117170 * (61 : ZMod 509926561) ^ 117170) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 43107601 := by rw [factor_5_16]; decide
      have factor_5_18 : (61 : ZMod 509926561) ^ 468682 = 69057099 := by
        calc
          (61 : ZMod 509926561) ^ 468682 = (61 : ZMod 509926561) ^ (234341 + 234341) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 234341 * (61 : ZMod 509926561) ^ 234341 := by rw [pow_add]
          _ = 69057099 := by rw [factor_5_17]; decide
      have factor_5_19 : (61 : ZMod 509926561) ^ 937365 = 110067033 := by
        calc
          (61 : ZMod 509926561) ^ 937365 = (61 : ZMod 509926561) ^ (468682 + 468682 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 468682 * (61 : ZMod 509926561) ^ 468682) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 110067033 := by rw [factor_5_18]; decide
      have factor_5_20 : (61 : ZMod 509926561) ^ 1874730 = 145141093 := by
        calc
          (61 : ZMod 509926561) ^ 1874730 = (61 : ZMod 509926561) ^ (937365 + 937365) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 937365 * (61 : ZMod 509926561) ^ 937365 := by rw [pow_add]
          _ = 145141093 := by rw [factor_5_19]; decide
      have factor_5_21 : (61 : ZMod 509926561) ^ 3749460 = 197685022 := by
        calc
          (61 : ZMod 509926561) ^ 3749460 = (61 : ZMod 509926561) ^ (1874730 + 1874730) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1874730 * (61 : ZMod 509926561) ^ 1874730 := by rw [pow_add]
          _ = 197685022 := by rw [factor_5_20]; decide
      have factor_5_22 : (61 : ZMod 509926561) ^ 7498920 = 115922917 := by
        calc
          (61 : ZMod 509926561) ^ 7498920 = (61 : ZMod 509926561) ^ (3749460 + 3749460) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3749460 * (61 : ZMod 509926561) ^ 3749460 := by rw [pow_add]
          _ = 115922917 := by rw [factor_5_21]; decide
      have factor_5_23 : (61 : ZMod 509926561) ^ 14997840 = 487721595 := by
        calc
          (61 : ZMod 509926561) ^ 14997840 = (61 : ZMod 509926561) ^ (7498920 + 7498920) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 7498920 * (61 : ZMod 509926561) ^ 7498920 := by rw [pow_add]
          _ = 487721595 := by rw [factor_5_22]; decide
      have factor_5_24 : (61 : ZMod 509926561) ^ 29995680 = 284992792 := by
        calc
          (61 : ZMod 509926561) ^ 29995680 = (61 : ZMod 509926561) ^ (14997840 + 14997840) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 14997840 * (61 : ZMod 509926561) ^ 14997840 := by rw [pow_add]
          _ = 284992792 := by rw [factor_5_23]; decide
      change (61 : ZMod 509926561) ^ 29995680 ≠ 1
      rw [factor_5_24]
      decide
    ·
      have factor_6_0 : (61 : ZMod 509926561) ^ 1 = 61 := by norm_num
      have factor_6_1 : (61 : ZMod 509926561) ^ 3 = 226981 := by
        calc
          (61 : ZMod 509926561) ^ 3 = (61 : ZMod 509926561) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 1 * (61 : ZMod 509926561) ^ 1) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 226981 := by rw [factor_6_0]; decide
      have factor_6_2 : (61 : ZMod 509926561) ^ 6 = 17791700 := by
        calc
          (61 : ZMod 509926561) ^ 6 = (61 : ZMod 509926561) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3 * (61 : ZMod 509926561) ^ 3 := by rw [pow_add]
          _ = 17791700 := by rw [factor_6_1]; decide
      have factor_6_3 : (61 : ZMod 509926561) ^ 12 = 27250835 := by
        calc
          (61 : ZMod 509926561) ^ 12 = (61 : ZMod 509926561) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 6 * (61 : ZMod 509926561) ^ 6 := by rw [pow_add]
          _ = 27250835 := by rw [factor_6_2]; decide
      have factor_6_4 : (61 : ZMod 509926561) ^ 25 = 79373151 := by
        calc
          (61 : ZMod 509926561) ^ 25 = (61 : ZMod 509926561) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 12 * (61 : ZMod 509926561) ^ 12) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 79373151 := by rw [factor_6_3]; decide
      have factor_6_5 : (61 : ZMod 509926561) ^ 51 = 359025872 := by
        calc
          (61 : ZMod 509926561) ^ 51 = (61 : ZMod 509926561) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 25 * (61 : ZMod 509926561) ^ 25) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 359025872 := by rw [factor_6_4]; decide
      have factor_6_6 : (61 : ZMod 509926561) ^ 102 = 44837636 := by
        calc
          (61 : ZMod 509926561) ^ 102 = (61 : ZMod 509926561) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 51 * (61 : ZMod 509926561) ^ 51 := by rw [pow_add]
          _ = 44837636 := by rw [factor_6_5]; decide
      have factor_6_7 : (61 : ZMod 509926561) ^ 204 = 89365141 := by
        calc
          (61 : ZMod 509926561) ^ 204 = (61 : ZMod 509926561) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 102 * (61 : ZMod 509926561) ^ 102 := by rw [pow_add]
          _ = 89365141 := by rw [factor_6_6]; decide
      have factor_6_8 : (61 : ZMod 509926561) ^ 409 = 152612298 := by
        calc
          (61 : ZMod 509926561) ^ 409 = (61 : ZMod 509926561) ^ (204 + 204 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 204 * (61 : ZMod 509926561) ^ 204) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 152612298 := by rw [factor_6_7]; decide
      have factor_6_9 : (61 : ZMod 509926561) ^ 819 = 279629842 := by
        calc
          (61 : ZMod 509926561) ^ 819 = (61 : ZMod 509926561) ^ (409 + 409 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 409 * (61 : ZMod 509926561) ^ 409) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 279629842 := by rw [factor_6_8]; decide
      have factor_6_10 : (61 : ZMod 509926561) ^ 1638 = 365358613 := by
        calc
          (61 : ZMod 509926561) ^ 1638 = (61 : ZMod 509926561) ^ (819 + 819) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 819 * (61 : ZMod 509926561) ^ 819 := by rw [pow_add]
          _ = 365358613 := by rw [factor_6_9]; decide
      have factor_6_11 : (61 : ZMod 509926561) ^ 3276 = 255733263 := by
        calc
          (61 : ZMod 509926561) ^ 3276 = (61 : ZMod 509926561) ^ (1638 + 1638) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1638 * (61 : ZMod 509926561) ^ 1638 := by rw [pow_add]
          _ = 255733263 := by rw [factor_6_10]; decide
      have factor_6_12 : (61 : ZMod 509926561) ^ 6552 = 210904784 := by
        calc
          (61 : ZMod 509926561) ^ 6552 = (61 : ZMod 509926561) ^ (3276 + 3276) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3276 * (61 : ZMod 509926561) ^ 3276 := by rw [pow_add]
          _ = 210904784 := by rw [factor_6_11]; decide
      have factor_6_13 : (61 : ZMod 509926561) ^ 13104 = 288509586 := by
        calc
          (61 : ZMod 509926561) ^ 13104 = (61 : ZMod 509926561) ^ (6552 + 6552) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 6552 * (61 : ZMod 509926561) ^ 6552 := by rw [pow_add]
          _ = 288509586 := by rw [factor_6_12]; decide
      have factor_6_14 : (61 : ZMod 509926561) ^ 26209 = 431036563 := by
        calc
          (61 : ZMod 509926561) ^ 26209 = (61 : ZMod 509926561) ^ (13104 + 13104 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 13104 * (61 : ZMod 509926561) ^ 13104) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 431036563 := by rw [factor_6_13]; decide
      have factor_6_15 : (61 : ZMod 509926561) ^ 52418 = 34277127 := by
        calc
          (61 : ZMod 509926561) ^ 52418 = (61 : ZMod 509926561) ^ (26209 + 26209) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 26209 * (61 : ZMod 509926561) ^ 26209 := by rw [pow_add]
          _ = 34277127 := by rw [factor_6_14]; decide
      have factor_6_16 : (61 : ZMod 509926561) ^ 104836 = 156100590 := by
        calc
          (61 : ZMod 509926561) ^ 104836 = (61 : ZMod 509926561) ^ (52418 + 52418) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 52418 * (61 : ZMod 509926561) ^ 52418 := by rw [pow_add]
          _ = 156100590 := by rw [factor_6_15]; decide
      have factor_6_17 : (61 : ZMod 509926561) ^ 209673 = 101145290 := by
        calc
          (61 : ZMod 509926561) ^ 209673 = (61 : ZMod 509926561) ^ (104836 + 104836 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 104836 * (61 : ZMod 509926561) ^ 104836) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 101145290 := by rw [factor_6_16]; decide
      have factor_6_18 : (61 : ZMod 509926561) ^ 419347 = 35807181 := by
        calc
          (61 : ZMod 509926561) ^ 419347 = (61 : ZMod 509926561) ^ (209673 + 209673 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 209673 * (61 : ZMod 509926561) ^ 209673) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 35807181 := by rw [factor_6_17]; decide
      have factor_6_19 : (61 : ZMod 509926561) ^ 838695 = 442325036 := by
        calc
          (61 : ZMod 509926561) ^ 838695 = (61 : ZMod 509926561) ^ (419347 + 419347 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 419347 * (61 : ZMod 509926561) ^ 419347) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 442325036 := by rw [factor_6_18]; decide
      have factor_6_20 : (61 : ZMod 509926561) ^ 1677390 = 263231137 := by
        calc
          (61 : ZMod 509926561) ^ 1677390 = (61 : ZMod 509926561) ^ (838695 + 838695) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 838695 * (61 : ZMod 509926561) ^ 838695 := by rw [pow_add]
          _ = 263231137 := by rw [factor_6_19]; decide
      have factor_6_21 : (61 : ZMod 509926561) ^ 3354780 = 138341219 := by
        calc
          (61 : ZMod 509926561) ^ 3354780 = (61 : ZMod 509926561) ^ (1677390 + 1677390) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1677390 * (61 : ZMod 509926561) ^ 1677390 := by rw [pow_add]
          _ = 138341219 := by rw [factor_6_20]; decide
      have factor_6_22 : (61 : ZMod 509926561) ^ 6709560 = 467884413 := by
        calc
          (61 : ZMod 509926561) ^ 6709560 = (61 : ZMod 509926561) ^ (3354780 + 3354780) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 3354780 * (61 : ZMod 509926561) ^ 3354780 := by rw [pow_add]
          _ = 467884413 := by rw [factor_6_21]; decide
      have factor_6_23 : (61 : ZMod 509926561) ^ 13419120 = 87709556 := by
        calc
          (61 : ZMod 509926561) ^ 13419120 = (61 : ZMod 509926561) ^ (6709560 + 6709560) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 6709560 * (61 : ZMod 509926561) ^ 6709560 := by rw [pow_add]
          _ = 87709556 := by rw [factor_6_22]; decide
      have factor_6_24 : (61 : ZMod 509926561) ^ 26838240 = 455242077 := by
        calc
          (61 : ZMod 509926561) ^ 26838240 = (61 : ZMod 509926561) ^ (13419120 + 13419120) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 13419120 * (61 : ZMod 509926561) ^ 13419120 := by rw [pow_add]
          _ = 455242077 := by rw [factor_6_23]; decide
      change (61 : ZMod 509926561) ^ 26838240 ≠ 1
      rw [factor_6_24]
      decide
    ·
      have factor_7_0 : (61 : ZMod 509926561) ^ 1 = 61 := by norm_num
      have factor_7_1 : (61 : ZMod 509926561) ^ 2 = 3721 := by
        calc
          (61 : ZMod 509926561) ^ 2 = (61 : ZMod 509926561) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1 * (61 : ZMod 509926561) ^ 1 := by rw [pow_add]
          _ = 3721 := by rw [factor_7_0]; decide
      have factor_7_2 : (61 : ZMod 509926561) ^ 5 = 334669740 := by
        calc
          (61 : ZMod 509926561) ^ 5 = (61 : ZMod 509926561) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 2 * (61 : ZMod 509926561) ^ 2) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 334669740 := by rw [factor_7_1]; decide
      have factor_7_3 : (61 : ZMod 509926561) ^ 10 = 117039649 := by
        calc
          (61 : ZMod 509926561) ^ 10 = (61 : ZMod 509926561) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 5 * (61 : ZMod 509926561) ^ 5 := by rw [pow_add]
          _ = 117039649 := by rw [factor_7_2]; decide
      have factor_7_4 : (61 : ZMod 509926561) ^ 21 = 387663880 := by
        calc
          (61 : ZMod 509926561) ^ 21 = (61 : ZMod 509926561) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 10 * (61 : ZMod 509926561) ^ 10) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 387663880 := by rw [factor_7_3]; decide
      have factor_7_5 : (61 : ZMod 509926561) ^ 42 = 31490216 := by
        calc
          (61 : ZMod 509926561) ^ 42 = (61 : ZMod 509926561) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 21 * (61 : ZMod 509926561) ^ 21 := by rw [pow_add]
          _ = 31490216 := by rw [factor_7_4]; decide
      have factor_7_6 : (61 : ZMod 509926561) ^ 84 = 427538957 := by
        calc
          (61 : ZMod 509926561) ^ 84 = (61 : ZMod 509926561) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 42 * (61 : ZMod 509926561) ^ 42 := by rw [pow_add]
          _ = 427538957 := by rw [factor_7_5]; decide
      have factor_7_7 : (61 : ZMod 509926561) ^ 169 = 468037748 := by
        calc
          (61 : ZMod 509926561) ^ 169 = (61 : ZMod 509926561) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 84 * (61 : ZMod 509926561) ^ 84) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 468037748 := by rw [factor_7_6]; decide
      have factor_7_8 : (61 : ZMod 509926561) ^ 338 = 60351139 := by
        calc
          (61 : ZMod 509926561) ^ 338 = (61 : ZMod 509926561) ^ (169 + 169) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 169 * (61 : ZMod 509926561) ^ 169 := by rw [pow_add]
          _ = 60351139 := by rw [factor_7_7]; decide
      have factor_7_9 : (61 : ZMod 509926561) ^ 676 = 392370767 := by
        calc
          (61 : ZMod 509926561) ^ 676 = (61 : ZMod 509926561) ^ (338 + 338) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 338 * (61 : ZMod 509926561) ^ 338 := by rw [pow_add]
          _ = 392370767 := by rw [factor_7_8]; decide
      have factor_7_10 : (61 : ZMod 509926561) ^ 1353 = 469875902 := by
        calc
          (61 : ZMod 509926561) ^ 1353 = (61 : ZMod 509926561) ^ (676 + 676 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 676 * (61 : ZMod 509926561) ^ 676) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 469875902 := by rw [factor_7_9]; decide
      have factor_7_11 : (61 : ZMod 509926561) ^ 2706 = 210385582 := by
        calc
          (61 : ZMod 509926561) ^ 2706 = (61 : ZMod 509926561) ^ (1353 + 1353) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1353 * (61 : ZMod 509926561) ^ 1353 := by rw [pow_add]
          _ = 210385582 := by rw [factor_7_10]; decide
      have factor_7_12 : (61 : ZMod 509926561) ^ 5412 = 16022287 := by
        calc
          (61 : ZMod 509926561) ^ 5412 = (61 : ZMod 509926561) ^ (2706 + 2706) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 2706 * (61 : ZMod 509926561) ^ 2706 := by rw [pow_add]
          _ = 16022287 := by rw [factor_7_11]; decide
      have factor_7_13 : (61 : ZMod 509926561) ^ 10825 = 380298158 := by
        calc
          (61 : ZMod 509926561) ^ 10825 = (61 : ZMod 509926561) ^ (5412 + 5412 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 5412 * (61 : ZMod 509926561) ^ 5412) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 380298158 := by rw [factor_7_12]; decide
      have factor_7_14 : (61 : ZMod 509926561) ^ 21651 = 316307569 := by
        calc
          (61 : ZMod 509926561) ^ 21651 = (61 : ZMod 509926561) ^ (10825 + 10825 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 10825 * (61 : ZMod 509926561) ^ 10825) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 316307569 := by rw [factor_7_13]; decide
      have factor_7_15 : (61 : ZMod 509926561) ^ 43302 = 244227940 := by
        calc
          (61 : ZMod 509926561) ^ 43302 = (61 : ZMod 509926561) ^ (21651 + 21651) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 21651 * (61 : ZMod 509926561) ^ 21651 := by rw [pow_add]
          _ = 244227940 := by rw [factor_7_14]; decide
      have factor_7_16 : (61 : ZMod 509926561) ^ 86604 = 435897373 := by
        calc
          (61 : ZMod 509926561) ^ 86604 = (61 : ZMod 509926561) ^ (43302 + 43302) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 43302 * (61 : ZMod 509926561) ^ 43302 := by rw [pow_add]
          _ = 435897373 := by rw [factor_7_15]; decide
      have factor_7_17 : (61 : ZMod 509926561) ^ 173208 = 204994630 := by
        calc
          (61 : ZMod 509926561) ^ 173208 = (61 : ZMod 509926561) ^ (86604 + 86604) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 86604 * (61 : ZMod 509926561) ^ 86604 := by rw [pow_add]
          _ = 204994630 := by rw [factor_7_16]; decide
      have factor_7_18 : (61 : ZMod 509926561) ^ 346417 = 503919555 := by
        calc
          (61 : ZMod 509926561) ^ 346417 = (61 : ZMod 509926561) ^ (173208 + 173208 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 173208 * (61 : ZMod 509926561) ^ 173208) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 503919555 := by rw [factor_7_17]; decide
      have factor_7_19 : (61 : ZMod 509926561) ^ 692835 = 240343231 := by
        calc
          (61 : ZMod 509926561) ^ 692835 = (61 : ZMod 509926561) ^ (346417 + 346417 + 1) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = ((61 : ZMod 509926561) ^ 346417 * (61 : ZMod 509926561) ^ 346417) * (61 : ZMod 509926561) := by rw [pow_succ, pow_add]
          _ = 240343231 := by rw [factor_7_18]; decide
      have factor_7_20 : (61 : ZMod 509926561) ^ 1385670 = 313253001 := by
        calc
          (61 : ZMod 509926561) ^ 1385670 = (61 : ZMod 509926561) ^ (692835 + 692835) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 692835 * (61 : ZMod 509926561) ^ 692835 := by rw [pow_add]
          _ = 313253001 := by rw [factor_7_19]; decide
      have factor_7_21 : (61 : ZMod 509926561) ^ 2771340 = 229813941 := by
        calc
          (61 : ZMod 509926561) ^ 2771340 = (61 : ZMod 509926561) ^ (1385670 + 1385670) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 1385670 * (61 : ZMod 509926561) ^ 1385670 := by rw [pow_add]
          _ = 229813941 := by rw [factor_7_20]; decide
      have factor_7_22 : (61 : ZMod 509926561) ^ 5542680 = 210088587 := by
        calc
          (61 : ZMod 509926561) ^ 5542680 = (61 : ZMod 509926561) ^ (2771340 + 2771340) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 2771340 * (61 : ZMod 509926561) ^ 2771340 := by rw [pow_add]
          _ = 210088587 := by rw [factor_7_21]; decide
      have factor_7_23 : (61 : ZMod 509926561) ^ 11085360 = 265282788 := by
        calc
          (61 : ZMod 509926561) ^ 11085360 = (61 : ZMod 509926561) ^ (5542680 + 5542680) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 5542680 * (61 : ZMod 509926561) ^ 5542680 := by rw [pow_add]
          _ = 265282788 := by rw [factor_7_22]; decide
      have factor_7_24 : (61 : ZMod 509926561) ^ 22170720 = 64414798 := by
        calc
          (61 : ZMod 509926561) ^ 22170720 = (61 : ZMod 509926561) ^ (11085360 + 11085360) :=
            congrArg (fun n : ℕ => (61 : ZMod 509926561) ^ n) (by norm_num)
          _ = (61 : ZMod 509926561) ^ 11085360 * (61 : ZMod 509926561) ^ 11085360 := by rw [pow_add]
          _ = 64414798 := by rw [factor_7_23]; decide
      change (61 : ZMod 509926561) ^ 22170720 ≠ 1
      rw [factor_7_24]
      decide

#print axioms prime_lucas_509926561

end TotientTailPeriodKiller
end Erdos249257
