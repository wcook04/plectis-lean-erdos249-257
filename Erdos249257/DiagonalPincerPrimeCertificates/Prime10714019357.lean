import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_10714019357 : Nat.Prime 10714019357 := by
  apply lucas_primality 10714019357 (2 : ZMod 10714019357)
  ·
      have fermat_0 : (2 : ZMod 10714019357) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 10714019357) ^ 2 = 4 := by
        calc
          (2 : ZMod 10714019357) ^ 2 = (2 : ZMod 10714019357) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 1 * (2 : ZMod 10714019357) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 10714019357) ^ 4 = 16 := by
        calc
          (2 : ZMod 10714019357) ^ 4 = (2 : ZMod 10714019357) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 2 * (2 : ZMod 10714019357) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 10714019357) ^ 9 = 512 := by
        calc
          (2 : ZMod 10714019357) ^ 9 = (2 : ZMod 10714019357) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 4 * (2 : ZMod 10714019357) ^ 4) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 10714019357) ^ 19 = 524288 := by
        calc
          (2 : ZMod 10714019357) ^ 19 = (2 : ZMod 10714019357) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 9 * (2 : ZMod 10714019357) ^ 9) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 10714019357) ^ 39 = 3340826681 := by
        calc
          (2 : ZMod 10714019357) ^ 39 = (2 : ZMod 10714019357) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 19 * (2 : ZMod 10714019357) ^ 19) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3340826681 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 10714019357) ^ 79 = 2230534937 := by
        calc
          (2 : ZMod 10714019357) ^ 79 = (2 : ZMod 10714019357) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 39 * (2 : ZMod 10714019357) ^ 39) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 2230534937 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 10714019357) ^ 159 = 5719820461 := by
        calc
          (2 : ZMod 10714019357) ^ 159 = (2 : ZMod 10714019357) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 79 * (2 : ZMod 10714019357) ^ 79) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 5719820461 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 10714019357) ^ 319 = 3046137056 := by
        calc
          (2 : ZMod 10714019357) ^ 319 = (2 : ZMod 10714019357) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 159 * (2 : ZMod 10714019357) ^ 159) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3046137056 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 10714019357) ^ 638 = 5229907915 := by
        calc
          (2 : ZMod 10714019357) ^ 638 = (2 : ZMod 10714019357) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 319 * (2 : ZMod 10714019357) ^ 319 := by rw [pow_add]
          _ = 5229907915 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 10714019357) ^ 1277 = 166711850 := by
        calc
          (2 : ZMod 10714019357) ^ 1277 = (2 : ZMod 10714019357) ^ (638 + 638 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 638 * (2 : ZMod 10714019357) ^ 638) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 166711850 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 10714019357) ^ 2554 = 10449164366 := by
        calc
          (2 : ZMod 10714019357) ^ 2554 = (2 : ZMod 10714019357) ^ (1277 + 1277) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 1277 * (2 : ZMod 10714019357) ^ 1277 := by rw [pow_add]
          _ = 10449164366 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 10714019357) ^ 5108 = 10185059413 := by
        calc
          (2 : ZMod 10714019357) ^ 5108 = (2 : ZMod 10714019357) ^ (2554 + 2554) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 2554 * (2 : ZMod 10714019357) ^ 2554 := by rw [pow_add]
          _ = 10185059413 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 10714019357) ^ 10217 = 6653616754 := by
        calc
          (2 : ZMod 10714019357) ^ 10217 = (2 : ZMod 10714019357) ^ (5108 + 5108 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 5108 * (2 : ZMod 10714019357) ^ 5108) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 6653616754 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 10714019357) ^ 20435 = 5572612353 := by
        calc
          (2 : ZMod 10714019357) ^ 20435 = (2 : ZMod 10714019357) ^ (10217 + 10217 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 10217 * (2 : ZMod 10714019357) ^ 10217) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 5572612353 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 10714019357) ^ 40870 = 1921567777 := by
        calc
          (2 : ZMod 10714019357) ^ 40870 = (2 : ZMod 10714019357) ^ (20435 + 20435) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 20435 * (2 : ZMod 10714019357) ^ 20435 := by rw [pow_add]
          _ = 1921567777 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 10714019357) ^ 81741 = 6558132226 := by
        calc
          (2 : ZMod 10714019357) ^ 81741 = (2 : ZMod 10714019357) ^ (40870 + 40870 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 40870 * (2 : ZMod 10714019357) ^ 40870) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 6558132226 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 10714019357) ^ 163482 = 5609195262 := by
        calc
          (2 : ZMod 10714019357) ^ 163482 = (2 : ZMod 10714019357) ^ (81741 + 81741) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 81741 * (2 : ZMod 10714019357) ^ 81741 := by rw [pow_add]
          _ = 5609195262 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 10714019357) ^ 326965 = 8130254386 := by
        calc
          (2 : ZMod 10714019357) ^ 326965 = (2 : ZMod 10714019357) ^ (163482 + 163482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 163482 * (2 : ZMod 10714019357) ^ 163482) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8130254386 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 10714019357) ^ 653931 = 3427255260 := by
        calc
          (2 : ZMod 10714019357) ^ 653931 = (2 : ZMod 10714019357) ^ (326965 + 326965 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 326965 * (2 : ZMod 10714019357) ^ 326965) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3427255260 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 10714019357) ^ 1307863 = 3542027393 := by
        calc
          (2 : ZMod 10714019357) ^ 1307863 = (2 : ZMod 10714019357) ^ (653931 + 653931 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 653931 * (2 : ZMod 10714019357) ^ 653931) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3542027393 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 10714019357) ^ 2615727 = 2829894311 := by
        calc
          (2 : ZMod 10714019357) ^ 2615727 = (2 : ZMod 10714019357) ^ (1307863 + 1307863 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 1307863 * (2 : ZMod 10714019357) ^ 1307863) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 2829894311 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 10714019357) ^ 5231454 = 2869318733 := by
        calc
          (2 : ZMod 10714019357) ^ 5231454 = (2 : ZMod 10714019357) ^ (2615727 + 2615727) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 2615727 * (2 : ZMod 10714019357) ^ 2615727 := by rw [pow_add]
          _ = 2869318733 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 10714019357) ^ 10462909 = 9176282150 := by
        calc
          (2 : ZMod 10714019357) ^ 10462909 = (2 : ZMod 10714019357) ^ (5231454 + 5231454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 5231454 * (2 : ZMod 10714019357) ^ 5231454) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 9176282150 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 10714019357) ^ 20925819 = 8257920218 := by
        calc
          (2 : ZMod 10714019357) ^ 20925819 = (2 : ZMod 10714019357) ^ (10462909 + 10462909 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 10462909 * (2 : ZMod 10714019357) ^ 10462909) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8257920218 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 10714019357) ^ 41851638 = 440512627 := by
        calc
          (2 : ZMod 10714019357) ^ 41851638 = (2 : ZMod 10714019357) ^ (20925819 + 20925819) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 20925819 * (2 : ZMod 10714019357) ^ 20925819 := by rw [pow_add]
          _ = 440512627 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 10714019357) ^ 83703276 = 9500179902 := by
        calc
          (2 : ZMod 10714019357) ^ 83703276 = (2 : ZMod 10714019357) ^ (41851638 + 41851638) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 41851638 * (2 : ZMod 10714019357) ^ 41851638 := by rw [pow_add]
          _ = 9500179902 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 10714019357) ^ 167406552 = 9466273501 := by
        calc
          (2 : ZMod 10714019357) ^ 167406552 = (2 : ZMod 10714019357) ^ (83703276 + 83703276) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 83703276 * (2 : ZMod 10714019357) ^ 83703276 := by rw [pow_add]
          _ = 9466273501 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 10714019357) ^ 334813104 = 929377015 := by
        calc
          (2 : ZMod 10714019357) ^ 334813104 = (2 : ZMod 10714019357) ^ (167406552 + 167406552) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 167406552 * (2 : ZMod 10714019357) ^ 167406552 := by rw [pow_add]
          _ = 929377015 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 10714019357) ^ 669626209 = 4059626990 := by
        calc
          (2 : ZMod 10714019357) ^ 669626209 = (2 : ZMod 10714019357) ^ (334813104 + 334813104 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 334813104 * (2 : ZMod 10714019357) ^ 334813104) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 4059626990 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 10714019357) ^ 1339252419 = 5688354527 := by
        calc
          (2 : ZMod 10714019357) ^ 1339252419 = (2 : ZMod 10714019357) ^ (669626209 + 669626209 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 669626209 * (2 : ZMod 10714019357) ^ 669626209) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 5688354527 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 10714019357) ^ 2678504839 = 10051329659 := by
        calc
          (2 : ZMod 10714019357) ^ 2678504839 = (2 : ZMod 10714019357) ^ (1339252419 + 1339252419 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 1339252419 * (2 : ZMod 10714019357) ^ 1339252419) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 10051329659 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 10714019357) ^ 5357009678 = 10714019356 := by
        calc
          (2 : ZMod 10714019357) ^ 5357009678 = (2 : ZMod 10714019357) ^ (2678504839 + 2678504839) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 2678504839 * (2 : ZMod 10714019357) ^ 2678504839 := by rw [pow_add]
          _ = 10714019356 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 10714019357) ^ 10714019356 = 1 := by
        calc
          (2 : ZMod 10714019357) ^ 10714019356 = (2 : ZMod 10714019357) ^ (5357009678 + 5357009678) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 5357009678 * (2 : ZMod 10714019357) ^ 5357009678 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13687, 1), (195697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13687, 1), (195697, 1)] : List FactorBlock).map factorBlockValue).prod = 10714019357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 10714019357) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 10714019357) ^ 2 = 4 := by
        calc
          (2 : ZMod 10714019357) ^ 2 = (2 : ZMod 10714019357) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 1 * (2 : ZMod 10714019357) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 10714019357) ^ 4 = 16 := by
        calc
          (2 : ZMod 10714019357) ^ 4 = (2 : ZMod 10714019357) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 2 * (2 : ZMod 10714019357) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 10714019357) ^ 9 = 512 := by
        calc
          (2 : ZMod 10714019357) ^ 9 = (2 : ZMod 10714019357) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 4 * (2 : ZMod 10714019357) ^ 4) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 10714019357) ^ 19 = 524288 := by
        calc
          (2 : ZMod 10714019357) ^ 19 = (2 : ZMod 10714019357) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 9 * (2 : ZMod 10714019357) ^ 9) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 10714019357) ^ 39 = 3340826681 := by
        calc
          (2 : ZMod 10714019357) ^ 39 = (2 : ZMod 10714019357) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 19 * (2 : ZMod 10714019357) ^ 19) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3340826681 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 10714019357) ^ 79 = 2230534937 := by
        calc
          (2 : ZMod 10714019357) ^ 79 = (2 : ZMod 10714019357) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 39 * (2 : ZMod 10714019357) ^ 39) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 2230534937 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 10714019357) ^ 159 = 5719820461 := by
        calc
          (2 : ZMod 10714019357) ^ 159 = (2 : ZMod 10714019357) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 79 * (2 : ZMod 10714019357) ^ 79) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 5719820461 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 10714019357) ^ 319 = 3046137056 := by
        calc
          (2 : ZMod 10714019357) ^ 319 = (2 : ZMod 10714019357) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 159 * (2 : ZMod 10714019357) ^ 159) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3046137056 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 10714019357) ^ 638 = 5229907915 := by
        calc
          (2 : ZMod 10714019357) ^ 638 = (2 : ZMod 10714019357) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 319 * (2 : ZMod 10714019357) ^ 319 := by rw [pow_add]
          _ = 5229907915 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 10714019357) ^ 1277 = 166711850 := by
        calc
          (2 : ZMod 10714019357) ^ 1277 = (2 : ZMod 10714019357) ^ (638 + 638 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 638 * (2 : ZMod 10714019357) ^ 638) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 166711850 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 10714019357) ^ 2554 = 10449164366 := by
        calc
          (2 : ZMod 10714019357) ^ 2554 = (2 : ZMod 10714019357) ^ (1277 + 1277) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 1277 * (2 : ZMod 10714019357) ^ 1277 := by rw [pow_add]
          _ = 10449164366 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 10714019357) ^ 5108 = 10185059413 := by
        calc
          (2 : ZMod 10714019357) ^ 5108 = (2 : ZMod 10714019357) ^ (2554 + 2554) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 2554 * (2 : ZMod 10714019357) ^ 2554 := by rw [pow_add]
          _ = 10185059413 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 10714019357) ^ 10217 = 6653616754 := by
        calc
          (2 : ZMod 10714019357) ^ 10217 = (2 : ZMod 10714019357) ^ (5108 + 5108 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 5108 * (2 : ZMod 10714019357) ^ 5108) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 6653616754 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 10714019357) ^ 20435 = 5572612353 := by
        calc
          (2 : ZMod 10714019357) ^ 20435 = (2 : ZMod 10714019357) ^ (10217 + 10217 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 10217 * (2 : ZMod 10714019357) ^ 10217) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 5572612353 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 10714019357) ^ 40870 = 1921567777 := by
        calc
          (2 : ZMod 10714019357) ^ 40870 = (2 : ZMod 10714019357) ^ (20435 + 20435) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 20435 * (2 : ZMod 10714019357) ^ 20435 := by rw [pow_add]
          _ = 1921567777 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 10714019357) ^ 81741 = 6558132226 := by
        calc
          (2 : ZMod 10714019357) ^ 81741 = (2 : ZMod 10714019357) ^ (40870 + 40870 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 40870 * (2 : ZMod 10714019357) ^ 40870) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 6558132226 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 10714019357) ^ 163482 = 5609195262 := by
        calc
          (2 : ZMod 10714019357) ^ 163482 = (2 : ZMod 10714019357) ^ (81741 + 81741) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 81741 * (2 : ZMod 10714019357) ^ 81741 := by rw [pow_add]
          _ = 5609195262 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 10714019357) ^ 326965 = 8130254386 := by
        calc
          (2 : ZMod 10714019357) ^ 326965 = (2 : ZMod 10714019357) ^ (163482 + 163482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 163482 * (2 : ZMod 10714019357) ^ 163482) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8130254386 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 10714019357) ^ 653931 = 3427255260 := by
        calc
          (2 : ZMod 10714019357) ^ 653931 = (2 : ZMod 10714019357) ^ (326965 + 326965 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 326965 * (2 : ZMod 10714019357) ^ 326965) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3427255260 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 10714019357) ^ 1307863 = 3542027393 := by
        calc
          (2 : ZMod 10714019357) ^ 1307863 = (2 : ZMod 10714019357) ^ (653931 + 653931 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 653931 * (2 : ZMod 10714019357) ^ 653931) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3542027393 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 10714019357) ^ 2615727 = 2829894311 := by
        calc
          (2 : ZMod 10714019357) ^ 2615727 = (2 : ZMod 10714019357) ^ (1307863 + 1307863 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 1307863 * (2 : ZMod 10714019357) ^ 1307863) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 2829894311 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 10714019357) ^ 5231454 = 2869318733 := by
        calc
          (2 : ZMod 10714019357) ^ 5231454 = (2 : ZMod 10714019357) ^ (2615727 + 2615727) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 2615727 * (2 : ZMod 10714019357) ^ 2615727 := by rw [pow_add]
          _ = 2869318733 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 10714019357) ^ 10462909 = 9176282150 := by
        calc
          (2 : ZMod 10714019357) ^ 10462909 = (2 : ZMod 10714019357) ^ (5231454 + 5231454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 5231454 * (2 : ZMod 10714019357) ^ 5231454) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 9176282150 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 10714019357) ^ 20925819 = 8257920218 := by
        calc
          (2 : ZMod 10714019357) ^ 20925819 = (2 : ZMod 10714019357) ^ (10462909 + 10462909 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 10462909 * (2 : ZMod 10714019357) ^ 10462909) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8257920218 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 10714019357) ^ 41851638 = 440512627 := by
        calc
          (2 : ZMod 10714019357) ^ 41851638 = (2 : ZMod 10714019357) ^ (20925819 + 20925819) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 20925819 * (2 : ZMod 10714019357) ^ 20925819 := by rw [pow_add]
          _ = 440512627 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 10714019357) ^ 83703276 = 9500179902 := by
        calc
          (2 : ZMod 10714019357) ^ 83703276 = (2 : ZMod 10714019357) ^ (41851638 + 41851638) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 41851638 * (2 : ZMod 10714019357) ^ 41851638 := by rw [pow_add]
          _ = 9500179902 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 10714019357) ^ 167406552 = 9466273501 := by
        calc
          (2 : ZMod 10714019357) ^ 167406552 = (2 : ZMod 10714019357) ^ (83703276 + 83703276) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 83703276 * (2 : ZMod 10714019357) ^ 83703276 := by rw [pow_add]
          _ = 9466273501 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 10714019357) ^ 334813104 = 929377015 := by
        calc
          (2 : ZMod 10714019357) ^ 334813104 = (2 : ZMod 10714019357) ^ (167406552 + 167406552) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 167406552 * (2 : ZMod 10714019357) ^ 167406552 := by rw [pow_add]
          _ = 929377015 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 10714019357) ^ 669626209 = 4059626990 := by
        calc
          (2 : ZMod 10714019357) ^ 669626209 = (2 : ZMod 10714019357) ^ (334813104 + 334813104 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 334813104 * (2 : ZMod 10714019357) ^ 334813104) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 4059626990 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 10714019357) ^ 1339252419 = 5688354527 := by
        calc
          (2 : ZMod 10714019357) ^ 1339252419 = (2 : ZMod 10714019357) ^ (669626209 + 669626209 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 669626209 * (2 : ZMod 10714019357) ^ 669626209) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 5688354527 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 10714019357) ^ 2678504839 = 10051329659 := by
        calc
          (2 : ZMod 10714019357) ^ 2678504839 = (2 : ZMod 10714019357) ^ (1339252419 + 1339252419 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 1339252419 * (2 : ZMod 10714019357) ^ 1339252419) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 10051329659 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 10714019357) ^ 5357009678 = 10714019356 := by
        calc
          (2 : ZMod 10714019357) ^ 5357009678 = (2 : ZMod 10714019357) ^ (2678504839 + 2678504839) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 2678504839 * (2 : ZMod 10714019357) ^ 2678504839 := by rw [pow_add]
          _ = 10714019356 := by rw [factor_0_31]; decide
      change (2 : ZMod 10714019357) ^ 5357009678 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (2 : ZMod 10714019357) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 10714019357) ^ 2 = 4 := by
        calc
          (2 : ZMod 10714019357) ^ 2 = (2 : ZMod 10714019357) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 1 * (2 : ZMod 10714019357) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 10714019357) ^ 5 = 32 := by
        calc
          (2 : ZMod 10714019357) ^ 5 = (2 : ZMod 10714019357) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 2 * (2 : ZMod 10714019357) ^ 2) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 10714019357) ^ 11 = 2048 := by
        calc
          (2 : ZMod 10714019357) ^ 11 = (2 : ZMod 10714019357) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 5 * (2 : ZMod 10714019357) ^ 5) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 10714019357) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 10714019357) ^ 23 = (2 : ZMod 10714019357) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 11 * (2 : ZMod 10714019357) ^ 11) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 10714019357) ^ 47 = 8844101133 := by
        calc
          (2 : ZMod 10714019357) ^ 47 = (2 : ZMod 10714019357) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 23 * (2 : ZMod 10714019357) ^ 23) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8844101133 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 10714019357) ^ 95 = 8971543681 := by
        calc
          (2 : ZMod 10714019357) ^ 95 = (2 : ZMod 10714019357) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 47 * (2 : ZMod 10714019357) ^ 47) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8971543681 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 10714019357) ^ 191 = 2669257371 := by
        calc
          (2 : ZMod 10714019357) ^ 191 = (2 : ZMod 10714019357) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 95 * (2 : ZMod 10714019357) ^ 95) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 2669257371 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 10714019357) ^ 382 = 3732415492 := by
        calc
          (2 : ZMod 10714019357) ^ 382 = (2 : ZMod 10714019357) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 191 * (2 : ZMod 10714019357) ^ 191 := by rw [pow_add]
          _ = 3732415492 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 10714019357) ^ 764 = 7951096068 := by
        calc
          (2 : ZMod 10714019357) ^ 764 = (2 : ZMod 10714019357) ^ (382 + 382) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 382 * (2 : ZMod 10714019357) ^ 382 := by rw [pow_add]
          _ = 7951096068 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 10714019357) ^ 1528 = 9192695605 := by
        calc
          (2 : ZMod 10714019357) ^ 1528 = (2 : ZMod 10714019357) ^ (764 + 764) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 764 * (2 : ZMod 10714019357) ^ 764 := by rw [pow_add]
          _ = 9192695605 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 10714019357) ^ 3057 = 3694073925 := by
        calc
          (2 : ZMod 10714019357) ^ 3057 = (2 : ZMod 10714019357) ^ (1528 + 1528 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 1528 * (2 : ZMod 10714019357) ^ 1528) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3694073925 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 10714019357) ^ 6115 = 3567008202 := by
        calc
          (2 : ZMod 10714019357) ^ 6115 = (2 : ZMod 10714019357) ^ (3057 + 3057 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 3057 * (2 : ZMod 10714019357) ^ 3057) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 3567008202 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 10714019357) ^ 12231 = 10690567429 := by
        calc
          (2 : ZMod 10714019357) ^ 12231 = (2 : ZMod 10714019357) ^ (6115 + 6115 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 6115 * (2 : ZMod 10714019357) ^ 6115) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 10690567429 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 10714019357) ^ 24462 = 10171264303 := by
        calc
          (2 : ZMod 10714019357) ^ 24462 = (2 : ZMod 10714019357) ^ (12231 + 12231) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 12231 * (2 : ZMod 10714019357) ^ 12231 := by rw [pow_add]
          _ = 10171264303 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 10714019357) ^ 48924 = 4305872859 := by
        calc
          (2 : ZMod 10714019357) ^ 48924 = (2 : ZMod 10714019357) ^ (24462 + 24462) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 24462 * (2 : ZMod 10714019357) ^ 24462 := by rw [pow_add]
          _ = 4305872859 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 10714019357) ^ 97848 = 7429767241 := by
        calc
          (2 : ZMod 10714019357) ^ 97848 = (2 : ZMod 10714019357) ^ (48924 + 48924) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 48924 * (2 : ZMod 10714019357) ^ 48924 := by rw [pow_add]
          _ = 7429767241 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 10714019357) ^ 195697 = 10523130334 := by
        calc
          (2 : ZMod 10714019357) ^ 195697 = (2 : ZMod 10714019357) ^ (97848 + 97848 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 97848 * (2 : ZMod 10714019357) ^ 97848) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 10523130334 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 10714019357) ^ 391394 = 3560311675 := by
        calc
          (2 : ZMod 10714019357) ^ 391394 = (2 : ZMod 10714019357) ^ (195697 + 195697) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 195697 * (2 : ZMod 10714019357) ^ 195697 := by rw [pow_add]
          _ = 3560311675 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 10714019357) ^ 782788 = 9152941321 := by
        calc
          (2 : ZMod 10714019357) ^ 782788 = (2 : ZMod 10714019357) ^ (391394 + 391394) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 391394 * (2 : ZMod 10714019357) ^ 391394 := by rw [pow_add]
          _ = 9152941321 := by rw [factor_1_18]; decide
      change (2 : ZMod 10714019357) ^ 782788 ≠ 1
      rw [factor_1_19]
      decide
    ·
      have factor_2_0 : (2 : ZMod 10714019357) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 10714019357) ^ 3 = 8 := by
        calc
          (2 : ZMod 10714019357) ^ 3 = (2 : ZMod 10714019357) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 1 * (2 : ZMod 10714019357) ^ 1) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 10714019357) ^ 6 = 64 := by
        calc
          (2 : ZMod 10714019357) ^ 6 = (2 : ZMod 10714019357) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 3 * (2 : ZMod 10714019357) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 10714019357) ^ 13 = 8192 := by
        calc
          (2 : ZMod 10714019357) ^ 13 = (2 : ZMod 10714019357) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 6 * (2 : ZMod 10714019357) ^ 6) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 10714019357) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 10714019357) ^ 26 = (2 : ZMod 10714019357) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 13 * (2 : ZMod 10714019357) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 10714019357) ^ 53 = 8893465948 := by
        calc
          (2 : ZMod 10714019357) ^ 53 = (2 : ZMod 10714019357) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 26 * (2 : ZMod 10714019357) ^ 26) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8893465948 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 10714019357) ^ 106 = 9892280790 := by
        calc
          (2 : ZMod 10714019357) ^ 106 = (2 : ZMod 10714019357) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 53 * (2 : ZMod 10714019357) ^ 53 := by rw [pow_add]
          _ = 9892280790 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 10714019357) ^ 213 = 8771020849 := by
        calc
          (2 : ZMod 10714019357) ^ 213 = (2 : ZMod 10714019357) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 106 * (2 : ZMod 10714019357) ^ 106) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 8771020849 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 10714019357) ^ 427 = 10467913997 := by
        calc
          (2 : ZMod 10714019357) ^ 427 = (2 : ZMod 10714019357) ^ (213 + 213 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 213 * (2 : ZMod 10714019357) ^ 213) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 10467913997 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 10714019357) ^ 855 = 4379816597 := by
        calc
          (2 : ZMod 10714019357) ^ 855 = (2 : ZMod 10714019357) ^ (427 + 427 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 427 * (2 : ZMod 10714019357) ^ 427) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 4379816597 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 10714019357) ^ 1710 = 1855396418 := by
        calc
          (2 : ZMod 10714019357) ^ 1710 = (2 : ZMod 10714019357) ^ (855 + 855) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 855 * (2 : ZMod 10714019357) ^ 855 := by rw [pow_add]
          _ = 1855396418 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 10714019357) ^ 3421 = 1095957620 := by
        calc
          (2 : ZMod 10714019357) ^ 3421 = (2 : ZMod 10714019357) ^ (1710 + 1710 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 1710 * (2 : ZMod 10714019357) ^ 1710) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 1095957620 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 10714019357) ^ 6843 = 2458115260 := by
        calc
          (2 : ZMod 10714019357) ^ 6843 = (2 : ZMod 10714019357) ^ (3421 + 3421 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 3421 * (2 : ZMod 10714019357) ^ 3421) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 2458115260 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 10714019357) ^ 13687 = 2341409594 := by
        calc
          (2 : ZMod 10714019357) ^ 13687 = (2 : ZMod 10714019357) ^ (6843 + 6843 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = ((2 : ZMod 10714019357) ^ 6843 * (2 : ZMod 10714019357) ^ 6843) * (2 : ZMod 10714019357) := by rw [pow_succ, pow_add]
          _ = 2341409594 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 10714019357) ^ 27374 = 6372132924 := by
        calc
          (2 : ZMod 10714019357) ^ 27374 = (2 : ZMod 10714019357) ^ (13687 + 13687) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 13687 * (2 : ZMod 10714019357) ^ 13687 := by rw [pow_add]
          _ = 6372132924 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 10714019357) ^ 54748 = 4854217299 := by
        calc
          (2 : ZMod 10714019357) ^ 54748 = (2 : ZMod 10714019357) ^ (27374 + 27374) :=
            congrArg (fun n : ℕ => (2 : ZMod 10714019357) ^ n) (by norm_num)
          _ = (2 : ZMod 10714019357) ^ 27374 * (2 : ZMod 10714019357) ^ 27374 := by rw [pow_add]
          _ = 4854217299 := by rw [factor_2_14]; decide
      change (2 : ZMod 10714019357) ^ 54748 ≠ 1
      rw [factor_2_15]
      decide

#print axioms prime_lucas_10714019357

end TotientTailPeriodKiller
end Erdos249257
