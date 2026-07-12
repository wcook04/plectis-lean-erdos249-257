import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2374507397 : Nat.Prime 2374507397 := by
  apply lucas_primality 2374507397 (3 : ZMod 2374507397)
  ·
      have fermat_0 : (3 : ZMod 2374507397) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 2374507397) ^ 2 = 9 := by
        calc
          (3 : ZMod 2374507397) ^ 2 = (3 : ZMod 2374507397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1 * (3 : ZMod 2374507397) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 2374507397) ^ 4 = 81 := by
        calc
          (3 : ZMod 2374507397) ^ 4 = (3 : ZMod 2374507397) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 2 * (3 : ZMod 2374507397) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 2374507397) ^ 8 = 6561 := by
        calc
          (3 : ZMod 2374507397) ^ 8 = (3 : ZMod 2374507397) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 4 * (3 : ZMod 2374507397) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 2374507397) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 2374507397) ^ 17 = (3 : ZMod 2374507397) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 8 * (3 : ZMod 2374507397) ^ 8) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 2374507397) ^ 35 = 2258616356 := by
        calc
          (3 : ZMod 2374507397) ^ 35 = (3 : ZMod 2374507397) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 17 * (3 : ZMod 2374507397) ^ 17) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 2258616356 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 2374507397) ^ 70 = 1904019135 := by
        calc
          (3 : ZMod 2374507397) ^ 70 = (3 : ZMod 2374507397) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 35 * (3 : ZMod 2374507397) ^ 35 := by rw [pow_add]
          _ = 1904019135 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 2374507397) ^ 141 = 1764566631 := by
        calc
          (3 : ZMod 2374507397) ^ 141 = (3 : ZMod 2374507397) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 70 * (3 : ZMod 2374507397) ^ 70) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1764566631 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 2374507397) ^ 283 = 1300835857 := by
        calc
          (3 : ZMod 2374507397) ^ 283 = (3 : ZMod 2374507397) ^ (141 + 141 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 141 * (3 : ZMod 2374507397) ^ 141) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1300835857 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 2374507397) ^ 566 = 865847734 := by
        calc
          (3 : ZMod 2374507397) ^ 566 = (3 : ZMod 2374507397) ^ (283 + 283) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 283 * (3 : ZMod 2374507397) ^ 283 := by rw [pow_add]
          _ = 865847734 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 2374507397) ^ 1132 = 752150956 := by
        calc
          (3 : ZMod 2374507397) ^ 1132 = (3 : ZMod 2374507397) ^ (566 + 566) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 566 * (3 : ZMod 2374507397) ^ 566 := by rw [pow_add]
          _ = 752150956 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 2374507397) ^ 2264 = 245906640 := by
        calc
          (3 : ZMod 2374507397) ^ 2264 = (3 : ZMod 2374507397) ^ (1132 + 1132) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1132 * (3 : ZMod 2374507397) ^ 1132 := by rw [pow_add]
          _ = 245906640 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 2374507397) ^ 4529 = 1088633497 := by
        calc
          (3 : ZMod 2374507397) ^ 4529 = (3 : ZMod 2374507397) ^ (2264 + 2264 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 2264 * (3 : ZMod 2374507397) ^ 2264) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1088633497 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 2374507397) ^ 9058 = 1618787502 := by
        calc
          (3 : ZMod 2374507397) ^ 9058 = (3 : ZMod 2374507397) ^ (4529 + 4529) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 4529 * (3 : ZMod 2374507397) ^ 4529 := by rw [pow_add]
          _ = 1618787502 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 2374507397) ^ 18116 = 1250709221 := by
        calc
          (3 : ZMod 2374507397) ^ 18116 = (3 : ZMod 2374507397) ^ (9058 + 9058) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 9058 * (3 : ZMod 2374507397) ^ 9058 := by rw [pow_add]
          _ = 1250709221 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 2374507397) ^ 36232 = 955062246 := by
        calc
          (3 : ZMod 2374507397) ^ 36232 = (3 : ZMod 2374507397) ^ (18116 + 18116) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 18116 * (3 : ZMod 2374507397) ^ 18116 := by rw [pow_add]
          _ = 955062246 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 2374507397) ^ 72464 = 130046502 := by
        calc
          (3 : ZMod 2374507397) ^ 72464 = (3 : ZMod 2374507397) ^ (36232 + 36232) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 36232 * (3 : ZMod 2374507397) ^ 36232 := by rw [pow_add]
          _ = 130046502 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 2374507397) ^ 144928 = 927353878 := by
        calc
          (3 : ZMod 2374507397) ^ 144928 = (3 : ZMod 2374507397) ^ (72464 + 72464) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 72464 * (3 : ZMod 2374507397) ^ 72464 := by rw [pow_add]
          _ = 927353878 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 2374507397) ^ 289856 = 242899555 := by
        calc
          (3 : ZMod 2374507397) ^ 289856 = (3 : ZMod 2374507397) ^ (144928 + 144928) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 144928 * (3 : ZMod 2374507397) ^ 144928 := by rw [pow_add]
          _ = 242899555 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 2374507397) ^ 579713 = 1205764738 := by
        calc
          (3 : ZMod 2374507397) ^ 579713 = (3 : ZMod 2374507397) ^ (289856 + 289856 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 289856 * (3 : ZMod 2374507397) ^ 289856) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1205764738 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 2374507397) ^ 1159427 = 2226921893 := by
        calc
          (3 : ZMod 2374507397) ^ 1159427 = (3 : ZMod 2374507397) ^ (579713 + 579713 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 579713 * (3 : ZMod 2374507397) ^ 579713) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 2226921893 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 2374507397) ^ 2318854 = 1163868372 := by
        calc
          (3 : ZMod 2374507397) ^ 2318854 = (3 : ZMod 2374507397) ^ (1159427 + 1159427) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1159427 * (3 : ZMod 2374507397) ^ 1159427 := by rw [pow_add]
          _ = 1163868372 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 2374507397) ^ 4637709 = 309845049 := by
        calc
          (3 : ZMod 2374507397) ^ 4637709 = (3 : ZMod 2374507397) ^ (2318854 + 2318854 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 2318854 * (3 : ZMod 2374507397) ^ 2318854) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 309845049 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 2374507397) ^ 9275419 = 1367823133 := by
        calc
          (3 : ZMod 2374507397) ^ 9275419 = (3 : ZMod 2374507397) ^ (4637709 + 4637709 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 4637709 * (3 : ZMod 2374507397) ^ 4637709) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1367823133 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 2374507397) ^ 18550839 = 1512990056 := by
        calc
          (3 : ZMod 2374507397) ^ 18550839 = (3 : ZMod 2374507397) ^ (9275419 + 9275419 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 9275419 * (3 : ZMod 2374507397) ^ 9275419) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1512990056 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 2374507397) ^ 37101678 = 1950448484 := by
        calc
          (3 : ZMod 2374507397) ^ 37101678 = (3 : ZMod 2374507397) ^ (18550839 + 18550839) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 18550839 * (3 : ZMod 2374507397) ^ 18550839 := by rw [pow_add]
          _ = 1950448484 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 2374507397) ^ 74203356 = 206862475 := by
        calc
          (3 : ZMod 2374507397) ^ 74203356 = (3 : ZMod 2374507397) ^ (37101678 + 37101678) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 37101678 * (3 : ZMod 2374507397) ^ 37101678 := by rw [pow_add]
          _ = 206862475 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 2374507397) ^ 148406712 = 611908196 := by
        calc
          (3 : ZMod 2374507397) ^ 148406712 = (3 : ZMod 2374507397) ^ (74203356 + 74203356) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 74203356 * (3 : ZMod 2374507397) ^ 74203356 := by rw [pow_add]
          _ = 611908196 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 2374507397) ^ 296813424 = 2104354615 := by
        calc
          (3 : ZMod 2374507397) ^ 296813424 = (3 : ZMod 2374507397) ^ (148406712 + 148406712) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 148406712 * (3 : ZMod 2374507397) ^ 148406712 := by rw [pow_add]
          _ = 2104354615 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 2374507397) ^ 593626849 = 846564106 := by
        calc
          (3 : ZMod 2374507397) ^ 593626849 = (3 : ZMod 2374507397) ^ (296813424 + 296813424 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 296813424 * (3 : ZMod 2374507397) ^ 296813424) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 846564106 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 2374507397) ^ 1187253698 = 2374507396 := by
        calc
          (3 : ZMod 2374507397) ^ 1187253698 = (3 : ZMod 2374507397) ^ (593626849 + 593626849) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 593626849 * (3 : ZMod 2374507397) ^ 593626849 := by rw [pow_add]
          _ = 2374507396 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 2374507397) ^ 2374507396 = 1 := by
        calc
          (3 : ZMod 2374507397) ^ 2374507396 = (3 : ZMod 2374507397) ^ (1187253698 + 1187253698) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1187253698 * (3 : ZMod 2374507397) ^ 1187253698 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (23, 1), (509, 1), (50707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (23, 1), (509, 1), (50707, 1)] : List FactorBlock).map factorBlockValue).prod = 2374507397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 2374507397) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 2374507397) ^ 2 = 9 := by
        calc
          (3 : ZMod 2374507397) ^ 2 = (3 : ZMod 2374507397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1 * (3 : ZMod 2374507397) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 2374507397) ^ 4 = 81 := by
        calc
          (3 : ZMod 2374507397) ^ 4 = (3 : ZMod 2374507397) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 2 * (3 : ZMod 2374507397) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 2374507397) ^ 8 = 6561 := by
        calc
          (3 : ZMod 2374507397) ^ 8 = (3 : ZMod 2374507397) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 4 * (3 : ZMod 2374507397) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 2374507397) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 2374507397) ^ 17 = (3 : ZMod 2374507397) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 8 * (3 : ZMod 2374507397) ^ 8) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 2374507397) ^ 35 = 2258616356 := by
        calc
          (3 : ZMod 2374507397) ^ 35 = (3 : ZMod 2374507397) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 17 * (3 : ZMod 2374507397) ^ 17) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 2258616356 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 2374507397) ^ 70 = 1904019135 := by
        calc
          (3 : ZMod 2374507397) ^ 70 = (3 : ZMod 2374507397) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 35 * (3 : ZMod 2374507397) ^ 35 := by rw [pow_add]
          _ = 1904019135 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 2374507397) ^ 141 = 1764566631 := by
        calc
          (3 : ZMod 2374507397) ^ 141 = (3 : ZMod 2374507397) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 70 * (3 : ZMod 2374507397) ^ 70) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1764566631 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 2374507397) ^ 283 = 1300835857 := by
        calc
          (3 : ZMod 2374507397) ^ 283 = (3 : ZMod 2374507397) ^ (141 + 141 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 141 * (3 : ZMod 2374507397) ^ 141) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1300835857 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 2374507397) ^ 566 = 865847734 := by
        calc
          (3 : ZMod 2374507397) ^ 566 = (3 : ZMod 2374507397) ^ (283 + 283) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 283 * (3 : ZMod 2374507397) ^ 283 := by rw [pow_add]
          _ = 865847734 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 2374507397) ^ 1132 = 752150956 := by
        calc
          (3 : ZMod 2374507397) ^ 1132 = (3 : ZMod 2374507397) ^ (566 + 566) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 566 * (3 : ZMod 2374507397) ^ 566 := by rw [pow_add]
          _ = 752150956 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 2374507397) ^ 2264 = 245906640 := by
        calc
          (3 : ZMod 2374507397) ^ 2264 = (3 : ZMod 2374507397) ^ (1132 + 1132) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1132 * (3 : ZMod 2374507397) ^ 1132 := by rw [pow_add]
          _ = 245906640 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 2374507397) ^ 4529 = 1088633497 := by
        calc
          (3 : ZMod 2374507397) ^ 4529 = (3 : ZMod 2374507397) ^ (2264 + 2264 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 2264 * (3 : ZMod 2374507397) ^ 2264) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1088633497 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 2374507397) ^ 9058 = 1618787502 := by
        calc
          (3 : ZMod 2374507397) ^ 9058 = (3 : ZMod 2374507397) ^ (4529 + 4529) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 4529 * (3 : ZMod 2374507397) ^ 4529 := by rw [pow_add]
          _ = 1618787502 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 2374507397) ^ 18116 = 1250709221 := by
        calc
          (3 : ZMod 2374507397) ^ 18116 = (3 : ZMod 2374507397) ^ (9058 + 9058) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 9058 * (3 : ZMod 2374507397) ^ 9058 := by rw [pow_add]
          _ = 1250709221 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 2374507397) ^ 36232 = 955062246 := by
        calc
          (3 : ZMod 2374507397) ^ 36232 = (3 : ZMod 2374507397) ^ (18116 + 18116) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 18116 * (3 : ZMod 2374507397) ^ 18116 := by rw [pow_add]
          _ = 955062246 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 2374507397) ^ 72464 = 130046502 := by
        calc
          (3 : ZMod 2374507397) ^ 72464 = (3 : ZMod 2374507397) ^ (36232 + 36232) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 36232 * (3 : ZMod 2374507397) ^ 36232 := by rw [pow_add]
          _ = 130046502 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 2374507397) ^ 144928 = 927353878 := by
        calc
          (3 : ZMod 2374507397) ^ 144928 = (3 : ZMod 2374507397) ^ (72464 + 72464) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 72464 * (3 : ZMod 2374507397) ^ 72464 := by rw [pow_add]
          _ = 927353878 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 2374507397) ^ 289856 = 242899555 := by
        calc
          (3 : ZMod 2374507397) ^ 289856 = (3 : ZMod 2374507397) ^ (144928 + 144928) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 144928 * (3 : ZMod 2374507397) ^ 144928 := by rw [pow_add]
          _ = 242899555 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 2374507397) ^ 579713 = 1205764738 := by
        calc
          (3 : ZMod 2374507397) ^ 579713 = (3 : ZMod 2374507397) ^ (289856 + 289856 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 289856 * (3 : ZMod 2374507397) ^ 289856) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1205764738 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 2374507397) ^ 1159427 = 2226921893 := by
        calc
          (3 : ZMod 2374507397) ^ 1159427 = (3 : ZMod 2374507397) ^ (579713 + 579713 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 579713 * (3 : ZMod 2374507397) ^ 579713) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 2226921893 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 2374507397) ^ 2318854 = 1163868372 := by
        calc
          (3 : ZMod 2374507397) ^ 2318854 = (3 : ZMod 2374507397) ^ (1159427 + 1159427) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1159427 * (3 : ZMod 2374507397) ^ 1159427 := by rw [pow_add]
          _ = 1163868372 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 2374507397) ^ 4637709 = 309845049 := by
        calc
          (3 : ZMod 2374507397) ^ 4637709 = (3 : ZMod 2374507397) ^ (2318854 + 2318854 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 2318854 * (3 : ZMod 2374507397) ^ 2318854) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 309845049 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 2374507397) ^ 9275419 = 1367823133 := by
        calc
          (3 : ZMod 2374507397) ^ 9275419 = (3 : ZMod 2374507397) ^ (4637709 + 4637709 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 4637709 * (3 : ZMod 2374507397) ^ 4637709) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1367823133 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 2374507397) ^ 18550839 = 1512990056 := by
        calc
          (3 : ZMod 2374507397) ^ 18550839 = (3 : ZMod 2374507397) ^ (9275419 + 9275419 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 9275419 * (3 : ZMod 2374507397) ^ 9275419) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1512990056 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 2374507397) ^ 37101678 = 1950448484 := by
        calc
          (3 : ZMod 2374507397) ^ 37101678 = (3 : ZMod 2374507397) ^ (18550839 + 18550839) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 18550839 * (3 : ZMod 2374507397) ^ 18550839 := by rw [pow_add]
          _ = 1950448484 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 2374507397) ^ 74203356 = 206862475 := by
        calc
          (3 : ZMod 2374507397) ^ 74203356 = (3 : ZMod 2374507397) ^ (37101678 + 37101678) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 37101678 * (3 : ZMod 2374507397) ^ 37101678 := by rw [pow_add]
          _ = 206862475 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 2374507397) ^ 148406712 = 611908196 := by
        calc
          (3 : ZMod 2374507397) ^ 148406712 = (3 : ZMod 2374507397) ^ (74203356 + 74203356) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 74203356 * (3 : ZMod 2374507397) ^ 74203356 := by rw [pow_add]
          _ = 611908196 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 2374507397) ^ 296813424 = 2104354615 := by
        calc
          (3 : ZMod 2374507397) ^ 296813424 = (3 : ZMod 2374507397) ^ (148406712 + 148406712) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 148406712 * (3 : ZMod 2374507397) ^ 148406712 := by rw [pow_add]
          _ = 2104354615 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 2374507397) ^ 593626849 = 846564106 := by
        calc
          (3 : ZMod 2374507397) ^ 593626849 = (3 : ZMod 2374507397) ^ (296813424 + 296813424 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 296813424 * (3 : ZMod 2374507397) ^ 296813424) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 846564106 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 2374507397) ^ 1187253698 = 2374507396 := by
        calc
          (3 : ZMod 2374507397) ^ 1187253698 = (3 : ZMod 2374507397) ^ (593626849 + 593626849) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 593626849 * (3 : ZMod 2374507397) ^ 593626849 := by rw [pow_add]
          _ = 2374507396 := by rw [factor_0_29]; decide
      change (3 : ZMod 2374507397) ^ 1187253698 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (3 : ZMod 2374507397) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 2374507397) ^ 3 = 27 := by
        calc
          (3 : ZMod 2374507397) ^ 3 = (3 : ZMod 2374507397) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 1 * (3 : ZMod 2374507397) ^ 1) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 2374507397) ^ 6 = 729 := by
        calc
          (3 : ZMod 2374507397) ^ 6 = (3 : ZMod 2374507397) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 3 * (3 : ZMod 2374507397) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 2374507397) ^ 12 = 531441 := by
        calc
          (3 : ZMod 2374507397) ^ 12 = (3 : ZMod 2374507397) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 6 * (3 : ZMod 2374507397) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 2374507397) ^ 24 = 2237663635 := by
        calc
          (3 : ZMod 2374507397) ^ 24 = (3 : ZMod 2374507397) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 12 * (3 : ZMod 2374507397) ^ 12 := by rw [pow_add]
          _ = 2237663635 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 2374507397) ^ 49 = 1750274951 := by
        calc
          (3 : ZMod 2374507397) ^ 49 = (3 : ZMod 2374507397) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 24 * (3 : ZMod 2374507397) ^ 24) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1750274951 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 2374507397) ^ 98 = 1383406695 := by
        calc
          (3 : ZMod 2374507397) ^ 98 = (3 : ZMod 2374507397) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 49 * (3 : ZMod 2374507397) ^ 49 := by rw [pow_add]
          _ = 1383406695 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 2374507397) ^ 196 = 1972941503 := by
        calc
          (3 : ZMod 2374507397) ^ 196 = (3 : ZMod 2374507397) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 98 * (3 : ZMod 2374507397) ^ 98 := by rw [pow_add]
          _ = 1972941503 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 2374507397) ^ 393 = 406101090 := by
        calc
          (3 : ZMod 2374507397) ^ 393 = (3 : ZMod 2374507397) ^ (196 + 196 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 196 * (3 : ZMod 2374507397) ^ 196) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 406101090 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 2374507397) ^ 787 = 1307652730 := by
        calc
          (3 : ZMod 2374507397) ^ 787 = (3 : ZMod 2374507397) ^ (393 + 393 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 393 * (3 : ZMod 2374507397) ^ 393) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1307652730 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 2374507397) ^ 1575 = 576605955 := by
        calc
          (3 : ZMod 2374507397) ^ 1575 = (3 : ZMod 2374507397) ^ (787 + 787 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 787 * (3 : ZMod 2374507397) ^ 787) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 576605955 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 2374507397) ^ 3150 = 13289247 := by
        calc
          (3 : ZMod 2374507397) ^ 3150 = (3 : ZMod 2374507397) ^ (1575 + 1575) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1575 * (3 : ZMod 2374507397) ^ 1575 := by rw [pow_add]
          _ = 13289247 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 2374507397) ^ 6301 = 294525402 := by
        calc
          (3 : ZMod 2374507397) ^ 6301 = (3 : ZMod 2374507397) ^ (3150 + 3150 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 3150 * (3 : ZMod 2374507397) ^ 3150) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 294525402 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 2374507397) ^ 12602 = 260467435 := by
        calc
          (3 : ZMod 2374507397) ^ 12602 = (3 : ZMod 2374507397) ^ (6301 + 6301) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 6301 * (3 : ZMod 2374507397) ^ 6301 := by rw [pow_add]
          _ = 260467435 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 2374507397) ^ 25204 = 1486453182 := by
        calc
          (3 : ZMod 2374507397) ^ 25204 = (3 : ZMod 2374507397) ^ (12602 + 12602) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 12602 * (3 : ZMod 2374507397) ^ 12602 := by rw [pow_add]
          _ = 1486453182 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 2374507397) ^ 50409 = 1520327079 := by
        calc
          (3 : ZMod 2374507397) ^ 50409 = (3 : ZMod 2374507397) ^ (25204 + 25204 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 25204 * (3 : ZMod 2374507397) ^ 25204) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1520327079 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 2374507397) ^ 100819 = 527871168 := by
        calc
          (3 : ZMod 2374507397) ^ 100819 = (3 : ZMod 2374507397) ^ (50409 + 50409 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 50409 * (3 : ZMod 2374507397) ^ 50409) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 527871168 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 2374507397) ^ 201639 = 858626078 := by
        calc
          (3 : ZMod 2374507397) ^ 201639 = (3 : ZMod 2374507397) ^ (100819 + 100819 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 100819 * (3 : ZMod 2374507397) ^ 100819) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 858626078 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 2374507397) ^ 403279 = 277058039 := by
        calc
          (3 : ZMod 2374507397) ^ 403279 = (3 : ZMod 2374507397) ^ (201639 + 201639 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 201639 * (3 : ZMod 2374507397) ^ 201639) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 277058039 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 2374507397) ^ 806558 = 446286297 := by
        calc
          (3 : ZMod 2374507397) ^ 806558 = (3 : ZMod 2374507397) ^ (403279 + 403279) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 403279 * (3 : ZMod 2374507397) ^ 403279 := by rw [pow_add]
          _ = 446286297 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 2374507397) ^ 1613116 = 968535801 := by
        calc
          (3 : ZMod 2374507397) ^ 1613116 = (3 : ZMod 2374507397) ^ (806558 + 806558) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 806558 * (3 : ZMod 2374507397) ^ 806558 := by rw [pow_add]
          _ = 968535801 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 2374507397) ^ 3226232 = 1091579130 := by
        calc
          (3 : ZMod 2374507397) ^ 3226232 = (3 : ZMod 2374507397) ^ (1613116 + 1613116) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1613116 * (3 : ZMod 2374507397) ^ 1613116 := by rw [pow_add]
          _ = 1091579130 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 2374507397) ^ 6452465 = 406267036 := by
        calc
          (3 : ZMod 2374507397) ^ 6452465 = (3 : ZMod 2374507397) ^ (3226232 + 3226232 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 3226232 * (3 : ZMod 2374507397) ^ 3226232) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 406267036 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 2374507397) ^ 12904931 = 556399881 := by
        calc
          (3 : ZMod 2374507397) ^ 12904931 = (3 : ZMod 2374507397) ^ (6452465 + 6452465 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 6452465 * (3 : ZMod 2374507397) ^ 6452465) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 556399881 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 2374507397) ^ 25809863 = 1207960856 := by
        calc
          (3 : ZMod 2374507397) ^ 25809863 = (3 : ZMod 2374507397) ^ (12904931 + 12904931 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 12904931 * (3 : ZMod 2374507397) ^ 12904931) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1207960856 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 2374507397) ^ 51619726 = 1981367491 := by
        calc
          (3 : ZMod 2374507397) ^ 51619726 = (3 : ZMod 2374507397) ^ (25809863 + 25809863) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 25809863 * (3 : ZMod 2374507397) ^ 25809863 := by rw [pow_add]
          _ = 1981367491 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 2374507397) ^ 103239452 = 695798540 := by
        calc
          (3 : ZMod 2374507397) ^ 103239452 = (3 : ZMod 2374507397) ^ (51619726 + 51619726) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 51619726 * (3 : ZMod 2374507397) ^ 51619726 := by rw [pow_add]
          _ = 695798540 := by rw [factor_1_25]; decide
      change (3 : ZMod 2374507397) ^ 103239452 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (3 : ZMod 2374507397) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 2374507397) ^ 2 = 9 := by
        calc
          (3 : ZMod 2374507397) ^ 2 = (3 : ZMod 2374507397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1 * (3 : ZMod 2374507397) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 2374507397) ^ 4 = 81 := by
        calc
          (3 : ZMod 2374507397) ^ 4 = (3 : ZMod 2374507397) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 2 * (3 : ZMod 2374507397) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 2374507397) ^ 8 = 6561 := by
        calc
          (3 : ZMod 2374507397) ^ 8 = (3 : ZMod 2374507397) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 4 * (3 : ZMod 2374507397) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 2374507397) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 2374507397) ^ 17 = (3 : ZMod 2374507397) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 8 * (3 : ZMod 2374507397) ^ 8) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 2374507397) ^ 35 = 2258616356 := by
        calc
          (3 : ZMod 2374507397) ^ 35 = (3 : ZMod 2374507397) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 17 * (3 : ZMod 2374507397) ^ 17) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 2258616356 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 2374507397) ^ 71 = 963042611 := by
        calc
          (3 : ZMod 2374507397) ^ 71 = (3 : ZMod 2374507397) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 35 * (3 : ZMod 2374507397) ^ 35) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 963042611 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 2374507397) ^ 142 = 544685099 := by
        calc
          (3 : ZMod 2374507397) ^ 142 = (3 : ZMod 2374507397) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 71 * (3 : ZMod 2374507397) ^ 71 := by rw [pow_add]
          _ = 544685099 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 2374507397) ^ 284 = 1528000174 := by
        calc
          (3 : ZMod 2374507397) ^ 284 = (3 : ZMod 2374507397) ^ (142 + 142) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 142 * (3 : ZMod 2374507397) ^ 142 := by rw [pow_add]
          _ = 1528000174 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 2374507397) ^ 569 = 2007322245 := by
        calc
          (3 : ZMod 2374507397) ^ 569 = (3 : ZMod 2374507397) ^ (284 + 284 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 284 * (3 : ZMod 2374507397) ^ 284) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 2007322245 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 2374507397) ^ 1138 = 2181345614 := by
        calc
          (3 : ZMod 2374507397) ^ 1138 = (3 : ZMod 2374507397) ^ (569 + 569) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 569 * (3 : ZMod 2374507397) ^ 569 := by rw [pow_add]
          _ = 2181345614 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 2374507397) ^ 2277 = 2070193447 := by
        calc
          (3 : ZMod 2374507397) ^ 2277 = (3 : ZMod 2374507397) ^ (1138 + 1138 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 1138 * (3 : ZMod 2374507397) ^ 1138) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 2070193447 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 2374507397) ^ 4555 = 1411175015 := by
        calc
          (3 : ZMod 2374507397) ^ 4555 = (3 : ZMod 2374507397) ^ (2277 + 2277 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 2277 * (3 : ZMod 2374507397) ^ 2277) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1411175015 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 2374507397) ^ 9111 = 742103459 := by
        calc
          (3 : ZMod 2374507397) ^ 9111 = (3 : ZMod 2374507397) ^ (4555 + 4555 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 4555 * (3 : ZMod 2374507397) ^ 4555) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 742103459 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 2374507397) ^ 18222 = 2242157206 := by
        calc
          (3 : ZMod 2374507397) ^ 18222 = (3 : ZMod 2374507397) ^ (9111 + 9111) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 9111 * (3 : ZMod 2374507397) ^ 9111 := by rw [pow_add]
          _ = 2242157206 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 2374507397) ^ 36445 = 1740278004 := by
        calc
          (3 : ZMod 2374507397) ^ 36445 = (3 : ZMod 2374507397) ^ (18222 + 18222 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 18222 * (3 : ZMod 2374507397) ^ 18222) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1740278004 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 2374507397) ^ 72891 = 1021864099 := by
        calc
          (3 : ZMod 2374507397) ^ 72891 = (3 : ZMod 2374507397) ^ (36445 + 36445 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 36445 * (3 : ZMod 2374507397) ^ 36445) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1021864099 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 2374507397) ^ 145782 = 1689597183 := by
        calc
          (3 : ZMod 2374507397) ^ 145782 = (3 : ZMod 2374507397) ^ (72891 + 72891) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 72891 * (3 : ZMod 2374507397) ^ 72891 := by rw [pow_add]
          _ = 1689597183 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 2374507397) ^ 291565 = 1510205657 := by
        calc
          (3 : ZMod 2374507397) ^ 291565 = (3 : ZMod 2374507397) ^ (145782 + 145782 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 145782 * (3 : ZMod 2374507397) ^ 145782) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1510205657 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 2374507397) ^ 583130 = 1895712802 := by
        calc
          (3 : ZMod 2374507397) ^ 583130 = (3 : ZMod 2374507397) ^ (291565 + 291565) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 291565 * (3 : ZMod 2374507397) ^ 291565 := by rw [pow_add]
          _ = 1895712802 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 2374507397) ^ 1166261 = 459902400 := by
        calc
          (3 : ZMod 2374507397) ^ 1166261 = (3 : ZMod 2374507397) ^ (583130 + 583130 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 583130 * (3 : ZMod 2374507397) ^ 583130) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 459902400 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 2374507397) ^ 2332522 = 2338967024 := by
        calc
          (3 : ZMod 2374507397) ^ 2332522 = (3 : ZMod 2374507397) ^ (1166261 + 1166261) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1166261 * (3 : ZMod 2374507397) ^ 1166261 := by rw [pow_add]
          _ = 2338967024 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 2374507397) ^ 4665044 = 1277652376 := by
        calc
          (3 : ZMod 2374507397) ^ 4665044 = (3 : ZMod 2374507397) ^ (2332522 + 2332522) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 2332522 * (3 : ZMod 2374507397) ^ 2332522 := by rw [pow_add]
          _ = 1277652376 := by rw [factor_2_21]; decide
      change (3 : ZMod 2374507397) ^ 4665044 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (3 : ZMod 2374507397) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 2374507397) ^ 2 = 9 := by
        calc
          (3 : ZMod 2374507397) ^ 2 = (3 : ZMod 2374507397) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1 * (3 : ZMod 2374507397) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 2374507397) ^ 5 = 243 := by
        calc
          (3 : ZMod 2374507397) ^ 5 = (3 : ZMod 2374507397) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 2 * (3 : ZMod 2374507397) ^ 2) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 2374507397) ^ 11 = 177147 := by
        calc
          (3 : ZMod 2374507397) ^ 11 = (3 : ZMod 2374507397) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 5 * (3 : ZMod 2374507397) ^ 5) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 2374507397) ^ 22 = 512463448 := by
        calc
          (3 : ZMod 2374507397) ^ 22 = (3 : ZMod 2374507397) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 11 * (3 : ZMod 2374507397) ^ 11 := by rw [pow_add]
          _ = 512463448 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 2374507397) ^ 45 = 80238145 := by
        calc
          (3 : ZMod 2374507397) ^ 45 = (3 : ZMod 2374507397) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 22 * (3 : ZMod 2374507397) ^ 22) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 80238145 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 2374507397) ^ 91 = 1495692772 := by
        calc
          (3 : ZMod 2374507397) ^ 91 = (3 : ZMod 2374507397) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 45 * (3 : ZMod 2374507397) ^ 45) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1495692772 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 2374507397) ^ 182 = 1236539980 := by
        calc
          (3 : ZMod 2374507397) ^ 182 = (3 : ZMod 2374507397) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 91 * (3 : ZMod 2374507397) ^ 91 := by rw [pow_add]
          _ = 1236539980 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 2374507397) ^ 365 = 159870239 := by
        calc
          (3 : ZMod 2374507397) ^ 365 = (3 : ZMod 2374507397) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 182 * (3 : ZMod 2374507397) ^ 182) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 159870239 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 2374507397) ^ 731 = 401410693 := by
        calc
          (3 : ZMod 2374507397) ^ 731 = (3 : ZMod 2374507397) ^ (365 + 365 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 365 * (3 : ZMod 2374507397) ^ 365) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 401410693 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 2374507397) ^ 1463 = 662429176 := by
        calc
          (3 : ZMod 2374507397) ^ 1463 = (3 : ZMod 2374507397) ^ (731 + 731 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 731 * (3 : ZMod 2374507397) ^ 731) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 662429176 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 2374507397) ^ 2926 = 840205929 := by
        calc
          (3 : ZMod 2374507397) ^ 2926 = (3 : ZMod 2374507397) ^ (1463 + 1463) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 1463 * (3 : ZMod 2374507397) ^ 1463 := by rw [pow_add]
          _ = 840205929 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 2374507397) ^ 5853 = 2328668697 := by
        calc
          (3 : ZMod 2374507397) ^ 5853 = (3 : ZMod 2374507397) ^ (2926 + 2926 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 2926 * (3 : ZMod 2374507397) ^ 2926) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 2328668697 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 2374507397) ^ 11707 = 1956402040 := by
        calc
          (3 : ZMod 2374507397) ^ 11707 = (3 : ZMod 2374507397) ^ (5853 + 5853 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = ((3 : ZMod 2374507397) ^ 5853 * (3 : ZMod 2374507397) ^ 5853) * (3 : ZMod 2374507397) := by rw [pow_succ, pow_add]
          _ = 1956402040 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 2374507397) ^ 23414 = 162294529 := by
        calc
          (3 : ZMod 2374507397) ^ 23414 = (3 : ZMod 2374507397) ^ (11707 + 11707) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 11707 * (3 : ZMod 2374507397) ^ 11707 := by rw [pow_add]
          _ = 162294529 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 2374507397) ^ 46828 = 1152206907 := by
        calc
          (3 : ZMod 2374507397) ^ 46828 = (3 : ZMod 2374507397) ^ (23414 + 23414) :=
            congrArg (fun n : ℕ => (3 : ZMod 2374507397) ^ n) (by norm_num)
          _ = (3 : ZMod 2374507397) ^ 23414 * (3 : ZMod 2374507397) ^ 23414 := by rw [pow_add]
          _ = 1152206907 := by rw [factor_3_14]; decide
      change (3 : ZMod 2374507397) ^ 46828 ≠ 1
      rw [factor_3_15]
      decide

#print axioms prime_lucas_2374507397

end TotientTailPeriodKiller
end Erdos249257
