import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_320796191 : Nat.Prime 320796191 := by
  apply lucas_primality 320796191 (7 : ZMod 320796191)
  ·
      have fermat_0 : (7 : ZMod 320796191) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 320796191) ^ 2 = 49 := by
        calc
          (7 : ZMod 320796191) ^ 2 = (7 : ZMod 320796191) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1 * (7 : ZMod 320796191) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 320796191) ^ 4 = 2401 := by
        calc
          (7 : ZMod 320796191) ^ 4 = (7 : ZMod 320796191) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2 * (7 : ZMod 320796191) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 320796191) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 320796191) ^ 9 = (7 : ZMod 320796191) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 4 * (7 : ZMod 320796191) ^ 4) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 320796191) ^ 19 = 181491976 := by
        calc
          (7 : ZMod 320796191) ^ 19 = (7 : ZMod 320796191) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 9 * (7 : ZMod 320796191) ^ 9) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 181491976 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 320796191) ^ 38 = 179517935 := by
        calc
          (7 : ZMod 320796191) ^ 38 = (7 : ZMod 320796191) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 19 * (7 : ZMod 320796191) ^ 19 := by rw [pow_add]
          _ = 179517935 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 320796191) ^ 76 = 231307893 := by
        calc
          (7 : ZMod 320796191) ^ 76 = (7 : ZMod 320796191) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 38 * (7 : ZMod 320796191) ^ 38 := by rw [pow_add]
          _ = 231307893 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 320796191) ^ 152 = 185228370 := by
        calc
          (7 : ZMod 320796191) ^ 152 = (7 : ZMod 320796191) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 76 * (7 : ZMod 320796191) ^ 76 := by rw [pow_add]
          _ = 185228370 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 320796191) ^ 305 = 90796150 := by
        calc
          (7 : ZMod 320796191) ^ 305 = (7 : ZMod 320796191) ^ (152 + 152 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 152 * (7 : ZMod 320796191) ^ 152) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 90796150 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 320796191) ^ 611 = 279530125 := by
        calc
          (7 : ZMod 320796191) ^ 611 = (7 : ZMod 320796191) ^ (305 + 305 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 305 * (7 : ZMod 320796191) ^ 305) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 279530125 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 320796191) ^ 1223 = 56697326 := by
        calc
          (7 : ZMod 320796191) ^ 1223 = (7 : ZMod 320796191) ^ (611 + 611 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 611 * (7 : ZMod 320796191) ^ 611) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 56697326 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 320796191) ^ 2447 = 82277163 := by
        calc
          (7 : ZMod 320796191) ^ 2447 = (7 : ZMod 320796191) ^ (1223 + 1223 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1223 * (7 : ZMod 320796191) ^ 1223) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 82277163 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 320796191) ^ 4894 = 185116898 := by
        calc
          (7 : ZMod 320796191) ^ 4894 = (7 : ZMod 320796191) ^ (2447 + 2447) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2447 * (7 : ZMod 320796191) ^ 2447 := by rw [pow_add]
          _ = 185116898 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 320796191) ^ 9789 = 67144635 := by
        calc
          (7 : ZMod 320796191) ^ 9789 = (7 : ZMod 320796191) ^ (4894 + 4894 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 4894 * (7 : ZMod 320796191) ^ 4894) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 67144635 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 320796191) ^ 19579 = 202758682 := by
        calc
          (7 : ZMod 320796191) ^ 19579 = (7 : ZMod 320796191) ^ (9789 + 9789 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 9789 * (7 : ZMod 320796191) ^ 9789) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 202758682 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 320796191) ^ 39159 = 4264519 := by
        calc
          (7 : ZMod 320796191) ^ 39159 = (7 : ZMod 320796191) ^ (19579 + 19579 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 19579 * (7 : ZMod 320796191) ^ 19579) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 4264519 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 320796191) ^ 78319 = 20450233 := by
        calc
          (7 : ZMod 320796191) ^ 78319 = (7 : ZMod 320796191) ^ (39159 + 39159 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 39159 * (7 : ZMod 320796191) ^ 39159) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 20450233 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 320796191) ^ 156638 = 301025701 := by
        calc
          (7 : ZMod 320796191) ^ 156638 = (7 : ZMod 320796191) ^ (78319 + 78319) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 78319 * (7 : ZMod 320796191) ^ 78319 := by rw [pow_add]
          _ = 301025701 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 320796191) ^ 313277 = 244056881 := by
        calc
          (7 : ZMod 320796191) ^ 313277 = (7 : ZMod 320796191) ^ (156638 + 156638 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 156638 * (7 : ZMod 320796191) ^ 156638) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 244056881 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 320796191) ^ 626555 = 201108660 := by
        calc
          (7 : ZMod 320796191) ^ 626555 = (7 : ZMod 320796191) ^ (313277 + 313277 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 313277 * (7 : ZMod 320796191) ^ 313277) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 201108660 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 320796191) ^ 1253110 = 249588184 := by
        calc
          (7 : ZMod 320796191) ^ 1253110 = (7 : ZMod 320796191) ^ (626555 + 626555) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 626555 * (7 : ZMod 320796191) ^ 626555 := by rw [pow_add]
          _ = 249588184 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 320796191) ^ 2506220 = 278861164 := by
        calc
          (7 : ZMod 320796191) ^ 2506220 = (7 : ZMod 320796191) ^ (1253110 + 1253110) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1253110 * (7 : ZMod 320796191) ^ 1253110 := by rw [pow_add]
          _ = 278861164 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 320796191) ^ 5012440 = 155335491 := by
        calc
          (7 : ZMod 320796191) ^ 5012440 = (7 : ZMod 320796191) ^ (2506220 + 2506220) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2506220 * (7 : ZMod 320796191) ^ 2506220 := by rw [pow_add]
          _ = 155335491 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 320796191) ^ 10024880 = 32842523 := by
        calc
          (7 : ZMod 320796191) ^ 10024880 = (7 : ZMod 320796191) ^ (5012440 + 5012440) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 5012440 * (7 : ZMod 320796191) ^ 5012440 := by rw [pow_add]
          _ = 32842523 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 320796191) ^ 20049761 = 311159585 := by
        calc
          (7 : ZMod 320796191) ^ 20049761 = (7 : ZMod 320796191) ^ (10024880 + 10024880 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 10024880 * (7 : ZMod 320796191) ^ 10024880) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 311159585 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 320796191) ^ 40099523 = 15207510 := by
        calc
          (7 : ZMod 320796191) ^ 40099523 = (7 : ZMod 320796191) ^ (20049761 + 20049761 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 20049761 * (7 : ZMod 320796191) ^ 20049761) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 15207510 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 320796191) ^ 80199047 = 113486851 := by
        calc
          (7 : ZMod 320796191) ^ 80199047 = (7 : ZMod 320796191) ^ (40099523 + 40099523 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 40099523 * (7 : ZMod 320796191) ^ 40099523) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 113486851 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 320796191) ^ 160398095 = 320796190 := by
        calc
          (7 : ZMod 320796191) ^ 160398095 = (7 : ZMod 320796191) ^ (80199047 + 80199047 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 80199047 * (7 : ZMod 320796191) ^ 80199047) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 320796190 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 320796191) ^ 320796190 = 1 := by
        calc
          (7 : ZMod 320796191) ^ 320796190 = (7 : ZMod 320796191) ^ (160398095 + 160398095) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 160398095 * (7 : ZMod 320796191) ^ 160398095 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (13, 1), (19, 1), (11807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (13, 1), (19, 1), (11807, 1)] : List FactorBlock).map factorBlockValue).prod = 320796191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 320796191) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 320796191) ^ 2 = 49 := by
        calc
          (7 : ZMod 320796191) ^ 2 = (7 : ZMod 320796191) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1 * (7 : ZMod 320796191) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 320796191) ^ 4 = 2401 := by
        calc
          (7 : ZMod 320796191) ^ 4 = (7 : ZMod 320796191) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2 * (7 : ZMod 320796191) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 320796191) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 320796191) ^ 9 = (7 : ZMod 320796191) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 4 * (7 : ZMod 320796191) ^ 4) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 320796191) ^ 19 = 181491976 := by
        calc
          (7 : ZMod 320796191) ^ 19 = (7 : ZMod 320796191) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 9 * (7 : ZMod 320796191) ^ 9) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 181491976 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 320796191) ^ 38 = 179517935 := by
        calc
          (7 : ZMod 320796191) ^ 38 = (7 : ZMod 320796191) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 19 * (7 : ZMod 320796191) ^ 19 := by rw [pow_add]
          _ = 179517935 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 320796191) ^ 76 = 231307893 := by
        calc
          (7 : ZMod 320796191) ^ 76 = (7 : ZMod 320796191) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 38 * (7 : ZMod 320796191) ^ 38 := by rw [pow_add]
          _ = 231307893 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 320796191) ^ 152 = 185228370 := by
        calc
          (7 : ZMod 320796191) ^ 152 = (7 : ZMod 320796191) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 76 * (7 : ZMod 320796191) ^ 76 := by rw [pow_add]
          _ = 185228370 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 320796191) ^ 305 = 90796150 := by
        calc
          (7 : ZMod 320796191) ^ 305 = (7 : ZMod 320796191) ^ (152 + 152 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 152 * (7 : ZMod 320796191) ^ 152) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 90796150 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 320796191) ^ 611 = 279530125 := by
        calc
          (7 : ZMod 320796191) ^ 611 = (7 : ZMod 320796191) ^ (305 + 305 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 305 * (7 : ZMod 320796191) ^ 305) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 279530125 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 320796191) ^ 1223 = 56697326 := by
        calc
          (7 : ZMod 320796191) ^ 1223 = (7 : ZMod 320796191) ^ (611 + 611 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 611 * (7 : ZMod 320796191) ^ 611) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 56697326 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 320796191) ^ 2447 = 82277163 := by
        calc
          (7 : ZMod 320796191) ^ 2447 = (7 : ZMod 320796191) ^ (1223 + 1223 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1223 * (7 : ZMod 320796191) ^ 1223) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 82277163 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 320796191) ^ 4894 = 185116898 := by
        calc
          (7 : ZMod 320796191) ^ 4894 = (7 : ZMod 320796191) ^ (2447 + 2447) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2447 * (7 : ZMod 320796191) ^ 2447 := by rw [pow_add]
          _ = 185116898 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 320796191) ^ 9789 = 67144635 := by
        calc
          (7 : ZMod 320796191) ^ 9789 = (7 : ZMod 320796191) ^ (4894 + 4894 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 4894 * (7 : ZMod 320796191) ^ 4894) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 67144635 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 320796191) ^ 19579 = 202758682 := by
        calc
          (7 : ZMod 320796191) ^ 19579 = (7 : ZMod 320796191) ^ (9789 + 9789 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 9789 * (7 : ZMod 320796191) ^ 9789) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 202758682 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 320796191) ^ 39159 = 4264519 := by
        calc
          (7 : ZMod 320796191) ^ 39159 = (7 : ZMod 320796191) ^ (19579 + 19579 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 19579 * (7 : ZMod 320796191) ^ 19579) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 4264519 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 320796191) ^ 78319 = 20450233 := by
        calc
          (7 : ZMod 320796191) ^ 78319 = (7 : ZMod 320796191) ^ (39159 + 39159 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 39159 * (7 : ZMod 320796191) ^ 39159) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 20450233 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 320796191) ^ 156638 = 301025701 := by
        calc
          (7 : ZMod 320796191) ^ 156638 = (7 : ZMod 320796191) ^ (78319 + 78319) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 78319 * (7 : ZMod 320796191) ^ 78319 := by rw [pow_add]
          _ = 301025701 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 320796191) ^ 313277 = 244056881 := by
        calc
          (7 : ZMod 320796191) ^ 313277 = (7 : ZMod 320796191) ^ (156638 + 156638 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 156638 * (7 : ZMod 320796191) ^ 156638) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 244056881 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 320796191) ^ 626555 = 201108660 := by
        calc
          (7 : ZMod 320796191) ^ 626555 = (7 : ZMod 320796191) ^ (313277 + 313277 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 313277 * (7 : ZMod 320796191) ^ 313277) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 201108660 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 320796191) ^ 1253110 = 249588184 := by
        calc
          (7 : ZMod 320796191) ^ 1253110 = (7 : ZMod 320796191) ^ (626555 + 626555) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 626555 * (7 : ZMod 320796191) ^ 626555 := by rw [pow_add]
          _ = 249588184 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 320796191) ^ 2506220 = 278861164 := by
        calc
          (7 : ZMod 320796191) ^ 2506220 = (7 : ZMod 320796191) ^ (1253110 + 1253110) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1253110 * (7 : ZMod 320796191) ^ 1253110 := by rw [pow_add]
          _ = 278861164 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 320796191) ^ 5012440 = 155335491 := by
        calc
          (7 : ZMod 320796191) ^ 5012440 = (7 : ZMod 320796191) ^ (2506220 + 2506220) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2506220 * (7 : ZMod 320796191) ^ 2506220 := by rw [pow_add]
          _ = 155335491 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 320796191) ^ 10024880 = 32842523 := by
        calc
          (7 : ZMod 320796191) ^ 10024880 = (7 : ZMod 320796191) ^ (5012440 + 5012440) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 5012440 * (7 : ZMod 320796191) ^ 5012440 := by rw [pow_add]
          _ = 32842523 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 320796191) ^ 20049761 = 311159585 := by
        calc
          (7 : ZMod 320796191) ^ 20049761 = (7 : ZMod 320796191) ^ (10024880 + 10024880 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 10024880 * (7 : ZMod 320796191) ^ 10024880) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 311159585 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 320796191) ^ 40099523 = 15207510 := by
        calc
          (7 : ZMod 320796191) ^ 40099523 = (7 : ZMod 320796191) ^ (20049761 + 20049761 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 20049761 * (7 : ZMod 320796191) ^ 20049761) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 15207510 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 320796191) ^ 80199047 = 113486851 := by
        calc
          (7 : ZMod 320796191) ^ 80199047 = (7 : ZMod 320796191) ^ (40099523 + 40099523 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 40099523 * (7 : ZMod 320796191) ^ 40099523) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 113486851 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 320796191) ^ 160398095 = 320796190 := by
        calc
          (7 : ZMod 320796191) ^ 160398095 = (7 : ZMod 320796191) ^ (80199047 + 80199047 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 80199047 * (7 : ZMod 320796191) ^ 80199047) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 320796190 := by rw [factor_0_26]; decide
      change (7 : ZMod 320796191) ^ 160398095 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (7 : ZMod 320796191) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 320796191) ^ 3 = 343 := by
        calc
          (7 : ZMod 320796191) ^ 3 = (7 : ZMod 320796191) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1 * (7 : ZMod 320796191) ^ 1) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 320796191) ^ 7 = 823543 := by
        calc
          (7 : ZMod 320796191) ^ 7 = (7 : ZMod 320796191) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 3 * (7 : ZMod 320796191) ^ 3) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 320796191) ^ 15 = 98679334 := by
        calc
          (7 : ZMod 320796191) ^ 15 = (7 : ZMod 320796191) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 7 * (7 : ZMod 320796191) ^ 7) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 98679334 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 320796191) ^ 30 = 91808337 := by
        calc
          (7 : ZMod 320796191) ^ 30 = (7 : ZMod 320796191) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 15 * (7 : ZMod 320796191) ^ 15 := by rw [pow_add]
          _ = 91808337 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 320796191) ^ 61 = 281661879 := by
        calc
          (7 : ZMod 320796191) ^ 61 = (7 : ZMod 320796191) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 30 * (7 : ZMod 320796191) ^ 30) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 281661879 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 320796191) ^ 122 = 207235513 := by
        calc
          (7 : ZMod 320796191) ^ 122 = (7 : ZMod 320796191) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 61 * (7 : ZMod 320796191) ^ 61 := by rw [pow_add]
          _ = 207235513 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 320796191) ^ 244 = 178663460 := by
        calc
          (7 : ZMod 320796191) ^ 244 = (7 : ZMod 320796191) ^ (122 + 122) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 122 * (7 : ZMod 320796191) ^ 122 := by rw [pow_add]
          _ = 178663460 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 320796191) ^ 489 = 190368883 := by
        calc
          (7 : ZMod 320796191) ^ 489 = (7 : ZMod 320796191) ^ (244 + 244 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 244 * (7 : ZMod 320796191) ^ 244) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 190368883 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 320796191) ^ 978 = 242590126 := by
        calc
          (7 : ZMod 320796191) ^ 978 = (7 : ZMod 320796191) ^ (489 + 489) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 489 * (7 : ZMod 320796191) ^ 489 := by rw [pow_add]
          _ = 242590126 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 320796191) ^ 1957 = 114972660 := by
        calc
          (7 : ZMod 320796191) ^ 1957 = (7 : ZMod 320796191) ^ (978 + 978 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 978 * (7 : ZMod 320796191) ^ 978) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 114972660 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 320796191) ^ 3915 = 53834994 := by
        calc
          (7 : ZMod 320796191) ^ 3915 = (7 : ZMod 320796191) ^ (1957 + 1957 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1957 * (7 : ZMod 320796191) ^ 1957) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 53834994 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 320796191) ^ 7831 = 122320723 := by
        calc
          (7 : ZMod 320796191) ^ 7831 = (7 : ZMod 320796191) ^ (3915 + 3915 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 3915 * (7 : ZMod 320796191) ^ 3915) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 122320723 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 320796191) ^ 15663 = 66736151 := by
        calc
          (7 : ZMod 320796191) ^ 15663 = (7 : ZMod 320796191) ^ (7831 + 7831 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 7831 * (7 : ZMod 320796191) ^ 7831) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 66736151 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 320796191) ^ 31327 = 91630508 := by
        calc
          (7 : ZMod 320796191) ^ 31327 = (7 : ZMod 320796191) ^ (15663 + 15663 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 15663 * (7 : ZMod 320796191) ^ 15663) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 91630508 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 320796191) ^ 62655 = 31416481 := by
        calc
          (7 : ZMod 320796191) ^ 62655 = (7 : ZMod 320796191) ^ (31327 + 31327 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 31327 * (7 : ZMod 320796191) ^ 31327) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 31416481 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 320796191) ^ 125311 = 235148942 := by
        calc
          (7 : ZMod 320796191) ^ 125311 = (7 : ZMod 320796191) ^ (62655 + 62655 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 62655 * (7 : ZMod 320796191) ^ 62655) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 235148942 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 320796191) ^ 250622 = 126551320 := by
        calc
          (7 : ZMod 320796191) ^ 250622 = (7 : ZMod 320796191) ^ (125311 + 125311) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 125311 * (7 : ZMod 320796191) ^ 125311 := by rw [pow_add]
          _ = 126551320 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 320796191) ^ 501244 = 31973000 := by
        calc
          (7 : ZMod 320796191) ^ 501244 = (7 : ZMod 320796191) ^ (250622 + 250622) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 250622 * (7 : ZMod 320796191) ^ 250622 := by rw [pow_add]
          _ = 31973000 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 320796191) ^ 1002488 = 168637457 := by
        calc
          (7 : ZMod 320796191) ^ 1002488 = (7 : ZMod 320796191) ^ (501244 + 501244) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 501244 * (7 : ZMod 320796191) ^ 501244 := by rw [pow_add]
          _ = 168637457 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 320796191) ^ 2004976 = 268187310 := by
        calc
          (7 : ZMod 320796191) ^ 2004976 = (7 : ZMod 320796191) ^ (1002488 + 1002488) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1002488 * (7 : ZMod 320796191) ^ 1002488 := by rw [pow_add]
          _ = 268187310 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 320796191) ^ 4009952 = 200116763 := by
        calc
          (7 : ZMod 320796191) ^ 4009952 = (7 : ZMod 320796191) ^ (2004976 + 2004976) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2004976 * (7 : ZMod 320796191) ^ 2004976 := by rw [pow_add]
          _ = 200116763 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 320796191) ^ 8019904 = 257210106 := by
        calc
          (7 : ZMod 320796191) ^ 8019904 = (7 : ZMod 320796191) ^ (4009952 + 4009952) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 4009952 * (7 : ZMod 320796191) ^ 4009952 := by rw [pow_add]
          _ = 257210106 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 320796191) ^ 16039809 = 231851623 := by
        calc
          (7 : ZMod 320796191) ^ 16039809 = (7 : ZMod 320796191) ^ (8019904 + 8019904 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 8019904 * (7 : ZMod 320796191) ^ 8019904) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 231851623 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 320796191) ^ 32079619 = 58035296 := by
        calc
          (7 : ZMod 320796191) ^ 32079619 = (7 : ZMod 320796191) ^ (16039809 + 16039809 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 16039809 * (7 : ZMod 320796191) ^ 16039809) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 58035296 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 320796191) ^ 64159238 = 233165191 := by
        calc
          (7 : ZMod 320796191) ^ 64159238 = (7 : ZMod 320796191) ^ (32079619 + 32079619) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 32079619 * (7 : ZMod 320796191) ^ 32079619 := by rw [pow_add]
          _ = 233165191 := by rw [factor_1_24]; decide
      change (7 : ZMod 320796191) ^ 64159238 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (7 : ZMod 320796191) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 320796191) ^ 3 = 343 := by
        calc
          (7 : ZMod 320796191) ^ 3 = (7 : ZMod 320796191) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1 * (7 : ZMod 320796191) ^ 1) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 320796191) ^ 6 = 117649 := by
        calc
          (7 : ZMod 320796191) ^ 6 = (7 : ZMod 320796191) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 3 * (7 : ZMod 320796191) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 320796191) ^ 13 = 8560725 := by
        calc
          (7 : ZMod 320796191) ^ 13 = (7 : ZMod 320796191) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 6 * (7 : ZMod 320796191) ^ 6) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 8560725 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 320796191) ^ 27 = 217249343 := by
        calc
          (7 : ZMod 320796191) ^ 27 = (7 : ZMod 320796191) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 13 * (7 : ZMod 320796191) ^ 13) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 217249343 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 320796191) ^ 55 = 284415925 := by
        calc
          (7 : ZMod 320796191) ^ 55 = (7 : ZMod 320796191) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 27 * (7 : ZMod 320796191) ^ 27) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 284415925 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 320796191) ^ 111 = 104392317 := by
        calc
          (7 : ZMod 320796191) ^ 111 = (7 : ZMod 320796191) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 55 * (7 : ZMod 320796191) ^ 55) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 104392317 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 320796191) ^ 222 = 313626556 := by
        calc
          (7 : ZMod 320796191) ^ 222 = (7 : ZMod 320796191) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 111 * (7 : ZMod 320796191) ^ 111 := by rw [pow_add]
          _ = 313626556 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 320796191) ^ 444 = 246775958 := by
        calc
          (7 : ZMod 320796191) ^ 444 = (7 : ZMod 320796191) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 222 * (7 : ZMod 320796191) ^ 222 := by rw [pow_add]
          _ = 246775958 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 320796191) ^ 889 = 163098546 := by
        calc
          (7 : ZMod 320796191) ^ 889 = (7 : ZMod 320796191) ^ (444 + 444 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 444 * (7 : ZMod 320796191) ^ 444) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 163098546 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 320796191) ^ 1779 = 256228729 := by
        calc
          (7 : ZMod 320796191) ^ 1779 = (7 : ZMod 320796191) ^ (889 + 889 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 889 * (7 : ZMod 320796191) ^ 889) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 256228729 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 320796191) ^ 3559 = 150241272 := by
        calc
          (7 : ZMod 320796191) ^ 3559 = (7 : ZMod 320796191) ^ (1779 + 1779 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1779 * (7 : ZMod 320796191) ^ 1779) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 150241272 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 320796191) ^ 7119 = 61710041 := by
        calc
          (7 : ZMod 320796191) ^ 7119 = (7 : ZMod 320796191) ^ (3559 + 3559 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 3559 * (7 : ZMod 320796191) ^ 3559) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 61710041 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 320796191) ^ 14239 = 95297633 := by
        calc
          (7 : ZMod 320796191) ^ 14239 = (7 : ZMod 320796191) ^ (7119 + 7119 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 7119 * (7 : ZMod 320796191) ^ 7119) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 95297633 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 320796191) ^ 28479 = 97727124 := by
        calc
          (7 : ZMod 320796191) ^ 28479 = (7 : ZMod 320796191) ^ (14239 + 14239 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 14239 * (7 : ZMod 320796191) ^ 14239) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 97727124 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 320796191) ^ 56959 = 314459291 := by
        calc
          (7 : ZMod 320796191) ^ 56959 = (7 : ZMod 320796191) ^ (28479 + 28479 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 28479 * (7 : ZMod 320796191) ^ 28479) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 314459291 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 320796191) ^ 113919 = 298460542 := by
        calc
          (7 : ZMod 320796191) ^ 113919 = (7 : ZMod 320796191) ^ (56959 + 56959 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 56959 * (7 : ZMod 320796191) ^ 56959) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 298460542 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 320796191) ^ 227838 = 152556607 := by
        calc
          (7 : ZMod 320796191) ^ 227838 = (7 : ZMod 320796191) ^ (113919 + 113919) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 113919 * (7 : ZMod 320796191) ^ 113919 := by rw [pow_add]
          _ = 152556607 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 320796191) ^ 455676 = 91388564 := by
        calc
          (7 : ZMod 320796191) ^ 455676 = (7 : ZMod 320796191) ^ (227838 + 227838) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 227838 * (7 : ZMod 320796191) ^ 227838 := by rw [pow_add]
          _ = 91388564 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 320796191) ^ 911352 = 144592431 := by
        calc
          (7 : ZMod 320796191) ^ 911352 = (7 : ZMod 320796191) ^ (455676 + 455676) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 455676 * (7 : ZMod 320796191) ^ 455676 := by rw [pow_add]
          _ = 144592431 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 320796191) ^ 1822705 = 273930517 := by
        calc
          (7 : ZMod 320796191) ^ 1822705 = (7 : ZMod 320796191) ^ (911352 + 911352 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 911352 * (7 : ZMod 320796191) ^ 911352) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 273930517 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 320796191) ^ 3645411 = 97558267 := by
        calc
          (7 : ZMod 320796191) ^ 3645411 = (7 : ZMod 320796191) ^ (1822705 + 1822705 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1822705 * (7 : ZMod 320796191) ^ 1822705) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 97558267 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 320796191) ^ 7290822 = 205032050 := by
        calc
          (7 : ZMod 320796191) ^ 7290822 = (7 : ZMod 320796191) ^ (3645411 + 3645411) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 3645411 * (7 : ZMod 320796191) ^ 3645411 := by rw [pow_add]
          _ = 205032050 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 320796191) ^ 14581645 = 206569781 := by
        calc
          (7 : ZMod 320796191) ^ 14581645 = (7 : ZMod 320796191) ^ (7290822 + 7290822 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 7290822 * (7 : ZMod 320796191) ^ 7290822) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 206569781 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 320796191) ^ 29163290 = 160903311 := by
        calc
          (7 : ZMod 320796191) ^ 29163290 = (7 : ZMod 320796191) ^ (14581645 + 14581645) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 14581645 * (7 : ZMod 320796191) ^ 14581645 := by rw [pow_add]
          _ = 160903311 := by rw [factor_2_23]; decide
      change (7 : ZMod 320796191) ^ 29163290 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (7 : ZMod 320796191) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 320796191) ^ 2 = 49 := by
        calc
          (7 : ZMod 320796191) ^ 2 = (7 : ZMod 320796191) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1 * (7 : ZMod 320796191) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 320796191) ^ 5 = 16807 := by
        calc
          (7 : ZMod 320796191) ^ 5 = (7 : ZMod 320796191) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 2 * (7 : ZMod 320796191) ^ 2) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 320796191) ^ 11 = 52549597 := by
        calc
          (7 : ZMod 320796191) ^ 11 = (7 : ZMod 320796191) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 5 * (7 : ZMod 320796191) ^ 5) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 52549597 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 320796191) ^ 23 = 121006998 := by
        calc
          (7 : ZMod 320796191) ^ 23 = (7 : ZMod 320796191) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 11 * (7 : ZMod 320796191) ^ 11) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 121006998 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 320796191) ^ 47 = 31401488 := by
        calc
          (7 : ZMod 320796191) ^ 47 = (7 : ZMod 320796191) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 23 * (7 : ZMod 320796191) ^ 23) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 31401488 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 320796191) ^ 94 = 61400265 := by
        calc
          (7 : ZMod 320796191) ^ 94 = (7 : ZMod 320796191) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 47 * (7 : ZMod 320796191) ^ 47 := by rw [pow_add]
          _ = 61400265 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 320796191) ^ 188 = 196584899 := by
        calc
          (7 : ZMod 320796191) ^ 188 = (7 : ZMod 320796191) ^ (94 + 94) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 94 * (7 : ZMod 320796191) ^ 94 := by rw [pow_add]
          _ = 196584899 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 320796191) ^ 376 = 229619907 := by
        calc
          (7 : ZMod 320796191) ^ 376 = (7 : ZMod 320796191) ^ (188 + 188) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 188 * (7 : ZMod 320796191) ^ 188 := by rw [pow_add]
          _ = 229619907 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 320796191) ^ 753 = 174309233 := by
        calc
          (7 : ZMod 320796191) ^ 753 = (7 : ZMod 320796191) ^ (376 + 376 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 376 * (7 : ZMod 320796191) ^ 376) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 174309233 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 320796191) ^ 1506 = 166114586 := by
        calc
          (7 : ZMod 320796191) ^ 1506 = (7 : ZMod 320796191) ^ (753 + 753) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 753 * (7 : ZMod 320796191) ^ 753 := by rw [pow_add]
          _ = 166114586 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 320796191) ^ 3012 = 119043232 := by
        calc
          (7 : ZMod 320796191) ^ 3012 = (7 : ZMod 320796191) ^ (1506 + 1506) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1506 * (7 : ZMod 320796191) ^ 1506 := by rw [pow_add]
          _ = 119043232 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 320796191) ^ 6024 = 11397772 := by
        calc
          (7 : ZMod 320796191) ^ 6024 = (7 : ZMod 320796191) ^ (3012 + 3012) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 3012 * (7 : ZMod 320796191) ^ 3012 := by rw [pow_add]
          _ = 11397772 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 320796191) ^ 12049 = 275358278 := by
        calc
          (7 : ZMod 320796191) ^ 12049 = (7 : ZMod 320796191) ^ (6024 + 6024 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 6024 * (7 : ZMod 320796191) ^ 6024) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 275358278 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 320796191) ^ 24098 = 72839635 := by
        calc
          (7 : ZMod 320796191) ^ 24098 = (7 : ZMod 320796191) ^ (12049 + 12049) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 12049 * (7 : ZMod 320796191) ^ 12049 := by rw [pow_add]
          _ = 72839635 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 320796191) ^ 48196 = 153157617 := by
        calc
          (7 : ZMod 320796191) ^ 48196 = (7 : ZMod 320796191) ^ (24098 + 24098) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 24098 * (7 : ZMod 320796191) ^ 24098 := by rw [pow_add]
          _ = 153157617 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 320796191) ^ 96393 = 27431148 := by
        calc
          (7 : ZMod 320796191) ^ 96393 = (7 : ZMod 320796191) ^ (48196 + 48196 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 48196 * (7 : ZMod 320796191) ^ 48196) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 27431148 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 320796191) ^ 192786 = 315083529 := by
        calc
          (7 : ZMod 320796191) ^ 192786 = (7 : ZMod 320796191) ^ (96393 + 96393) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 96393 * (7 : ZMod 320796191) ^ 96393 := by rw [pow_add]
          _ = 315083529 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 320796191) ^ 385572 = 231412005 := by
        calc
          (7 : ZMod 320796191) ^ 385572 = (7 : ZMod 320796191) ^ (192786 + 192786) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 192786 * (7 : ZMod 320796191) ^ 192786 := by rw [pow_add]
          _ = 231412005 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 320796191) ^ 771144 = 273654094 := by
        calc
          (7 : ZMod 320796191) ^ 771144 = (7 : ZMod 320796191) ^ (385572 + 385572) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 385572 * (7 : ZMod 320796191) ^ 385572 := by rw [pow_add]
          _ = 273654094 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 320796191) ^ 1542289 = 83161277 := by
        calc
          (7 : ZMod 320796191) ^ 1542289 = (7 : ZMod 320796191) ^ (771144 + 771144 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 771144 * (7 : ZMod 320796191) ^ 771144) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 83161277 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 320796191) ^ 3084578 = 244364990 := by
        calc
          (7 : ZMod 320796191) ^ 3084578 = (7 : ZMod 320796191) ^ (1542289 + 1542289) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1542289 * (7 : ZMod 320796191) ^ 1542289 := by rw [pow_add]
          _ = 244364990 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 320796191) ^ 6169157 = 99026466 := by
        calc
          (7 : ZMod 320796191) ^ 6169157 = (7 : ZMod 320796191) ^ (3084578 + 3084578 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 3084578 * (7 : ZMod 320796191) ^ 3084578) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 99026466 := by rw [factor_3_21]; decide
      have factor_3_23 : (7 : ZMod 320796191) ^ 12338315 = 129612172 := by
        calc
          (7 : ZMod 320796191) ^ 12338315 = (7 : ZMod 320796191) ^ (6169157 + 6169157 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 6169157 * (7 : ZMod 320796191) ^ 6169157) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 129612172 := by rw [factor_3_22]; decide
      have factor_3_24 : (7 : ZMod 320796191) ^ 24676630 = 67408860 := by
        calc
          (7 : ZMod 320796191) ^ 24676630 = (7 : ZMod 320796191) ^ (12338315 + 12338315) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 12338315 * (7 : ZMod 320796191) ^ 12338315 := by rw [pow_add]
          _ = 67408860 := by rw [factor_3_23]; decide
      change (7 : ZMod 320796191) ^ 24676630 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (7 : ZMod 320796191) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 320796191) ^ 2 = 49 := by
        calc
          (7 : ZMod 320796191) ^ 2 = (7 : ZMod 320796191) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1 * (7 : ZMod 320796191) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 320796191) ^ 4 = 2401 := by
        calc
          (7 : ZMod 320796191) ^ 4 = (7 : ZMod 320796191) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2 * (7 : ZMod 320796191) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 320796191) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 320796191) ^ 8 = (7 : ZMod 320796191) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 4 * (7 : ZMod 320796191) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 320796191) ^ 16 = 49162956 := by
        calc
          (7 : ZMod 320796191) ^ 16 = (7 : ZMod 320796191) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 8 * (7 : ZMod 320796191) ^ 8 := by rw [pow_add]
          _ = 49162956 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 320796191) ^ 32 = 7461839 := by
        calc
          (7 : ZMod 320796191) ^ 32 = (7 : ZMod 320796191) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 16 * (7 : ZMod 320796191) ^ 16 := by rw [pow_add]
          _ = 7461839 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 320796191) ^ 64 = 50371006 := by
        calc
          (7 : ZMod 320796191) ^ 64 = (7 : ZMod 320796191) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 32 * (7 : ZMod 320796191) ^ 32 := by rw [pow_add]
          _ = 50371006 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 320796191) ^ 128 = 219556746 := by
        calc
          (7 : ZMod 320796191) ^ 128 = (7 : ZMod 320796191) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 64 * (7 : ZMod 320796191) ^ 64 := by rw [pow_add]
          _ = 219556746 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 320796191) ^ 257 = 197916801 := by
        calc
          (7 : ZMod 320796191) ^ 257 = (7 : ZMod 320796191) ^ (128 + 128 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 128 * (7 : ZMod 320796191) ^ 128) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 197916801 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 320796191) ^ 515 = 161776974 := by
        calc
          (7 : ZMod 320796191) ^ 515 = (7 : ZMod 320796191) ^ (257 + 257 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 257 * (7 : ZMod 320796191) ^ 257) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 161776974 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 320796191) ^ 1030 = 27092753 := by
        calc
          (7 : ZMod 320796191) ^ 1030 = (7 : ZMod 320796191) ^ (515 + 515) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 515 * (7 : ZMod 320796191) ^ 515 := by rw [pow_add]
          _ = 27092753 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 320796191) ^ 2061 = 122932847 := by
        calc
          (7 : ZMod 320796191) ^ 2061 = (7 : ZMod 320796191) ^ (1030 + 1030 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1030 * (7 : ZMod 320796191) ^ 1030) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 122932847 := by rw [factor_4_10]; decide
      have factor_4_12 : (7 : ZMod 320796191) ^ 4122 = 229256727 := by
        calc
          (7 : ZMod 320796191) ^ 4122 = (7 : ZMod 320796191) ^ (2061 + 2061) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2061 * (7 : ZMod 320796191) ^ 2061 := by rw [pow_add]
          _ = 229256727 := by rw [factor_4_11]; decide
      have factor_4_13 : (7 : ZMod 320796191) ^ 8244 = 113374463 := by
        calc
          (7 : ZMod 320796191) ^ 8244 = (7 : ZMod 320796191) ^ (4122 + 4122) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 4122 * (7 : ZMod 320796191) ^ 4122 := by rw [pow_add]
          _ = 113374463 := by rw [factor_4_12]; decide
      have factor_4_14 : (7 : ZMod 320796191) ^ 16488 = 254418766 := by
        calc
          (7 : ZMod 320796191) ^ 16488 = (7 : ZMod 320796191) ^ (8244 + 8244) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 8244 * (7 : ZMod 320796191) ^ 8244 := by rw [pow_add]
          _ = 254418766 := by rw [factor_4_13]; decide
      have factor_4_15 : (7 : ZMod 320796191) ^ 32976 = 96188765 := by
        calc
          (7 : ZMod 320796191) ^ 32976 = (7 : ZMod 320796191) ^ (16488 + 16488) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 16488 * (7 : ZMod 320796191) ^ 16488 := by rw [pow_add]
          _ = 96188765 := by rw [factor_4_14]; decide
      have factor_4_16 : (7 : ZMod 320796191) ^ 65953 = 135812578 := by
        calc
          (7 : ZMod 320796191) ^ 65953 = (7 : ZMod 320796191) ^ (32976 + 32976 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 32976 * (7 : ZMod 320796191) ^ 32976) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 135812578 := by rw [factor_4_15]; decide
      have factor_4_17 : (7 : ZMod 320796191) ^ 131906 = 39101553 := by
        calc
          (7 : ZMod 320796191) ^ 131906 = (7 : ZMod 320796191) ^ (65953 + 65953) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 65953 * (7 : ZMod 320796191) ^ 65953 := by rw [pow_add]
          _ = 39101553 := by rw [factor_4_16]; decide
      have factor_4_18 : (7 : ZMod 320796191) ^ 263812 = 119303877 := by
        calc
          (7 : ZMod 320796191) ^ 263812 = (7 : ZMod 320796191) ^ (131906 + 131906) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 131906 * (7 : ZMod 320796191) ^ 131906 := by rw [pow_add]
          _ = 119303877 := by rw [factor_4_17]; decide
      have factor_4_19 : (7 : ZMod 320796191) ^ 527625 = 167600040 := by
        calc
          (7 : ZMod 320796191) ^ 527625 = (7 : ZMod 320796191) ^ (263812 + 263812 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 263812 * (7 : ZMod 320796191) ^ 263812) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 167600040 := by rw [factor_4_18]; decide
      have factor_4_20 : (7 : ZMod 320796191) ^ 1055250 = 152638293 := by
        calc
          (7 : ZMod 320796191) ^ 1055250 = (7 : ZMod 320796191) ^ (527625 + 527625) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 527625 * (7 : ZMod 320796191) ^ 527625 := by rw [pow_add]
          _ = 152638293 := by rw [factor_4_19]; decide
      have factor_4_21 : (7 : ZMod 320796191) ^ 2110501 = 170006703 := by
        calc
          (7 : ZMod 320796191) ^ 2110501 = (7 : ZMod 320796191) ^ (1055250 + 1055250 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1055250 * (7 : ZMod 320796191) ^ 1055250) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 170006703 := by rw [factor_4_20]; decide
      have factor_4_22 : (7 : ZMod 320796191) ^ 4221002 = 274518304 := by
        calc
          (7 : ZMod 320796191) ^ 4221002 = (7 : ZMod 320796191) ^ (2110501 + 2110501) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 2110501 * (7 : ZMod 320796191) ^ 2110501 := by rw [pow_add]
          _ = 274518304 := by rw [factor_4_21]; decide
      have factor_4_23 : (7 : ZMod 320796191) ^ 8442005 = 209498441 := by
        calc
          (7 : ZMod 320796191) ^ 8442005 = (7 : ZMod 320796191) ^ (4221002 + 4221002 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 4221002 * (7 : ZMod 320796191) ^ 4221002) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 209498441 := by rw [factor_4_22]; decide
      have factor_4_24 : (7 : ZMod 320796191) ^ 16884010 = 2573319 := by
        calc
          (7 : ZMod 320796191) ^ 16884010 = (7 : ZMod 320796191) ^ (8442005 + 8442005) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 8442005 * (7 : ZMod 320796191) ^ 8442005 := by rw [pow_add]
          _ = 2573319 := by rw [factor_4_23]; decide
      change (7 : ZMod 320796191) ^ 16884010 ≠ 1
      rw [factor_4_24]
      decide
    ·
      have factor_5_0 : (7 : ZMod 320796191) ^ 1 = 7 := by norm_num
      have factor_5_1 : (7 : ZMod 320796191) ^ 3 = 343 := by
        calc
          (7 : ZMod 320796191) ^ 3 = (7 : ZMod 320796191) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 1 * (7 : ZMod 320796191) ^ 1) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_5_0]; decide
      have factor_5_2 : (7 : ZMod 320796191) ^ 6 = 117649 := by
        calc
          (7 : ZMod 320796191) ^ 6 = (7 : ZMod 320796191) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 3 * (7 : ZMod 320796191) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_5_1]; decide
      have factor_5_3 : (7 : ZMod 320796191) ^ 13 = 8560725 := by
        calc
          (7 : ZMod 320796191) ^ 13 = (7 : ZMod 320796191) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 6 * (7 : ZMod 320796191) ^ 6) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 8560725 := by rw [factor_5_2]; decide
      have factor_5_4 : (7 : ZMod 320796191) ^ 26 = 122691675 := by
        calc
          (7 : ZMod 320796191) ^ 26 = (7 : ZMod 320796191) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 13 * (7 : ZMod 320796191) ^ 13 := by rw [pow_add]
          _ = 122691675 := by rw [factor_5_3]; decide
      have factor_5_5 : (7 : ZMod 320796191) ^ 53 = 64726156 := by
        calc
          (7 : ZMod 320796191) ^ 53 = (7 : ZMod 320796191) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 26 * (7 : ZMod 320796191) ^ 26) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 64726156 := by rw [factor_5_4]; decide
      have factor_5_6 : (7 : ZMod 320796191) ^ 106 = 201813680 := by
        calc
          (7 : ZMod 320796191) ^ 106 = (7 : ZMod 320796191) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 53 * (7 : ZMod 320796191) ^ 53 := by rw [pow_add]
          _ = 201813680 := by rw [factor_5_5]; decide
      have factor_5_7 : (7 : ZMod 320796191) ^ 212 = 1846383 := by
        calc
          (7 : ZMod 320796191) ^ 212 = (7 : ZMod 320796191) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 106 * (7 : ZMod 320796191) ^ 106 := by rw [pow_add]
          _ = 1846383 := by rw [factor_5_6]; decide
      have factor_5_8 : (7 : ZMod 320796191) ^ 424 = 29060932 := by
        calc
          (7 : ZMod 320796191) ^ 424 = (7 : ZMod 320796191) ^ (212 + 212) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 212 * (7 : ZMod 320796191) ^ 212 := by rw [pow_add]
          _ = 29060932 := by rw [factor_5_7]; decide
      have factor_5_9 : (7 : ZMod 320796191) ^ 849 = 5181676 := by
        calc
          (7 : ZMod 320796191) ^ 849 = (7 : ZMod 320796191) ^ (424 + 424 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 424 * (7 : ZMod 320796191) ^ 424) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 5181676 := by rw [factor_5_8]; decide
      have factor_5_10 : (7 : ZMod 320796191) ^ 1698 = 87370849 := by
        calc
          (7 : ZMod 320796191) ^ 1698 = (7 : ZMod 320796191) ^ (849 + 849) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 849 * (7 : ZMod 320796191) ^ 849 := by rw [pow_add]
          _ = 87370849 := by rw [factor_5_9]; decide
      have factor_5_11 : (7 : ZMod 320796191) ^ 3396 = 56333374 := by
        calc
          (7 : ZMod 320796191) ^ 3396 = (7 : ZMod 320796191) ^ (1698 + 1698) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 1698 * (7 : ZMod 320796191) ^ 1698 := by rw [pow_add]
          _ = 56333374 := by rw [factor_5_10]; decide
      have factor_5_12 : (7 : ZMod 320796191) ^ 6792 = 295228802 := by
        calc
          (7 : ZMod 320796191) ^ 6792 = (7 : ZMod 320796191) ^ (3396 + 3396) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 3396 * (7 : ZMod 320796191) ^ 3396 := by rw [pow_add]
          _ = 295228802 := by rw [factor_5_11]; decide
      have factor_5_13 : (7 : ZMod 320796191) ^ 13585 = 227147719 := by
        calc
          (7 : ZMod 320796191) ^ 13585 = (7 : ZMod 320796191) ^ (6792 + 6792 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = ((7 : ZMod 320796191) ^ 6792 * (7 : ZMod 320796191) ^ 6792) * (7 : ZMod 320796191) := by rw [pow_succ, pow_add]
          _ = 227147719 := by rw [factor_5_12]; decide
      have factor_5_14 : (7 : ZMod 320796191) ^ 27170 = 5283271 := by
        calc
          (7 : ZMod 320796191) ^ 27170 = (7 : ZMod 320796191) ^ (13585 + 13585) :=
            congrArg (fun n : ℕ => (7 : ZMod 320796191) ^ n) (by norm_num)
          _ = (7 : ZMod 320796191) ^ 13585 * (7 : ZMod 320796191) ^ 13585 := by rw [pow_add]
          _ = 5283271 := by rw [factor_5_13]; decide
      change (7 : ZMod 320796191) ^ 27170 ≠ 1
      rw [factor_5_14]
      decide

#print axioms prime_lucas_320796191

end TotientTailPeriodKiller
end Erdos249257
