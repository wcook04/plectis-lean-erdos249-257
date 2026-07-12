import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_11867484623 : Nat.Prime 11867484623 := by
  apply lucas_primality 11867484623 (5 : ZMod 11867484623)
  ·
      have fermat_0 : (5 : ZMod 11867484623) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 11867484623) ^ 2 = 25 := by
        calc
          (5 : ZMod 11867484623) ^ 2 = (5 : ZMod 11867484623) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 1 * (5 : ZMod 11867484623) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 11867484623) ^ 5 = 3125 := by
        calc
          (5 : ZMod 11867484623) ^ 5 = (5 : ZMod 11867484623) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 2 * (5 : ZMod 11867484623) ^ 2) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 11867484623) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 11867484623) ^ 11 = (5 : ZMod 11867484623) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 5 * (5 : ZMod 11867484623) ^ 5) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 11867484623) ^ 22 = 8130254925 := by
        calc
          (5 : ZMod 11867484623) ^ 22 = (5 : ZMod 11867484623) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 11 * (5 : ZMod 11867484623) ^ 11 := by rw [pow_add]
          _ = 8130254925 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 11867484623) ^ 44 = 762897353 := by
        calc
          (5 : ZMod 11867484623) ^ 44 = (5 : ZMod 11867484623) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 22 * (5 : ZMod 11867484623) ^ 22 := by rw [pow_add]
          _ = 762897353 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 11867484623) ^ 88 = 10505043694 := by
        calc
          (5 : ZMod 11867484623) ^ 88 = (5 : ZMod 11867484623) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 44 * (5 : ZMod 11867484623) ^ 44 := by rw [pow_add]
          _ = 10505043694 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 11867484623) ^ 176 = 11813335055 := by
        calc
          (5 : ZMod 11867484623) ^ 176 = (5 : ZMod 11867484623) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 88 * (5 : ZMod 11867484623) ^ 88 := by rw [pow_add]
          _ = 11813335055 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 11867484623) ^ 353 = 1684402134 := by
        calc
          (5 : ZMod 11867484623) ^ 353 = (5 : ZMod 11867484623) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 176 * (5 : ZMod 11867484623) ^ 176) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 1684402134 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 11867484623) ^ 707 = 4373625379 := by
        calc
          (5 : ZMod 11867484623) ^ 707 = (5 : ZMod 11867484623) ^ (353 + 353 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 353 * (5 : ZMod 11867484623) ^ 353) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 4373625379 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 11867484623) ^ 1414 = 1739893732 := by
        calc
          (5 : ZMod 11867484623) ^ 1414 = (5 : ZMod 11867484623) ^ (707 + 707) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 707 * (5 : ZMod 11867484623) ^ 707 := by rw [pow_add]
          _ = 1739893732 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 11867484623) ^ 2829 = 1268130476 := by
        calc
          (5 : ZMod 11867484623) ^ 2829 = (5 : ZMod 11867484623) ^ (1414 + 1414 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 1414 * (5 : ZMod 11867484623) ^ 1414) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 1268130476 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 11867484623) ^ 5658 = 2244469363 := by
        calc
          (5 : ZMod 11867484623) ^ 5658 = (5 : ZMod 11867484623) ^ (2829 + 2829) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 2829 * (5 : ZMod 11867484623) ^ 2829 := by rw [pow_add]
          _ = 2244469363 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 11867484623) ^ 11317 = 8391094912 := by
        calc
          (5 : ZMod 11867484623) ^ 11317 = (5 : ZMod 11867484623) ^ (5658 + 5658 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 5658 * (5 : ZMod 11867484623) ^ 5658) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 8391094912 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 11867484623) ^ 22635 = 8588332703 := by
        calc
          (5 : ZMod 11867484623) ^ 22635 = (5 : ZMod 11867484623) ^ (11317 + 11317 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 11317 * (5 : ZMod 11867484623) ^ 11317) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 8588332703 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 11867484623) ^ 45270 = 1695472817 := by
        calc
          (5 : ZMod 11867484623) ^ 45270 = (5 : ZMod 11867484623) ^ (22635 + 22635) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 22635 * (5 : ZMod 11867484623) ^ 22635 := by rw [pow_add]
          _ = 1695472817 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 11867484623) ^ 90541 = 5528593992 := by
        calc
          (5 : ZMod 11867484623) ^ 90541 = (5 : ZMod 11867484623) ^ (45270 + 45270 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 45270 * (5 : ZMod 11867484623) ^ 45270) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 5528593992 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 11867484623) ^ 181083 = 1770426597 := by
        calc
          (5 : ZMod 11867484623) ^ 181083 = (5 : ZMod 11867484623) ^ (90541 + 90541 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 90541 * (5 : ZMod 11867484623) ^ 90541) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 1770426597 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 11867484623) ^ 362166 = 1052251778 := by
        calc
          (5 : ZMod 11867484623) ^ 362166 = (5 : ZMod 11867484623) ^ (181083 + 181083) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 181083 * (5 : ZMod 11867484623) ^ 181083 := by rw [pow_add]
          _ = 1052251778 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 11867484623) ^ 724333 = 690037554 := by
        calc
          (5 : ZMod 11867484623) ^ 724333 = (5 : ZMod 11867484623) ^ (362166 + 362166 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 362166 * (5 : ZMod 11867484623) ^ 362166) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 690037554 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 11867484623) ^ 1448667 = 4643831337 := by
        calc
          (5 : ZMod 11867484623) ^ 1448667 = (5 : ZMod 11867484623) ^ (724333 + 724333 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 724333 * (5 : ZMod 11867484623) ^ 724333) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 4643831337 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 11867484623) ^ 2897335 = 7376373802 := by
        calc
          (5 : ZMod 11867484623) ^ 2897335 = (5 : ZMod 11867484623) ^ (1448667 + 1448667 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 1448667 * (5 : ZMod 11867484623) ^ 1448667) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 7376373802 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 11867484623) ^ 5794670 = 8658960940 := by
        calc
          (5 : ZMod 11867484623) ^ 5794670 = (5 : ZMod 11867484623) ^ (2897335 + 2897335) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 2897335 * (5 : ZMod 11867484623) ^ 2897335 := by rw [pow_add]
          _ = 8658960940 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 11867484623) ^ 11589340 = 10644368552 := by
        calc
          (5 : ZMod 11867484623) ^ 11589340 = (5 : ZMod 11867484623) ^ (5794670 + 5794670) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 5794670 * (5 : ZMod 11867484623) ^ 5794670 := by rw [pow_add]
          _ = 10644368552 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 11867484623) ^ 23178680 = 7047752296 := by
        calc
          (5 : ZMod 11867484623) ^ 23178680 = (5 : ZMod 11867484623) ^ (11589340 + 11589340) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 11589340 * (5 : ZMod 11867484623) ^ 11589340 := by rw [pow_add]
          _ = 7047752296 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 11867484623) ^ 46357361 = 10801466542 := by
        calc
          (5 : ZMod 11867484623) ^ 46357361 = (5 : ZMod 11867484623) ^ (23178680 + 23178680 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 23178680 * (5 : ZMod 11867484623) ^ 23178680) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 10801466542 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 11867484623) ^ 92714723 = 9932904530 := by
        calc
          (5 : ZMod 11867484623) ^ 92714723 = (5 : ZMod 11867484623) ^ (46357361 + 46357361 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 46357361 * (5 : ZMod 11867484623) ^ 46357361) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 9932904530 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 11867484623) ^ 185429447 = 6092741135 := by
        calc
          (5 : ZMod 11867484623) ^ 185429447 = (5 : ZMod 11867484623) ^ (92714723 + 92714723 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 92714723 * (5 : ZMod 11867484623) ^ 92714723) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 6092741135 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 11867484623) ^ 370858894 = 2795501919 := by
        calc
          (5 : ZMod 11867484623) ^ 370858894 = (5 : ZMod 11867484623) ^ (185429447 + 185429447) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 185429447 * (5 : ZMod 11867484623) ^ 185429447 := by rw [pow_add]
          _ = 2795501919 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 11867484623) ^ 741717788 = 2121846375 := by
        calc
          (5 : ZMod 11867484623) ^ 741717788 = (5 : ZMod 11867484623) ^ (370858894 + 370858894) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 370858894 * (5 : ZMod 11867484623) ^ 370858894 := by rw [pow_add]
          _ = 2121846375 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 11867484623) ^ 1483435577 = 11640346512 := by
        calc
          (5 : ZMod 11867484623) ^ 1483435577 = (5 : ZMod 11867484623) ^ (741717788 + 741717788 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 741717788 * (5 : ZMod 11867484623) ^ 741717788) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 11640346512 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 11867484623) ^ 2966871155 = 7231724527 := by
        calc
          (5 : ZMod 11867484623) ^ 2966871155 = (5 : ZMod 11867484623) ^ (1483435577 + 1483435577 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 1483435577 * (5 : ZMod 11867484623) ^ 1483435577) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 7231724527 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 11867484623) ^ 5933742311 = 11867484622 := by
        calc
          (5 : ZMod 11867484623) ^ 5933742311 = (5 : ZMod 11867484623) ^ (2966871155 + 2966871155 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 2966871155 * (5 : ZMod 11867484623) ^ 2966871155) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 11867484622 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 11867484623) ^ 11867484622 = 1 := by
        calc
          (5 : ZMod 11867484623) ^ 11867484622 = (5 : ZMod 11867484623) ^ (5933742311 + 5933742311) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 5933742311 * (5 : ZMod 11867484623) ^ 5933742311 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (5197, 1), (163109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (5197, 1), (163109, 1)] : List FactorBlock).map factorBlockValue).prod = 11867484623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 11867484623) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 11867484623) ^ 2 = 25 := by
        calc
          (5 : ZMod 11867484623) ^ 2 = (5 : ZMod 11867484623) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 1 * (5 : ZMod 11867484623) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 11867484623) ^ 5 = 3125 := by
        calc
          (5 : ZMod 11867484623) ^ 5 = (5 : ZMod 11867484623) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 2 * (5 : ZMod 11867484623) ^ 2) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 11867484623) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 11867484623) ^ 11 = (5 : ZMod 11867484623) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 5 * (5 : ZMod 11867484623) ^ 5) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 11867484623) ^ 22 = 8130254925 := by
        calc
          (5 : ZMod 11867484623) ^ 22 = (5 : ZMod 11867484623) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 11 * (5 : ZMod 11867484623) ^ 11 := by rw [pow_add]
          _ = 8130254925 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 11867484623) ^ 44 = 762897353 := by
        calc
          (5 : ZMod 11867484623) ^ 44 = (5 : ZMod 11867484623) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 22 * (5 : ZMod 11867484623) ^ 22 := by rw [pow_add]
          _ = 762897353 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 11867484623) ^ 88 = 10505043694 := by
        calc
          (5 : ZMod 11867484623) ^ 88 = (5 : ZMod 11867484623) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 44 * (5 : ZMod 11867484623) ^ 44 := by rw [pow_add]
          _ = 10505043694 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 11867484623) ^ 176 = 11813335055 := by
        calc
          (5 : ZMod 11867484623) ^ 176 = (5 : ZMod 11867484623) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 88 * (5 : ZMod 11867484623) ^ 88 := by rw [pow_add]
          _ = 11813335055 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 11867484623) ^ 353 = 1684402134 := by
        calc
          (5 : ZMod 11867484623) ^ 353 = (5 : ZMod 11867484623) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 176 * (5 : ZMod 11867484623) ^ 176) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 1684402134 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 11867484623) ^ 707 = 4373625379 := by
        calc
          (5 : ZMod 11867484623) ^ 707 = (5 : ZMod 11867484623) ^ (353 + 353 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 353 * (5 : ZMod 11867484623) ^ 353) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 4373625379 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 11867484623) ^ 1414 = 1739893732 := by
        calc
          (5 : ZMod 11867484623) ^ 1414 = (5 : ZMod 11867484623) ^ (707 + 707) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 707 * (5 : ZMod 11867484623) ^ 707 := by rw [pow_add]
          _ = 1739893732 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 11867484623) ^ 2829 = 1268130476 := by
        calc
          (5 : ZMod 11867484623) ^ 2829 = (5 : ZMod 11867484623) ^ (1414 + 1414 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 1414 * (5 : ZMod 11867484623) ^ 1414) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 1268130476 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 11867484623) ^ 5658 = 2244469363 := by
        calc
          (5 : ZMod 11867484623) ^ 5658 = (5 : ZMod 11867484623) ^ (2829 + 2829) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 2829 * (5 : ZMod 11867484623) ^ 2829 := by rw [pow_add]
          _ = 2244469363 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 11867484623) ^ 11317 = 8391094912 := by
        calc
          (5 : ZMod 11867484623) ^ 11317 = (5 : ZMod 11867484623) ^ (5658 + 5658 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 5658 * (5 : ZMod 11867484623) ^ 5658) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 8391094912 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 11867484623) ^ 22635 = 8588332703 := by
        calc
          (5 : ZMod 11867484623) ^ 22635 = (5 : ZMod 11867484623) ^ (11317 + 11317 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 11317 * (5 : ZMod 11867484623) ^ 11317) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 8588332703 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 11867484623) ^ 45270 = 1695472817 := by
        calc
          (5 : ZMod 11867484623) ^ 45270 = (5 : ZMod 11867484623) ^ (22635 + 22635) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 22635 * (5 : ZMod 11867484623) ^ 22635 := by rw [pow_add]
          _ = 1695472817 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 11867484623) ^ 90541 = 5528593992 := by
        calc
          (5 : ZMod 11867484623) ^ 90541 = (5 : ZMod 11867484623) ^ (45270 + 45270 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 45270 * (5 : ZMod 11867484623) ^ 45270) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 5528593992 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 11867484623) ^ 181083 = 1770426597 := by
        calc
          (5 : ZMod 11867484623) ^ 181083 = (5 : ZMod 11867484623) ^ (90541 + 90541 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 90541 * (5 : ZMod 11867484623) ^ 90541) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 1770426597 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 11867484623) ^ 362166 = 1052251778 := by
        calc
          (5 : ZMod 11867484623) ^ 362166 = (5 : ZMod 11867484623) ^ (181083 + 181083) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 181083 * (5 : ZMod 11867484623) ^ 181083 := by rw [pow_add]
          _ = 1052251778 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 11867484623) ^ 724333 = 690037554 := by
        calc
          (5 : ZMod 11867484623) ^ 724333 = (5 : ZMod 11867484623) ^ (362166 + 362166 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 362166 * (5 : ZMod 11867484623) ^ 362166) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 690037554 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 11867484623) ^ 1448667 = 4643831337 := by
        calc
          (5 : ZMod 11867484623) ^ 1448667 = (5 : ZMod 11867484623) ^ (724333 + 724333 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 724333 * (5 : ZMod 11867484623) ^ 724333) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 4643831337 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 11867484623) ^ 2897335 = 7376373802 := by
        calc
          (5 : ZMod 11867484623) ^ 2897335 = (5 : ZMod 11867484623) ^ (1448667 + 1448667 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 1448667 * (5 : ZMod 11867484623) ^ 1448667) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 7376373802 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 11867484623) ^ 5794670 = 8658960940 := by
        calc
          (5 : ZMod 11867484623) ^ 5794670 = (5 : ZMod 11867484623) ^ (2897335 + 2897335) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 2897335 * (5 : ZMod 11867484623) ^ 2897335 := by rw [pow_add]
          _ = 8658960940 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 11867484623) ^ 11589340 = 10644368552 := by
        calc
          (5 : ZMod 11867484623) ^ 11589340 = (5 : ZMod 11867484623) ^ (5794670 + 5794670) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 5794670 * (5 : ZMod 11867484623) ^ 5794670 := by rw [pow_add]
          _ = 10644368552 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 11867484623) ^ 23178680 = 7047752296 := by
        calc
          (5 : ZMod 11867484623) ^ 23178680 = (5 : ZMod 11867484623) ^ (11589340 + 11589340) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 11589340 * (5 : ZMod 11867484623) ^ 11589340 := by rw [pow_add]
          _ = 7047752296 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 11867484623) ^ 46357361 = 10801466542 := by
        calc
          (5 : ZMod 11867484623) ^ 46357361 = (5 : ZMod 11867484623) ^ (23178680 + 23178680 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 23178680 * (5 : ZMod 11867484623) ^ 23178680) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 10801466542 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 11867484623) ^ 92714723 = 9932904530 := by
        calc
          (5 : ZMod 11867484623) ^ 92714723 = (5 : ZMod 11867484623) ^ (46357361 + 46357361 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 46357361 * (5 : ZMod 11867484623) ^ 46357361) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 9932904530 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 11867484623) ^ 185429447 = 6092741135 := by
        calc
          (5 : ZMod 11867484623) ^ 185429447 = (5 : ZMod 11867484623) ^ (92714723 + 92714723 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 92714723 * (5 : ZMod 11867484623) ^ 92714723) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 6092741135 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 11867484623) ^ 370858894 = 2795501919 := by
        calc
          (5 : ZMod 11867484623) ^ 370858894 = (5 : ZMod 11867484623) ^ (185429447 + 185429447) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 185429447 * (5 : ZMod 11867484623) ^ 185429447 := by rw [pow_add]
          _ = 2795501919 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 11867484623) ^ 741717788 = 2121846375 := by
        calc
          (5 : ZMod 11867484623) ^ 741717788 = (5 : ZMod 11867484623) ^ (370858894 + 370858894) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 370858894 * (5 : ZMod 11867484623) ^ 370858894 := by rw [pow_add]
          _ = 2121846375 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 11867484623) ^ 1483435577 = 11640346512 := by
        calc
          (5 : ZMod 11867484623) ^ 1483435577 = (5 : ZMod 11867484623) ^ (741717788 + 741717788 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 741717788 * (5 : ZMod 11867484623) ^ 741717788) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 11640346512 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 11867484623) ^ 2966871155 = 7231724527 := by
        calc
          (5 : ZMod 11867484623) ^ 2966871155 = (5 : ZMod 11867484623) ^ (1483435577 + 1483435577 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 1483435577 * (5 : ZMod 11867484623) ^ 1483435577) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 7231724527 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 11867484623) ^ 5933742311 = 11867484622 := by
        calc
          (5 : ZMod 11867484623) ^ 5933742311 = (5 : ZMod 11867484623) ^ (2966871155 + 2966871155 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 2966871155 * (5 : ZMod 11867484623) ^ 2966871155) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 11867484622 := by rw [factor_0_31]; decide
      change (5 : ZMod 11867484623) ^ 5933742311 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (5 : ZMod 11867484623) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 11867484623) ^ 3 = 125 := by
        calc
          (5 : ZMod 11867484623) ^ 3 = (5 : ZMod 11867484623) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 1 * (5 : ZMod 11867484623) ^ 1) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 11867484623) ^ 6 = 15625 := by
        calc
          (5 : ZMod 11867484623) ^ 6 = (5 : ZMod 11867484623) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 3 * (5 : ZMod 11867484623) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 11867484623) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 11867484623) ^ 12 = (5 : ZMod 11867484623) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 6 * (5 : ZMod 11867484623) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 11867484623) ^ 25 = 7545672670 := by
        calc
          (5 : ZMod 11867484623) ^ 25 = (5 : ZMod 11867484623) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 12 * (5 : ZMod 11867484623) ^ 12) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 7545672670 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 11867484623) ^ 50 = 5316579133 := by
        calc
          (5 : ZMod 11867484623) ^ 50 = (5 : ZMod 11867484623) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 25 * (5 : ZMod 11867484623) ^ 25 := by rw [pow_add]
          _ = 5316579133 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 11867484623) ^ 101 = 2309541641 := by
        calc
          (5 : ZMod 11867484623) ^ 101 = (5 : ZMod 11867484623) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 50 * (5 : ZMod 11867484623) ^ 50) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 2309541641 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 11867484623) ^ 202 = 1144131999 := by
        calc
          (5 : ZMod 11867484623) ^ 202 = (5 : ZMod 11867484623) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 101 * (5 : ZMod 11867484623) ^ 101 := by rw [pow_add]
          _ = 1144131999 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 11867484623) ^ 404 = 5464416431 := by
        calc
          (5 : ZMod 11867484623) ^ 404 = (5 : ZMod 11867484623) ^ (202 + 202) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 202 * (5 : ZMod 11867484623) ^ 202 := by rw [pow_add]
          _ = 5464416431 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 11867484623) ^ 808 = 4439210492 := by
        calc
          (5 : ZMod 11867484623) ^ 808 = (5 : ZMod 11867484623) ^ (404 + 404) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 404 * (5 : ZMod 11867484623) ^ 404 := by rw [pow_add]
          _ = 4439210492 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 11867484623) ^ 1616 = 127230627 := by
        calc
          (5 : ZMod 11867484623) ^ 1616 = (5 : ZMod 11867484623) ^ (808 + 808) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 808 * (5 : ZMod 11867484623) ^ 808 := by rw [pow_add]
          _ = 127230627 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 11867484623) ^ 3233 = 6440181342 := by
        calc
          (5 : ZMod 11867484623) ^ 3233 = (5 : ZMod 11867484623) ^ (1616 + 1616 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 1616 * (5 : ZMod 11867484623) ^ 1616) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 6440181342 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 11867484623) ^ 6467 = 7732066405 := by
        calc
          (5 : ZMod 11867484623) ^ 6467 = (5 : ZMod 11867484623) ^ (3233 + 3233 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 3233 * (5 : ZMod 11867484623) ^ 3233) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 7732066405 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 11867484623) ^ 12934 = 1615608878 := by
        calc
          (5 : ZMod 11867484623) ^ 12934 = (5 : ZMod 11867484623) ^ (6467 + 6467) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 6467 * (5 : ZMod 11867484623) ^ 6467 := by rw [pow_add]
          _ = 1615608878 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 11867484623) ^ 25869 = 10441363852 := by
        calc
          (5 : ZMod 11867484623) ^ 25869 = (5 : ZMod 11867484623) ^ (12934 + 12934 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 12934 * (5 : ZMod 11867484623) ^ 12934) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 10441363852 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 11867484623) ^ 51738 = 2257736168 := by
        calc
          (5 : ZMod 11867484623) ^ 51738 = (5 : ZMod 11867484623) ^ (25869 + 25869) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 25869 * (5 : ZMod 11867484623) ^ 25869 := by rw [pow_add]
          _ = 2257736168 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 11867484623) ^ 103476 = 6069931752 := by
        calc
          (5 : ZMod 11867484623) ^ 103476 = (5 : ZMod 11867484623) ^ (51738 + 51738) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 51738 * (5 : ZMod 11867484623) ^ 51738 := by rw [pow_add]
          _ = 6069931752 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 11867484623) ^ 206952 = 5495618349 := by
        calc
          (5 : ZMod 11867484623) ^ 206952 = (5 : ZMod 11867484623) ^ (103476 + 103476) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 103476 * (5 : ZMod 11867484623) ^ 103476 := by rw [pow_add]
          _ = 5495618349 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 11867484623) ^ 413905 = 11629604351 := by
        calc
          (5 : ZMod 11867484623) ^ 413905 = (5 : ZMod 11867484623) ^ (206952 + 206952 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 206952 * (5 : ZMod 11867484623) ^ 206952) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 11629604351 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 11867484623) ^ 827810 = 8928020464 := by
        calc
          (5 : ZMod 11867484623) ^ 827810 = (5 : ZMod 11867484623) ^ (413905 + 413905) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 413905 * (5 : ZMod 11867484623) ^ 413905 := by rw [pow_add]
          _ = 8928020464 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 11867484623) ^ 1655620 = 9574586449 := by
        calc
          (5 : ZMod 11867484623) ^ 1655620 = (5 : ZMod 11867484623) ^ (827810 + 827810) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 827810 * (5 : ZMod 11867484623) ^ 827810 := by rw [pow_add]
          _ = 9574586449 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 11867484623) ^ 3311240 = 525417328 := by
        calc
          (5 : ZMod 11867484623) ^ 3311240 = (5 : ZMod 11867484623) ^ (1655620 + 1655620) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 1655620 * (5 : ZMod 11867484623) ^ 1655620 := by rw [pow_add]
          _ = 525417328 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 11867484623) ^ 6622480 = 6862440035 := by
        calc
          (5 : ZMod 11867484623) ^ 6622480 = (5 : ZMod 11867484623) ^ (3311240 + 3311240) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 3311240 * (5 : ZMod 11867484623) ^ 3311240 := by rw [pow_add]
          _ = 6862440035 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 11867484623) ^ 13244960 = 3467406796 := by
        calc
          (5 : ZMod 11867484623) ^ 13244960 = (5 : ZMod 11867484623) ^ (6622480 + 6622480) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 6622480 * (5 : ZMod 11867484623) ^ 6622480 := by rw [pow_add]
          _ = 3467406796 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 11867484623) ^ 26489921 = 1627167900 := by
        calc
          (5 : ZMod 11867484623) ^ 26489921 = (5 : ZMod 11867484623) ^ (13244960 + 13244960 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 13244960 * (5 : ZMod 11867484623) ^ 13244960) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 1627167900 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 11867484623) ^ 52979842 = 1072861541 := by
        calc
          (5 : ZMod 11867484623) ^ 52979842 = (5 : ZMod 11867484623) ^ (26489921 + 26489921) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 26489921 * (5 : ZMod 11867484623) ^ 26489921 := by rw [pow_add]
          _ = 1072861541 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 11867484623) ^ 105959684 = 7325514072 := by
        calc
          (5 : ZMod 11867484623) ^ 105959684 = (5 : ZMod 11867484623) ^ (52979842 + 52979842) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 52979842 * (5 : ZMod 11867484623) ^ 52979842 := by rw [pow_add]
          _ = 7325514072 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 11867484623) ^ 211919368 = 6766630639 := by
        calc
          (5 : ZMod 11867484623) ^ 211919368 = (5 : ZMod 11867484623) ^ (105959684 + 105959684) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 105959684 * (5 : ZMod 11867484623) ^ 105959684 := by rw [pow_add]
          _ = 6766630639 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 11867484623) ^ 423838736 = 2296098834 := by
        calc
          (5 : ZMod 11867484623) ^ 423838736 = (5 : ZMod 11867484623) ^ (211919368 + 211919368) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 211919368 * (5 : ZMod 11867484623) ^ 211919368 := by rw [pow_add]
          _ = 2296098834 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 11867484623) ^ 847677473 = 6184602437 := by
        calc
          (5 : ZMod 11867484623) ^ 847677473 = (5 : ZMod 11867484623) ^ (423838736 + 423838736 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 423838736 * (5 : ZMod 11867484623) ^ 423838736) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 6184602437 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 11867484623) ^ 1695354946 = 3013779490 := by
        calc
          (5 : ZMod 11867484623) ^ 1695354946 = (5 : ZMod 11867484623) ^ (847677473 + 847677473) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 847677473 * (5 : ZMod 11867484623) ^ 847677473 := by rw [pow_add]
          _ = 3013779490 := by rw [factor_1_29]; decide
      change (5 : ZMod 11867484623) ^ 1695354946 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (5 : ZMod 11867484623) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 11867484623) ^ 2 = 25 := by
        calc
          (5 : ZMod 11867484623) ^ 2 = (5 : ZMod 11867484623) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 1 * (5 : ZMod 11867484623) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 11867484623) ^ 4 = 625 := by
        calc
          (5 : ZMod 11867484623) ^ 4 = (5 : ZMod 11867484623) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 2 * (5 : ZMod 11867484623) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 11867484623) ^ 8 = 390625 := by
        calc
          (5 : ZMod 11867484623) ^ 8 = (5 : ZMod 11867484623) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 4 * (5 : ZMod 11867484623) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 11867484623) ^ 17 = 3420437253 := by
        calc
          (5 : ZMod 11867484623) ^ 17 = (5 : ZMod 11867484623) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 8 * (5 : ZMod 11867484623) ^ 8) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 3420437253 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 11867484623) ^ 34 = 6154521200 := by
        calc
          (5 : ZMod 11867484623) ^ 34 = (5 : ZMod 11867484623) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 17 * (5 : ZMod 11867484623) ^ 17 := by rw [pow_add]
          _ = 6154521200 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 11867484623) ^ 69 = 4910593440 := by
        calc
          (5 : ZMod 11867484623) ^ 69 = (5 : ZMod 11867484623) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 34 * (5 : ZMod 11867484623) ^ 34) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 4910593440 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 11867484623) ^ 139 = 8221937446 := by
        calc
          (5 : ZMod 11867484623) ^ 139 = (5 : ZMod 11867484623) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 69 * (5 : ZMod 11867484623) ^ 69) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 8221937446 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 11867484623) ^ 278 = 3017745108 := by
        calc
          (5 : ZMod 11867484623) ^ 278 = (5 : ZMod 11867484623) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 139 * (5 : ZMod 11867484623) ^ 139 := by rw [pow_add]
          _ = 3017745108 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 11867484623) ^ 557 = 6996476602 := by
        calc
          (5 : ZMod 11867484623) ^ 557 = (5 : ZMod 11867484623) ^ (278 + 278 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 278 * (5 : ZMod 11867484623) ^ 278) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 6996476602 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 11867484623) ^ 1115 = 7189821972 := by
        calc
          (5 : ZMod 11867484623) ^ 1115 = (5 : ZMod 11867484623) ^ (557 + 557 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 557 * (5 : ZMod 11867484623) ^ 557) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 7189821972 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 11867484623) ^ 2230 = 10496245918 := by
        calc
          (5 : ZMod 11867484623) ^ 2230 = (5 : ZMod 11867484623) ^ (1115 + 1115) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 1115 * (5 : ZMod 11867484623) ^ 1115 := by rw [pow_add]
          _ = 10496245918 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 11867484623) ^ 4460 = 841626683 := by
        calc
          (5 : ZMod 11867484623) ^ 4460 = (5 : ZMod 11867484623) ^ (2230 + 2230) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 2230 * (5 : ZMod 11867484623) ^ 2230 := by rw [pow_add]
          _ = 841626683 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 11867484623) ^ 8920 = 5048265518 := by
        calc
          (5 : ZMod 11867484623) ^ 8920 = (5 : ZMod 11867484623) ^ (4460 + 4460) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 4460 * (5 : ZMod 11867484623) ^ 4460 := by rw [pow_add]
          _ = 5048265518 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 11867484623) ^ 17840 = 4024643551 := by
        calc
          (5 : ZMod 11867484623) ^ 17840 = (5 : ZMod 11867484623) ^ (8920 + 8920) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 8920 * (5 : ZMod 11867484623) ^ 8920 := by rw [pow_add]
          _ = 4024643551 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 11867484623) ^ 35680 = 11070155142 := by
        calc
          (5 : ZMod 11867484623) ^ 35680 = (5 : ZMod 11867484623) ^ (17840 + 17840) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 17840 * (5 : ZMod 11867484623) ^ 17840 := by rw [pow_add]
          _ = 11070155142 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 11867484623) ^ 71360 = 9423731455 := by
        calc
          (5 : ZMod 11867484623) ^ 71360 = (5 : ZMod 11867484623) ^ (35680 + 35680) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 35680 * (5 : ZMod 11867484623) ^ 35680 := by rw [pow_add]
          _ = 9423731455 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 11867484623) ^ 142720 = 6987692955 := by
        calc
          (5 : ZMod 11867484623) ^ 142720 = (5 : ZMod 11867484623) ^ (71360 + 71360) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 71360 * (5 : ZMod 11867484623) ^ 71360 := by rw [pow_add]
          _ = 6987692955 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 11867484623) ^ 285440 = 9060579217 := by
        calc
          (5 : ZMod 11867484623) ^ 285440 = (5 : ZMod 11867484623) ^ (142720 + 142720) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 142720 * (5 : ZMod 11867484623) ^ 142720 := by rw [pow_add]
          _ = 9060579217 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 11867484623) ^ 570881 = 6125822882 := by
        calc
          (5 : ZMod 11867484623) ^ 570881 = (5 : ZMod 11867484623) ^ (285440 + 285440 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 285440 * (5 : ZMod 11867484623) ^ 285440) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 6125822882 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 11867484623) ^ 1141763 = 10820959234 := by
        calc
          (5 : ZMod 11867484623) ^ 1141763 = (5 : ZMod 11867484623) ^ (570881 + 570881 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 570881 * (5 : ZMod 11867484623) ^ 570881) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 10820959234 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 11867484623) ^ 2283526 = 5694876711 := by
        calc
          (5 : ZMod 11867484623) ^ 2283526 = (5 : ZMod 11867484623) ^ (1141763 + 1141763) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 1141763 * (5 : ZMod 11867484623) ^ 1141763 := by rw [pow_add]
          _ = 5694876711 := by rw [factor_2_20]; decide
      change (5 : ZMod 11867484623) ^ 2283526 ≠ 1
      rw [factor_2_21]
      decide
    ·
      have factor_3_0 : (5 : ZMod 11867484623) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 11867484623) ^ 2 = 25 := by
        calc
          (5 : ZMod 11867484623) ^ 2 = (5 : ZMod 11867484623) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 1 * (5 : ZMod 11867484623) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 11867484623) ^ 4 = 625 := by
        calc
          (5 : ZMod 11867484623) ^ 4 = (5 : ZMod 11867484623) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 2 * (5 : ZMod 11867484623) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 11867484623) ^ 8 = 390625 := by
        calc
          (5 : ZMod 11867484623) ^ 8 = (5 : ZMod 11867484623) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 4 * (5 : ZMod 11867484623) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 11867484623) ^ 17 = 3420437253 := by
        calc
          (5 : ZMod 11867484623) ^ 17 = (5 : ZMod 11867484623) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 8 * (5 : ZMod 11867484623) ^ 8) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 3420437253 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 11867484623) ^ 35 = 7037636754 := by
        calc
          (5 : ZMod 11867484623) ^ 35 = (5 : ZMod 11867484623) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 17 * (5 : ZMod 11867484623) ^ 17) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 7037636754 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 11867484623) ^ 71 = 4089989770 := by
        calc
          (5 : ZMod 11867484623) ^ 71 = (5 : ZMod 11867484623) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 35 * (5 : ZMod 11867484623) ^ 35) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 4089989770 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 11867484623) ^ 142 = 7138503172 := by
        calc
          (5 : ZMod 11867484623) ^ 142 = (5 : ZMod 11867484623) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 71 * (5 : ZMod 11867484623) ^ 71 := by rw [pow_add]
          _ = 7138503172 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 11867484623) ^ 284 = 2750905321 := by
        calc
          (5 : ZMod 11867484623) ^ 284 = (5 : ZMod 11867484623) ^ (142 + 142) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 142 * (5 : ZMod 11867484623) ^ 142 := by rw [pow_add]
          _ = 2750905321 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 11867484623) ^ 568 = 4546463875 := by
        calc
          (5 : ZMod 11867484623) ^ 568 = (5 : ZMod 11867484623) ^ (284 + 284) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 284 * (5 : ZMod 11867484623) ^ 284 := by rw [pow_add]
          _ = 4546463875 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 11867484623) ^ 1136 = 2886805002 := by
        calc
          (5 : ZMod 11867484623) ^ 1136 = (5 : ZMod 11867484623) ^ (568 + 568) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 568 * (5 : ZMod 11867484623) ^ 568 := by rw [pow_add]
          _ = 2886805002 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 11867484623) ^ 2273 = 34498325 := by
        calc
          (5 : ZMod 11867484623) ^ 2273 = (5 : ZMod 11867484623) ^ (1136 + 1136 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 1136 * (5 : ZMod 11867484623) ^ 1136) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 34498325 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 11867484623) ^ 4547 = 6794455727 := by
        calc
          (5 : ZMod 11867484623) ^ 4547 = (5 : ZMod 11867484623) ^ (2273 + 2273 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 2273 * (5 : ZMod 11867484623) ^ 2273) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 6794455727 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 11867484623) ^ 9094 = 1407587272 := by
        calc
          (5 : ZMod 11867484623) ^ 9094 = (5 : ZMod 11867484623) ^ (4547 + 4547) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 4547 * (5 : ZMod 11867484623) ^ 4547 := by rw [pow_add]
          _ = 1407587272 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 11867484623) ^ 18189 = 889624673 := by
        calc
          (5 : ZMod 11867484623) ^ 18189 = (5 : ZMod 11867484623) ^ (9094 + 9094 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 9094 * (5 : ZMod 11867484623) ^ 9094) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 889624673 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 11867484623) ^ 36379 = 794468305 := by
        calc
          (5 : ZMod 11867484623) ^ 36379 = (5 : ZMod 11867484623) ^ (18189 + 18189 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = ((5 : ZMod 11867484623) ^ 18189 * (5 : ZMod 11867484623) ^ 18189) * (5 : ZMod 11867484623) := by rw [pow_succ, pow_add]
          _ = 794468305 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 11867484623) ^ 72758 = 4110313075 := by
        calc
          (5 : ZMod 11867484623) ^ 72758 = (5 : ZMod 11867484623) ^ (36379 + 36379) :=
            congrArg (fun n : ℕ => (5 : ZMod 11867484623) ^ n) (by norm_num)
          _ = (5 : ZMod 11867484623) ^ 36379 * (5 : ZMod 11867484623) ^ 36379 := by rw [pow_add]
          _ = 4110313075 := by rw [factor_3_15]; decide
      change (5 : ZMod 11867484623) ^ 72758 ≠ 1
      rw [factor_3_16]
      decide

#print axioms prime_lucas_11867484623

end TotientTailPeriodKiller
end Erdos249257
