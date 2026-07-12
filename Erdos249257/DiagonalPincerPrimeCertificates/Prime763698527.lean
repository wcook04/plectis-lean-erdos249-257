import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_763698527 : Nat.Prime 763698527 := by
  apply lucas_primality 763698527 (5 : ZMod 763698527)
  ·
      have fermat_0 : (5 : ZMod 763698527) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 763698527) ^ 2 = 25 := by
        calc
          (5 : ZMod 763698527) ^ 2 = (5 : ZMod 763698527) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 1 * (5 : ZMod 763698527) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 763698527) ^ 5 = 3125 := by
        calc
          (5 : ZMod 763698527) ^ 5 = (5 : ZMod 763698527) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 2 * (5 : ZMod 763698527) ^ 2) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 763698527) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 763698527) ^ 11 = (5 : ZMod 763698527) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 5 * (5 : ZMod 763698527) ^ 5) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 763698527) ^ 22 = 705464014 := by
        calc
          (5 : ZMod 763698527) ^ 22 = (5 : ZMod 763698527) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 11 * (5 : ZMod 763698527) ^ 11 := by rw [pow_add]
          _ = 705464014 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 763698527) ^ 45 = 280850098 := by
        calc
          (5 : ZMod 763698527) ^ 45 = (5 : ZMod 763698527) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 22 * (5 : ZMod 763698527) ^ 22) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 280850098 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 763698527) ^ 91 = 597073616 := by
        calc
          (5 : ZMod 763698527) ^ 91 = (5 : ZMod 763698527) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 45 * (5 : ZMod 763698527) ^ 45) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 597073616 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 763698527) ^ 182 = 431002542 := by
        calc
          (5 : ZMod 763698527) ^ 182 = (5 : ZMod 763698527) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 91 * (5 : ZMod 763698527) ^ 91 := by rw [pow_add]
          _ = 431002542 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 763698527) ^ 364 = 681220724 := by
        calc
          (5 : ZMod 763698527) ^ 364 = (5 : ZMod 763698527) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 182 * (5 : ZMod 763698527) ^ 182 := by rw [pow_add]
          _ = 681220724 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 763698527) ^ 728 = 635843834 := by
        calc
          (5 : ZMod 763698527) ^ 728 = (5 : ZMod 763698527) ^ (364 + 364) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 364 * (5 : ZMod 763698527) ^ 364 := by rw [pow_add]
          _ = 635843834 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 763698527) ^ 1456 = 654409379 := by
        calc
          (5 : ZMod 763698527) ^ 1456 = (5 : ZMod 763698527) ^ (728 + 728) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 728 * (5 : ZMod 763698527) ^ 728 := by rw [pow_add]
          _ = 654409379 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 763698527) ^ 2913 = 702302511 := by
        calc
          (5 : ZMod 763698527) ^ 2913 = (5 : ZMod 763698527) ^ (1456 + 1456 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 1456 * (5 : ZMod 763698527) ^ 1456) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 702302511 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 763698527) ^ 5826 = 717818913 := by
        calc
          (5 : ZMod 763698527) ^ 5826 = (5 : ZMod 763698527) ^ (2913 + 2913) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 2913 * (5 : ZMod 763698527) ^ 2913 := by rw [pow_add]
          _ = 717818913 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 763698527) ^ 11653 = 544476148 := by
        calc
          (5 : ZMod 763698527) ^ 11653 = (5 : ZMod 763698527) ^ (5826 + 5826 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 5826 * (5 : ZMod 763698527) ^ 5826) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 544476148 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 763698527) ^ 23306 = 585092940 := by
        calc
          (5 : ZMod 763698527) ^ 23306 = (5 : ZMod 763698527) ^ (11653 + 11653) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 11653 * (5 : ZMod 763698527) ^ 11653 := by rw [pow_add]
          _ = 585092940 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 763698527) ^ 46612 = 176641592 := by
        calc
          (5 : ZMod 763698527) ^ 46612 = (5 : ZMod 763698527) ^ (23306 + 23306) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 23306 * (5 : ZMod 763698527) ^ 23306 := by rw [pow_add]
          _ = 176641592 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 763698527) ^ 93224 = 12110782 := by
        calc
          (5 : ZMod 763698527) ^ 93224 = (5 : ZMod 763698527) ^ (46612 + 46612) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 46612 * (5 : ZMod 763698527) ^ 46612 := by rw [pow_add]
          _ = 12110782 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 763698527) ^ 186449 = 709830911 := by
        calc
          (5 : ZMod 763698527) ^ 186449 = (5 : ZMod 763698527) ^ (93224 + 93224 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 93224 * (5 : ZMod 763698527) ^ 93224) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 709830911 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 763698527) ^ 372899 = 754391410 := by
        calc
          (5 : ZMod 763698527) ^ 372899 = (5 : ZMod 763698527) ^ (186449 + 186449 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 186449 * (5 : ZMod 763698527) ^ 186449) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 754391410 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 763698527) ^ 745799 = 370832097 := by
        calc
          (5 : ZMod 763698527) ^ 745799 = (5 : ZMod 763698527) ^ (372899 + 372899 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 372899 * (5 : ZMod 763698527) ^ 372899) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 370832097 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 763698527) ^ 1491598 = 486923136 := by
        calc
          (5 : ZMod 763698527) ^ 1491598 = (5 : ZMod 763698527) ^ (745799 + 745799) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 745799 * (5 : ZMod 763698527) ^ 745799 := by rw [pow_add]
          _ = 486923136 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 763698527) ^ 2983197 = 378647811 := by
        calc
          (5 : ZMod 763698527) ^ 2983197 = (5 : ZMod 763698527) ^ (1491598 + 1491598 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 1491598 * (5 : ZMod 763698527) ^ 1491598) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 378647811 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 763698527) ^ 5966394 = 654802048 := by
        calc
          (5 : ZMod 763698527) ^ 5966394 = (5 : ZMod 763698527) ^ (2983197 + 2983197) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 2983197 * (5 : ZMod 763698527) ^ 2983197 := by rw [pow_add]
          _ = 654802048 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 763698527) ^ 11932789 = 56526509 := by
        calc
          (5 : ZMod 763698527) ^ 11932789 = (5 : ZMod 763698527) ^ (5966394 + 5966394 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 5966394 * (5 : ZMod 763698527) ^ 5966394) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 56526509 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 763698527) ^ 23865578 = 315626511 := by
        calc
          (5 : ZMod 763698527) ^ 23865578 = (5 : ZMod 763698527) ^ (11932789 + 11932789) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 11932789 * (5 : ZMod 763698527) ^ 11932789 := by rw [pow_add]
          _ = 315626511 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 763698527) ^ 47731157 = 176390587 := by
        calc
          (5 : ZMod 763698527) ^ 47731157 = (5 : ZMod 763698527) ^ (23865578 + 23865578 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 23865578 * (5 : ZMod 763698527) ^ 23865578) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 176390587 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 763698527) ^ 95462315 = 132734647 := by
        calc
          (5 : ZMod 763698527) ^ 95462315 = (5 : ZMod 763698527) ^ (47731157 + 47731157 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 47731157 * (5 : ZMod 763698527) ^ 47731157) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 132734647 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 763698527) ^ 190924631 = 697350376 := by
        calc
          (5 : ZMod 763698527) ^ 190924631 = (5 : ZMod 763698527) ^ (95462315 + 95462315 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 95462315 * (5 : ZMod 763698527) ^ 95462315) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 697350376 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 763698527) ^ 381849263 = 763698526 := by
        calc
          (5 : ZMod 763698527) ^ 381849263 = (5 : ZMod 763698527) ^ (190924631 + 190924631 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 190924631 * (5 : ZMod 763698527) ^ 190924631) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 763698526 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 763698527) ^ 763698526 = 1 := by
        calc
          (5 : ZMod 763698527) ^ 763698526 = (5 : ZMod 763698527) ^ (381849263 + 381849263) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 381849263 * (5 : ZMod 763698527) ^ 381849263 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (139, 1), (2747117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (139, 1), (2747117, 1)] : List FactorBlock).map factorBlockValue).prod = 763698527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 763698527) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 763698527) ^ 2 = 25 := by
        calc
          (5 : ZMod 763698527) ^ 2 = (5 : ZMod 763698527) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 1 * (5 : ZMod 763698527) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 763698527) ^ 5 = 3125 := by
        calc
          (5 : ZMod 763698527) ^ 5 = (5 : ZMod 763698527) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 2 * (5 : ZMod 763698527) ^ 2) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 763698527) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 763698527) ^ 11 = (5 : ZMod 763698527) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 5 * (5 : ZMod 763698527) ^ 5) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 763698527) ^ 22 = 705464014 := by
        calc
          (5 : ZMod 763698527) ^ 22 = (5 : ZMod 763698527) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 11 * (5 : ZMod 763698527) ^ 11 := by rw [pow_add]
          _ = 705464014 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 763698527) ^ 45 = 280850098 := by
        calc
          (5 : ZMod 763698527) ^ 45 = (5 : ZMod 763698527) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 22 * (5 : ZMod 763698527) ^ 22) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 280850098 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 763698527) ^ 91 = 597073616 := by
        calc
          (5 : ZMod 763698527) ^ 91 = (5 : ZMod 763698527) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 45 * (5 : ZMod 763698527) ^ 45) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 597073616 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 763698527) ^ 182 = 431002542 := by
        calc
          (5 : ZMod 763698527) ^ 182 = (5 : ZMod 763698527) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 91 * (5 : ZMod 763698527) ^ 91 := by rw [pow_add]
          _ = 431002542 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 763698527) ^ 364 = 681220724 := by
        calc
          (5 : ZMod 763698527) ^ 364 = (5 : ZMod 763698527) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 182 * (5 : ZMod 763698527) ^ 182 := by rw [pow_add]
          _ = 681220724 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 763698527) ^ 728 = 635843834 := by
        calc
          (5 : ZMod 763698527) ^ 728 = (5 : ZMod 763698527) ^ (364 + 364) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 364 * (5 : ZMod 763698527) ^ 364 := by rw [pow_add]
          _ = 635843834 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 763698527) ^ 1456 = 654409379 := by
        calc
          (5 : ZMod 763698527) ^ 1456 = (5 : ZMod 763698527) ^ (728 + 728) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 728 * (5 : ZMod 763698527) ^ 728 := by rw [pow_add]
          _ = 654409379 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 763698527) ^ 2913 = 702302511 := by
        calc
          (5 : ZMod 763698527) ^ 2913 = (5 : ZMod 763698527) ^ (1456 + 1456 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 1456 * (5 : ZMod 763698527) ^ 1456) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 702302511 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 763698527) ^ 5826 = 717818913 := by
        calc
          (5 : ZMod 763698527) ^ 5826 = (5 : ZMod 763698527) ^ (2913 + 2913) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 2913 * (5 : ZMod 763698527) ^ 2913 := by rw [pow_add]
          _ = 717818913 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 763698527) ^ 11653 = 544476148 := by
        calc
          (5 : ZMod 763698527) ^ 11653 = (5 : ZMod 763698527) ^ (5826 + 5826 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 5826 * (5 : ZMod 763698527) ^ 5826) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 544476148 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 763698527) ^ 23306 = 585092940 := by
        calc
          (5 : ZMod 763698527) ^ 23306 = (5 : ZMod 763698527) ^ (11653 + 11653) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 11653 * (5 : ZMod 763698527) ^ 11653 := by rw [pow_add]
          _ = 585092940 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 763698527) ^ 46612 = 176641592 := by
        calc
          (5 : ZMod 763698527) ^ 46612 = (5 : ZMod 763698527) ^ (23306 + 23306) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 23306 * (5 : ZMod 763698527) ^ 23306 := by rw [pow_add]
          _ = 176641592 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 763698527) ^ 93224 = 12110782 := by
        calc
          (5 : ZMod 763698527) ^ 93224 = (5 : ZMod 763698527) ^ (46612 + 46612) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 46612 * (5 : ZMod 763698527) ^ 46612 := by rw [pow_add]
          _ = 12110782 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 763698527) ^ 186449 = 709830911 := by
        calc
          (5 : ZMod 763698527) ^ 186449 = (5 : ZMod 763698527) ^ (93224 + 93224 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 93224 * (5 : ZMod 763698527) ^ 93224) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 709830911 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 763698527) ^ 372899 = 754391410 := by
        calc
          (5 : ZMod 763698527) ^ 372899 = (5 : ZMod 763698527) ^ (186449 + 186449 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 186449 * (5 : ZMod 763698527) ^ 186449) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 754391410 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 763698527) ^ 745799 = 370832097 := by
        calc
          (5 : ZMod 763698527) ^ 745799 = (5 : ZMod 763698527) ^ (372899 + 372899 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 372899 * (5 : ZMod 763698527) ^ 372899) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 370832097 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 763698527) ^ 1491598 = 486923136 := by
        calc
          (5 : ZMod 763698527) ^ 1491598 = (5 : ZMod 763698527) ^ (745799 + 745799) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 745799 * (5 : ZMod 763698527) ^ 745799 := by rw [pow_add]
          _ = 486923136 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 763698527) ^ 2983197 = 378647811 := by
        calc
          (5 : ZMod 763698527) ^ 2983197 = (5 : ZMod 763698527) ^ (1491598 + 1491598 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 1491598 * (5 : ZMod 763698527) ^ 1491598) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 378647811 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 763698527) ^ 5966394 = 654802048 := by
        calc
          (5 : ZMod 763698527) ^ 5966394 = (5 : ZMod 763698527) ^ (2983197 + 2983197) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 2983197 * (5 : ZMod 763698527) ^ 2983197 := by rw [pow_add]
          _ = 654802048 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 763698527) ^ 11932789 = 56526509 := by
        calc
          (5 : ZMod 763698527) ^ 11932789 = (5 : ZMod 763698527) ^ (5966394 + 5966394 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 5966394 * (5 : ZMod 763698527) ^ 5966394) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 56526509 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 763698527) ^ 23865578 = 315626511 := by
        calc
          (5 : ZMod 763698527) ^ 23865578 = (5 : ZMod 763698527) ^ (11932789 + 11932789) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 11932789 * (5 : ZMod 763698527) ^ 11932789 := by rw [pow_add]
          _ = 315626511 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 763698527) ^ 47731157 = 176390587 := by
        calc
          (5 : ZMod 763698527) ^ 47731157 = (5 : ZMod 763698527) ^ (23865578 + 23865578 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 23865578 * (5 : ZMod 763698527) ^ 23865578) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 176390587 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 763698527) ^ 95462315 = 132734647 := by
        calc
          (5 : ZMod 763698527) ^ 95462315 = (5 : ZMod 763698527) ^ (47731157 + 47731157 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 47731157 * (5 : ZMod 763698527) ^ 47731157) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 132734647 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 763698527) ^ 190924631 = 697350376 := by
        calc
          (5 : ZMod 763698527) ^ 190924631 = (5 : ZMod 763698527) ^ (95462315 + 95462315 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 95462315 * (5 : ZMod 763698527) ^ 95462315) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 697350376 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 763698527) ^ 381849263 = 763698526 := by
        calc
          (5 : ZMod 763698527) ^ 381849263 = (5 : ZMod 763698527) ^ (190924631 + 190924631 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 190924631 * (5 : ZMod 763698527) ^ 190924631) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 763698526 := by rw [factor_0_27]; decide
      change (5 : ZMod 763698527) ^ 381849263 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (5 : ZMod 763698527) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 763698527) ^ 2 = 25 := by
        calc
          (5 : ZMod 763698527) ^ 2 = (5 : ZMod 763698527) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 1 * (5 : ZMod 763698527) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 763698527) ^ 5 = 3125 := by
        calc
          (5 : ZMod 763698527) ^ 5 = (5 : ZMod 763698527) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 2 * (5 : ZMod 763698527) ^ 2) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 763698527) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 763698527) ^ 10 = (5 : ZMod 763698527) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 5 * (5 : ZMod 763698527) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 763698527) ^ 20 = 578081500 := by
        calc
          (5 : ZMod 763698527) ^ 20 = (5 : ZMod 763698527) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 10 * (5 : ZMod 763698527) ^ 10 := by rw [pow_add]
          _ = 578081500 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 763698527) ^ 41 = 459890394 := by
        calc
          (5 : ZMod 763698527) ^ 41 = (5 : ZMod 763698527) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 20 * (5 : ZMod 763698527) ^ 20) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 459890394 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 763698527) ^ 83 = 397940026 := by
        calc
          (5 : ZMod 763698527) ^ 83 = (5 : ZMod 763698527) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 41 * (5 : ZMod 763698527) ^ 41) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 397940026 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 763698527) ^ 167 = 441897842 := by
        calc
          (5 : ZMod 763698527) ^ 167 = (5 : ZMod 763698527) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 83 * (5 : ZMod 763698527) ^ 83) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 441897842 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 763698527) ^ 335 = 247706786 := by
        calc
          (5 : ZMod 763698527) ^ 335 = (5 : ZMod 763698527) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 167 * (5 : ZMod 763698527) ^ 167) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 247706786 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 763698527) ^ 670 = 99772271 := by
        calc
          (5 : ZMod 763698527) ^ 670 = (5 : ZMod 763698527) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 335 * (5 : ZMod 763698527) ^ 335 := by rw [pow_add]
          _ = 99772271 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 763698527) ^ 1341 = 92727989 := by
        calc
          (5 : ZMod 763698527) ^ 1341 = (5 : ZMod 763698527) ^ (670 + 670 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 670 * (5 : ZMod 763698527) ^ 670) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 92727989 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 763698527) ^ 2682 = 519586702 := by
        calc
          (5 : ZMod 763698527) ^ 2682 = (5 : ZMod 763698527) ^ (1341 + 1341) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 1341 * (5 : ZMod 763698527) ^ 1341 := by rw [pow_add]
          _ = 519586702 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 763698527) ^ 5365 = 382362346 := by
        calc
          (5 : ZMod 763698527) ^ 5365 = (5 : ZMod 763698527) ^ (2682 + 2682 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 2682 * (5 : ZMod 763698527) ^ 2682) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 382362346 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 763698527) ^ 10730 = 732283150 := by
        calc
          (5 : ZMod 763698527) ^ 10730 = (5 : ZMod 763698527) ^ (5365 + 5365) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 5365 * (5 : ZMod 763698527) ^ 5365 := by rw [pow_add]
          _ = 732283150 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 763698527) ^ 21461 = 692432469 := by
        calc
          (5 : ZMod 763698527) ^ 21461 = (5 : ZMod 763698527) ^ (10730 + 10730 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 10730 * (5 : ZMod 763698527) ^ 10730) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 692432469 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 763698527) ^ 42923 = 660212622 := by
        calc
          (5 : ZMod 763698527) ^ 42923 = (5 : ZMod 763698527) ^ (21461 + 21461 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 21461 * (5 : ZMod 763698527) ^ 21461) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 660212622 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 763698527) ^ 85847 = 16225231 := by
        calc
          (5 : ZMod 763698527) ^ 85847 = (5 : ZMod 763698527) ^ (42923 + 42923 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 42923 * (5 : ZMod 763698527) ^ 42923) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 16225231 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 763698527) ^ 171694 = 546967083 := by
        calc
          (5 : ZMod 763698527) ^ 171694 = (5 : ZMod 763698527) ^ (85847 + 85847) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 85847 * (5 : ZMod 763698527) ^ 85847 := by rw [pow_add]
          _ = 546967083 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 763698527) ^ 343389 = 289117332 := by
        calc
          (5 : ZMod 763698527) ^ 343389 = (5 : ZMod 763698527) ^ (171694 + 171694 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 171694 * (5 : ZMod 763698527) ^ 171694) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 289117332 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 763698527) ^ 686779 = 551596668 := by
        calc
          (5 : ZMod 763698527) ^ 686779 = (5 : ZMod 763698527) ^ (343389 + 343389 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 343389 * (5 : ZMod 763698527) ^ 343389) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 551596668 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 763698527) ^ 1373558 = 296884557 := by
        calc
          (5 : ZMod 763698527) ^ 1373558 = (5 : ZMod 763698527) ^ (686779 + 686779) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 686779 * (5 : ZMod 763698527) ^ 686779 := by rw [pow_add]
          _ = 296884557 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 763698527) ^ 2747117 = 418002422 := by
        calc
          (5 : ZMod 763698527) ^ 2747117 = (5 : ZMod 763698527) ^ (1373558 + 1373558 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 1373558 * (5 : ZMod 763698527) ^ 1373558) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 418002422 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 763698527) ^ 5494234 = 123953429 := by
        calc
          (5 : ZMod 763698527) ^ 5494234 = (5 : ZMod 763698527) ^ (2747117 + 2747117) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 2747117 * (5 : ZMod 763698527) ^ 2747117 := by rw [pow_add]
          _ = 123953429 := by rw [factor_1_21]; decide
      change (5 : ZMod 763698527) ^ 5494234 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (5 : ZMod 763698527) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 763698527) ^ 2 = 25 := by
        calc
          (5 : ZMod 763698527) ^ 2 = (5 : ZMod 763698527) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 1 * (5 : ZMod 763698527) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 763698527) ^ 4 = 625 := by
        calc
          (5 : ZMod 763698527) ^ 4 = (5 : ZMod 763698527) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 2 * (5 : ZMod 763698527) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 763698527) ^ 8 = 390625 := by
        calc
          (5 : ZMod 763698527) ^ 8 = (5 : ZMod 763698527) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 4 * (5 : ZMod 763698527) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 763698527) ^ 17 = 4624652 := by
        calc
          (5 : ZMod 763698527) ^ 17 = (5 : ZMod 763698527) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 8 * (5 : ZMod 763698527) ^ 8) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 4624652 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 763698527) ^ 34 = 28872469 := by
        calc
          (5 : ZMod 763698527) ^ 34 = (5 : ZMod 763698527) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 17 * (5 : ZMod 763698527) ^ 17 := by rw [pow_add]
          _ = 28872469 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 763698527) ^ 69 = 311486799 := by
        calc
          (5 : ZMod 763698527) ^ 69 = (5 : ZMod 763698527) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 34 * (5 : ZMod 763698527) ^ 34) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 311486799 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 763698527) ^ 139 = 237241455 := by
        calc
          (5 : ZMod 763698527) ^ 139 = (5 : ZMod 763698527) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = ((5 : ZMod 763698527) ^ 69 * (5 : ZMod 763698527) ^ 69) * (5 : ZMod 763698527) := by rw [pow_succ, pow_add]
          _ = 237241455 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 763698527) ^ 278 = 290745987 := by
        calc
          (5 : ZMod 763698527) ^ 278 = (5 : ZMod 763698527) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (5 : ZMod 763698527) ^ n) (by norm_num)
          _ = (5 : ZMod 763698527) ^ 139 * (5 : ZMod 763698527) ^ 139 := by rw [pow_add]
          _ = 290745987 := by rw [factor_2_7]; decide
      change (5 : ZMod 763698527) ^ 278 ≠ 1
      rw [factor_2_8]
      decide

#print axioms prime_lucas_763698527

end TotientTailPeriodKiller
end Erdos249257
