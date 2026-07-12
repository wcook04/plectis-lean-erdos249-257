import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_836598263 : Nat.Prime 836598263 := by
  apply lucas_primality 836598263 (5 : ZMod 836598263)
  ·
      have fermat_0 : (5 : ZMod 836598263) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 836598263) ^ 3 = 125 := by
        calc
          (5 : ZMod 836598263) ^ 3 = (5 : ZMod 836598263) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 1 * (5 : ZMod 836598263) ^ 1) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 836598263) ^ 6 = 15625 := by
        calc
          (5 : ZMod 836598263) ^ 6 = (5 : ZMod 836598263) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 3 * (5 : ZMod 836598263) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 836598263) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 836598263) ^ 12 = (5 : ZMod 836598263) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 6 * (5 : ZMod 836598263) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 836598263) ^ 24 = 172849957 := by
        calc
          (5 : ZMod 836598263) ^ 24 = (5 : ZMod 836598263) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 12 * (5 : ZMod 836598263) ^ 12 := by rw [pow_add]
          _ = 172849957 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 836598263) ^ 49 = 708527095 := by
        calc
          (5 : ZMod 836598263) ^ 49 = (5 : ZMod 836598263) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 24 * (5 : ZMod 836598263) ^ 24) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 708527095 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 836598263) ^ 99 = 12870058 := by
        calc
          (5 : ZMod 836598263) ^ 99 = (5 : ZMod 836598263) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 49 * (5 : ZMod 836598263) ^ 49) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 12870058 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 836598263) ^ 199 = 677561707 := by
        calc
          (5 : ZMod 836598263) ^ 199 = (5 : ZMod 836598263) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 99 * (5 : ZMod 836598263) ^ 99) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 677561707 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 836598263) ^ 398 = 165344510 := by
        calc
          (5 : ZMod 836598263) ^ 398 = (5 : ZMod 836598263) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 199 * (5 : ZMod 836598263) ^ 199 := by rw [pow_add]
          _ = 165344510 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 836598263) ^ 797 = 150990871 := by
        calc
          (5 : ZMod 836598263) ^ 797 = (5 : ZMod 836598263) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 398 * (5 : ZMod 836598263) ^ 398) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 150990871 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 836598263) ^ 1595 = 610705145 := by
        calc
          (5 : ZMod 836598263) ^ 1595 = (5 : ZMod 836598263) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 797 * (5 : ZMod 836598263) ^ 797) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 610705145 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 836598263) ^ 3191 = 450848044 := by
        calc
          (5 : ZMod 836598263) ^ 3191 = (5 : ZMod 836598263) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 1595 * (5 : ZMod 836598263) ^ 1595) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 450848044 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 836598263) ^ 6382 = 684142594 := by
        calc
          (5 : ZMod 836598263) ^ 6382 = (5 : ZMod 836598263) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 3191 * (5 : ZMod 836598263) ^ 3191 := by rw [pow_add]
          _ = 684142594 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 836598263) ^ 12765 = 17574985 := by
        calc
          (5 : ZMod 836598263) ^ 12765 = (5 : ZMod 836598263) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 6382 * (5 : ZMod 836598263) ^ 6382) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 17574985 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 836598263) ^ 25530 = 489666258 := by
        calc
          (5 : ZMod 836598263) ^ 25530 = (5 : ZMod 836598263) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 12765 * (5 : ZMod 836598263) ^ 12765 := by rw [pow_add]
          _ = 489666258 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 836598263) ^ 51061 = 37551683 := by
        calc
          (5 : ZMod 836598263) ^ 51061 = (5 : ZMod 836598263) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 25530 * (5 : ZMod 836598263) ^ 25530) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 37551683 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 836598263) ^ 102123 = 123271143 := by
        calc
          (5 : ZMod 836598263) ^ 102123 = (5 : ZMod 836598263) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 51061 * (5 : ZMod 836598263) ^ 51061) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 123271143 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 836598263) ^ 204247 = 566734744 := by
        calc
          (5 : ZMod 836598263) ^ 204247 = (5 : ZMod 836598263) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 102123 * (5 : ZMod 836598263) ^ 102123) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 566734744 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 836598263) ^ 408495 = 211135115 := by
        calc
          (5 : ZMod 836598263) ^ 408495 = (5 : ZMod 836598263) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 204247 * (5 : ZMod 836598263) ^ 204247) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 211135115 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 836598263) ^ 816990 = 407096311 := by
        calc
          (5 : ZMod 836598263) ^ 816990 = (5 : ZMod 836598263) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 408495 * (5 : ZMod 836598263) ^ 408495 := by rw [pow_add]
          _ = 407096311 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 836598263) ^ 1633980 = 271282578 := by
        calc
          (5 : ZMod 836598263) ^ 1633980 = (5 : ZMod 836598263) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 816990 * (5 : ZMod 836598263) ^ 816990 := by rw [pow_add]
          _ = 271282578 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 836598263) ^ 3267961 = 254658866 := by
        calc
          (5 : ZMod 836598263) ^ 3267961 = (5 : ZMod 836598263) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 1633980 * (5 : ZMod 836598263) ^ 1633980) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 254658866 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 836598263) ^ 6535923 = 825487773 := by
        calc
          (5 : ZMod 836598263) ^ 6535923 = (5 : ZMod 836598263) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 3267961 * (5 : ZMod 836598263) ^ 3267961) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 825487773 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 836598263) ^ 13071847 = 349501779 := by
        calc
          (5 : ZMod 836598263) ^ 13071847 = (5 : ZMod 836598263) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 6535923 * (5 : ZMod 836598263) ^ 6535923) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 349501779 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 836598263) ^ 26143695 = 824800472 := by
        calc
          (5 : ZMod 836598263) ^ 26143695 = (5 : ZMod 836598263) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 13071847 * (5 : ZMod 836598263) ^ 13071847) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 824800472 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 836598263) ^ 52287391 = 38553121 := by
        calc
          (5 : ZMod 836598263) ^ 52287391 = (5 : ZMod 836598263) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 26143695 * (5 : ZMod 836598263) ^ 26143695) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 38553121 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 836598263) ^ 104574782 = 834881691 := by
        calc
          (5 : ZMod 836598263) ^ 104574782 = (5 : ZMod 836598263) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 52287391 * (5 : ZMod 836598263) ^ 52287391 := by rw [pow_add]
          _ = 834881691 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 836598263) ^ 209149565 = 601744490 := by
        calc
          (5 : ZMod 836598263) ^ 209149565 = (5 : ZMod 836598263) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 104574782 * (5 : ZMod 836598263) ^ 104574782) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 601744490 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 836598263) ^ 418299131 = 836598262 := by
        calc
          (5 : ZMod 836598263) ^ 418299131 = (5 : ZMod 836598263) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 209149565 * (5 : ZMod 836598263) ^ 209149565) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 836598262 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 836598263) ^ 836598262 = 1 := by
        calc
          (5 : ZMod 836598263) ^ 836598262 = (5 : ZMod 836598263) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 418299131 * (5 : ZMod 836598263) ^ 418299131 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (347, 1), (1205473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (347, 1), (1205473, 1)] : List FactorBlock).map factorBlockValue).prod = 836598263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 836598263) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 836598263) ^ 3 = 125 := by
        calc
          (5 : ZMod 836598263) ^ 3 = (5 : ZMod 836598263) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 1 * (5 : ZMod 836598263) ^ 1) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 836598263) ^ 6 = 15625 := by
        calc
          (5 : ZMod 836598263) ^ 6 = (5 : ZMod 836598263) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 3 * (5 : ZMod 836598263) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 836598263) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 836598263) ^ 12 = (5 : ZMod 836598263) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 6 * (5 : ZMod 836598263) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 836598263) ^ 24 = 172849957 := by
        calc
          (5 : ZMod 836598263) ^ 24 = (5 : ZMod 836598263) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 12 * (5 : ZMod 836598263) ^ 12 := by rw [pow_add]
          _ = 172849957 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 836598263) ^ 49 = 708527095 := by
        calc
          (5 : ZMod 836598263) ^ 49 = (5 : ZMod 836598263) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 24 * (5 : ZMod 836598263) ^ 24) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 708527095 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 836598263) ^ 99 = 12870058 := by
        calc
          (5 : ZMod 836598263) ^ 99 = (5 : ZMod 836598263) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 49 * (5 : ZMod 836598263) ^ 49) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 12870058 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 836598263) ^ 199 = 677561707 := by
        calc
          (5 : ZMod 836598263) ^ 199 = (5 : ZMod 836598263) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 99 * (5 : ZMod 836598263) ^ 99) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 677561707 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 836598263) ^ 398 = 165344510 := by
        calc
          (5 : ZMod 836598263) ^ 398 = (5 : ZMod 836598263) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 199 * (5 : ZMod 836598263) ^ 199 := by rw [pow_add]
          _ = 165344510 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 836598263) ^ 797 = 150990871 := by
        calc
          (5 : ZMod 836598263) ^ 797 = (5 : ZMod 836598263) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 398 * (5 : ZMod 836598263) ^ 398) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 150990871 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 836598263) ^ 1595 = 610705145 := by
        calc
          (5 : ZMod 836598263) ^ 1595 = (5 : ZMod 836598263) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 797 * (5 : ZMod 836598263) ^ 797) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 610705145 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 836598263) ^ 3191 = 450848044 := by
        calc
          (5 : ZMod 836598263) ^ 3191 = (5 : ZMod 836598263) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 1595 * (5 : ZMod 836598263) ^ 1595) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 450848044 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 836598263) ^ 6382 = 684142594 := by
        calc
          (5 : ZMod 836598263) ^ 6382 = (5 : ZMod 836598263) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 3191 * (5 : ZMod 836598263) ^ 3191 := by rw [pow_add]
          _ = 684142594 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 836598263) ^ 12765 = 17574985 := by
        calc
          (5 : ZMod 836598263) ^ 12765 = (5 : ZMod 836598263) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 6382 * (5 : ZMod 836598263) ^ 6382) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 17574985 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 836598263) ^ 25530 = 489666258 := by
        calc
          (5 : ZMod 836598263) ^ 25530 = (5 : ZMod 836598263) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 12765 * (5 : ZMod 836598263) ^ 12765 := by rw [pow_add]
          _ = 489666258 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 836598263) ^ 51061 = 37551683 := by
        calc
          (5 : ZMod 836598263) ^ 51061 = (5 : ZMod 836598263) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 25530 * (5 : ZMod 836598263) ^ 25530) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 37551683 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 836598263) ^ 102123 = 123271143 := by
        calc
          (5 : ZMod 836598263) ^ 102123 = (5 : ZMod 836598263) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 51061 * (5 : ZMod 836598263) ^ 51061) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 123271143 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 836598263) ^ 204247 = 566734744 := by
        calc
          (5 : ZMod 836598263) ^ 204247 = (5 : ZMod 836598263) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 102123 * (5 : ZMod 836598263) ^ 102123) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 566734744 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 836598263) ^ 408495 = 211135115 := by
        calc
          (5 : ZMod 836598263) ^ 408495 = (5 : ZMod 836598263) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 204247 * (5 : ZMod 836598263) ^ 204247) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 211135115 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 836598263) ^ 816990 = 407096311 := by
        calc
          (5 : ZMod 836598263) ^ 816990 = (5 : ZMod 836598263) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 408495 * (5 : ZMod 836598263) ^ 408495 := by rw [pow_add]
          _ = 407096311 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 836598263) ^ 1633980 = 271282578 := by
        calc
          (5 : ZMod 836598263) ^ 1633980 = (5 : ZMod 836598263) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 816990 * (5 : ZMod 836598263) ^ 816990 := by rw [pow_add]
          _ = 271282578 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 836598263) ^ 3267961 = 254658866 := by
        calc
          (5 : ZMod 836598263) ^ 3267961 = (5 : ZMod 836598263) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 1633980 * (5 : ZMod 836598263) ^ 1633980) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 254658866 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 836598263) ^ 6535923 = 825487773 := by
        calc
          (5 : ZMod 836598263) ^ 6535923 = (5 : ZMod 836598263) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 3267961 * (5 : ZMod 836598263) ^ 3267961) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 825487773 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 836598263) ^ 13071847 = 349501779 := by
        calc
          (5 : ZMod 836598263) ^ 13071847 = (5 : ZMod 836598263) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 6535923 * (5 : ZMod 836598263) ^ 6535923) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 349501779 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 836598263) ^ 26143695 = 824800472 := by
        calc
          (5 : ZMod 836598263) ^ 26143695 = (5 : ZMod 836598263) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 13071847 * (5 : ZMod 836598263) ^ 13071847) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 824800472 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 836598263) ^ 52287391 = 38553121 := by
        calc
          (5 : ZMod 836598263) ^ 52287391 = (5 : ZMod 836598263) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 26143695 * (5 : ZMod 836598263) ^ 26143695) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 38553121 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 836598263) ^ 104574782 = 834881691 := by
        calc
          (5 : ZMod 836598263) ^ 104574782 = (5 : ZMod 836598263) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 52287391 * (5 : ZMod 836598263) ^ 52287391 := by rw [pow_add]
          _ = 834881691 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 836598263) ^ 209149565 = 601744490 := by
        calc
          (5 : ZMod 836598263) ^ 209149565 = (5 : ZMod 836598263) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 104574782 * (5 : ZMod 836598263) ^ 104574782) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 601744490 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 836598263) ^ 418299131 = 836598262 := by
        calc
          (5 : ZMod 836598263) ^ 418299131 = (5 : ZMod 836598263) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 209149565 * (5 : ZMod 836598263) ^ 209149565) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 836598262 := by rw [factor_0_27]; decide
      change (5 : ZMod 836598263) ^ 418299131 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (5 : ZMod 836598263) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 836598263) ^ 2 = 25 := by
        calc
          (5 : ZMod 836598263) ^ 2 = (5 : ZMod 836598263) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 1 * (5 : ZMod 836598263) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 836598263) ^ 4 = 625 := by
        calc
          (5 : ZMod 836598263) ^ 4 = (5 : ZMod 836598263) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 2 * (5 : ZMod 836598263) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 836598263) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 836598263) ^ 9 = (5 : ZMod 836598263) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 4 * (5 : ZMod 836598263) ^ 4) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 836598263) ^ 18 = 645784608 := by
        calc
          (5 : ZMod 836598263) ^ 18 = (5 : ZMod 836598263) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 9 * (5 : ZMod 836598263) ^ 9 := by rw [pow_add]
          _ = 645784608 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 836598263) ^ 36 = 258171021 := by
        calc
          (5 : ZMod 836598263) ^ 36 = (5 : ZMod 836598263) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 18 * (5 : ZMod 836598263) ^ 18 := by rw [pow_add]
          _ = 258171021 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 836598263) ^ 73 = 246174196 := by
        calc
          (5 : ZMod 836598263) ^ 73 = (5 : ZMod 836598263) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 36 * (5 : ZMod 836598263) ^ 36) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 246174196 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 836598263) ^ 147 = 355846981 := by
        calc
          (5 : ZMod 836598263) ^ 147 = (5 : ZMod 836598263) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 73 * (5 : ZMod 836598263) ^ 73) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 355846981 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 836598263) ^ 294 = 13222436 := by
        calc
          (5 : ZMod 836598263) ^ 294 = (5 : ZMod 836598263) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 147 * (5 : ZMod 836598263) ^ 147 := by rw [pow_add]
          _ = 13222436 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 836598263) ^ 588 = 508772356 := by
        calc
          (5 : ZMod 836598263) ^ 588 = (5 : ZMod 836598263) ^ (294 + 294) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 294 * (5 : ZMod 836598263) ^ 294 := by rw [pow_add]
          _ = 508772356 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 836598263) ^ 1177 = 798843213 := by
        calc
          (5 : ZMod 836598263) ^ 1177 = (5 : ZMod 836598263) ^ (588 + 588 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 588 * (5 : ZMod 836598263) ^ 588) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 798843213 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 836598263) ^ 2354 = 830500372 := by
        calc
          (5 : ZMod 836598263) ^ 2354 = (5 : ZMod 836598263) ^ (1177 + 1177) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 1177 * (5 : ZMod 836598263) ^ 1177 := by rw [pow_add]
          _ = 830500372 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 836598263) ^ 4708 = 828250583 := by
        calc
          (5 : ZMod 836598263) ^ 4708 = (5 : ZMod 836598263) ^ (2354 + 2354) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 2354 * (5 : ZMod 836598263) ^ 2354 := by rw [pow_add]
          _ = 828250583 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 836598263) ^ 9417 = 728320390 := by
        calc
          (5 : ZMod 836598263) ^ 9417 = (5 : ZMod 836598263) ^ (4708 + 4708 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 4708 * (5 : ZMod 836598263) ^ 4708) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 728320390 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 836598263) ^ 18835 = 95911391 := by
        calc
          (5 : ZMod 836598263) ^ 18835 = (5 : ZMod 836598263) ^ (9417 + 9417 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 9417 * (5 : ZMod 836598263) ^ 9417) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 95911391 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 836598263) ^ 37671 = 126747021 := by
        calc
          (5 : ZMod 836598263) ^ 37671 = (5 : ZMod 836598263) ^ (18835 + 18835 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 18835 * (5 : ZMod 836598263) ^ 18835) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 126747021 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 836598263) ^ 75342 = 742775999 := by
        calc
          (5 : ZMod 836598263) ^ 75342 = (5 : ZMod 836598263) ^ (37671 + 37671) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 37671 * (5 : ZMod 836598263) ^ 37671 := by rw [pow_add]
          _ = 742775999 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 836598263) ^ 150684 = 573053788 := by
        calc
          (5 : ZMod 836598263) ^ 150684 = (5 : ZMod 836598263) ^ (75342 + 75342) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 75342 * (5 : ZMod 836598263) ^ 75342 := by rw [pow_add]
          _ = 573053788 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 836598263) ^ 301368 = 761868397 := by
        calc
          (5 : ZMod 836598263) ^ 301368 = (5 : ZMod 836598263) ^ (150684 + 150684) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 150684 * (5 : ZMod 836598263) ^ 150684 := by rw [pow_add]
          _ = 761868397 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 836598263) ^ 602736 = 121391426 := by
        calc
          (5 : ZMod 836598263) ^ 602736 = (5 : ZMod 836598263) ^ (301368 + 301368) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 301368 * (5 : ZMod 836598263) ^ 301368 := by rw [pow_add]
          _ = 121391426 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 836598263) ^ 1205473 = 130736046 := by
        calc
          (5 : ZMod 836598263) ^ 1205473 = (5 : ZMod 836598263) ^ (602736 + 602736 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 602736 * (5 : ZMod 836598263) ^ 602736) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 130736046 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 836598263) ^ 2410946 = 387861840 := by
        calc
          (5 : ZMod 836598263) ^ 2410946 = (5 : ZMod 836598263) ^ (1205473 + 1205473) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 1205473 * (5 : ZMod 836598263) ^ 1205473 := by rw [pow_add]
          _ = 387861840 := by rw [factor_1_20]; decide
      change (5 : ZMod 836598263) ^ 2410946 ≠ 1
      rw [factor_1_21]
      decide
    ·
      have factor_2_0 : (5 : ZMod 836598263) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 836598263) ^ 2 = 25 := by
        calc
          (5 : ZMod 836598263) ^ 2 = (5 : ZMod 836598263) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 1 * (5 : ZMod 836598263) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 836598263) ^ 5 = 3125 := by
        calc
          (5 : ZMod 836598263) ^ 5 = (5 : ZMod 836598263) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 2 * (5 : ZMod 836598263) ^ 2) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 836598263) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 836598263) ^ 10 = (5 : ZMod 836598263) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 5 * (5 : ZMod 836598263) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 836598263) ^ 21 = 409642752 := by
        calc
          (5 : ZMod 836598263) ^ 21 = (5 : ZMod 836598263) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 10 * (5 : ZMod 836598263) ^ 10) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 409642752 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 836598263) ^ 43 = 63492958 := by
        calc
          (5 : ZMod 836598263) ^ 43 = (5 : ZMod 836598263) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 21 * (5 : ZMod 836598263) ^ 21) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 63492958 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 836598263) ^ 86 = 345553303 := by
        calc
          (5 : ZMod 836598263) ^ 86 = (5 : ZMod 836598263) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 43 * (5 : ZMod 836598263) ^ 43 := by rw [pow_add]
          _ = 345553303 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 836598263) ^ 173 = 428626493 := by
        calc
          (5 : ZMod 836598263) ^ 173 = (5 : ZMod 836598263) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 86 * (5 : ZMod 836598263) ^ 86) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 428626493 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 836598263) ^ 347 = 192722150 := by
        calc
          (5 : ZMod 836598263) ^ 347 = (5 : ZMod 836598263) ^ (173 + 173 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = ((5 : ZMod 836598263) ^ 173 * (5 : ZMod 836598263) ^ 173) * (5 : ZMod 836598263) := by rw [pow_succ, pow_add]
          _ = 192722150 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 836598263) ^ 694 = 630310487 := by
        calc
          (5 : ZMod 836598263) ^ 694 = (5 : ZMod 836598263) ^ (347 + 347) :=
            congrArg (fun n : ℕ => (5 : ZMod 836598263) ^ n) (by norm_num)
          _ = (5 : ZMod 836598263) ^ 347 * (5 : ZMod 836598263) ^ 347 := by rw [pow_add]
          _ = 630310487 := by rw [factor_2_8]; decide
      change (5 : ZMod 836598263) ^ 694 ≠ 1
      rw [factor_2_9]
      decide

#print axioms prime_lucas_836598263

end TotientTailPeriodKiller
end Erdos249257
