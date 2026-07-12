import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_21369774403 : Nat.Prime 21369774403 := by
  apply lucas_primality 21369774403 (2 : ZMod 21369774403)
  ·
      have fermat_0 : (2 : ZMod 21369774403) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 21369774403) ^ 2 = 4 := by
        calc
          (2 : ZMod 21369774403) ^ 2 = (2 : ZMod 21369774403) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 1 * (2 : ZMod 21369774403) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 21369774403) ^ 4 = 16 := by
        calc
          (2 : ZMod 21369774403) ^ 4 = (2 : ZMod 21369774403) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2 * (2 : ZMod 21369774403) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 21369774403) ^ 9 = 512 := by
        calc
          (2 : ZMod 21369774403) ^ 9 = (2 : ZMod 21369774403) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 4 * (2 : ZMod 21369774403) ^ 4) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 21369774403) ^ 19 = 524288 := by
        calc
          (2 : ZMod 21369774403) ^ 19 = (2 : ZMod 21369774403) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 9 * (2 : ZMod 21369774403) ^ 9) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 21369774403) ^ 39 = 15511453813 := by
        calc
          (2 : ZMod 21369774403) ^ 39 = (2 : ZMod 21369774403) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 19 * (2 : ZMod 21369774403) ^ 19) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 15511453813 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 21369774403) ^ 79 = 3038285068 := by
        calc
          (2 : ZMod 21369774403) ^ 79 = (2 : ZMod 21369774403) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 39 * (2 : ZMod 21369774403) ^ 39) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 3038285068 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 21369774403) ^ 159 = 15042857875 := by
        calc
          (2 : ZMod 21369774403) ^ 159 = (2 : ZMod 21369774403) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 79 * (2 : ZMod 21369774403) ^ 79) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 15042857875 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 21369774403) ^ 318 = 14599541194 := by
        calc
          (2 : ZMod 21369774403) ^ 318 = (2 : ZMod 21369774403) ^ (159 + 159) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 159 * (2 : ZMod 21369774403) ^ 159 := by rw [pow_add]
          _ = 14599541194 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 21369774403) ^ 636 = 15863360870 := by
        calc
          (2 : ZMod 21369774403) ^ 636 = (2 : ZMod 21369774403) ^ (318 + 318) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 318 * (2 : ZMod 21369774403) ^ 318 := by rw [pow_add]
          _ = 15863360870 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 21369774403) ^ 1273 = 18894790551 := by
        calc
          (2 : ZMod 21369774403) ^ 1273 = (2 : ZMod 21369774403) ^ (636 + 636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 636 * (2 : ZMod 21369774403) ^ 636) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 18894790551 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 21369774403) ^ 2547 = 8424010501 := by
        calc
          (2 : ZMod 21369774403) ^ 2547 = (2 : ZMod 21369774403) ^ (1273 + 1273 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 1273 * (2 : ZMod 21369774403) ^ 1273) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 8424010501 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 21369774403) ^ 5094 = 13334491257 := by
        calc
          (2 : ZMod 21369774403) ^ 5094 = (2 : ZMod 21369774403) ^ (2547 + 2547) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2547 * (2 : ZMod 21369774403) ^ 2547 := by rw [pow_add]
          _ = 13334491257 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 21369774403) ^ 10189 = 7302924417 := by
        calc
          (2 : ZMod 21369774403) ^ 10189 = (2 : ZMod 21369774403) ^ (5094 + 5094 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 5094 * (2 : ZMod 21369774403) ^ 5094) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 7302924417 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 21369774403) ^ 20379 = 15233616720 := by
        calc
          (2 : ZMod 21369774403) ^ 20379 = (2 : ZMod 21369774403) ^ (10189 + 10189 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 10189 * (2 : ZMod 21369774403) ^ 10189) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 15233616720 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 21369774403) ^ 40759 = 2192385023 := by
        calc
          (2 : ZMod 21369774403) ^ 40759 = (2 : ZMod 21369774403) ^ (20379 + 20379 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 20379 * (2 : ZMod 21369774403) ^ 20379) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 2192385023 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 21369774403) ^ 81519 = 18481838732 := by
        calc
          (2 : ZMod 21369774403) ^ 81519 = (2 : ZMod 21369774403) ^ (40759 + 40759 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 40759 * (2 : ZMod 21369774403) ^ 40759) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 18481838732 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 21369774403) ^ 163038 = 7927284287 := by
        calc
          (2 : ZMod 21369774403) ^ 163038 = (2 : ZMod 21369774403) ^ (81519 + 81519) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 81519 * (2 : ZMod 21369774403) ^ 81519 := by rw [pow_add]
          _ = 7927284287 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 21369774403) ^ 326076 = 9076250789 := by
        calc
          (2 : ZMod 21369774403) ^ 326076 = (2 : ZMod 21369774403) ^ (163038 + 163038) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 163038 * (2 : ZMod 21369774403) ^ 163038 := by rw [pow_add]
          _ = 9076250789 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 21369774403) ^ 652153 = 16450783645 := by
        calc
          (2 : ZMod 21369774403) ^ 652153 = (2 : ZMod 21369774403) ^ (326076 + 326076 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 326076 * (2 : ZMod 21369774403) ^ 326076) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 16450783645 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 21369774403) ^ 1304307 = 7050168668 := by
        calc
          (2 : ZMod 21369774403) ^ 1304307 = (2 : ZMod 21369774403) ^ (652153 + 652153 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 652153 * (2 : ZMod 21369774403) ^ 652153) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 7050168668 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 21369774403) ^ 2608615 = 10416064551 := by
        calc
          (2 : ZMod 21369774403) ^ 2608615 = (2 : ZMod 21369774403) ^ (1304307 + 1304307 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 1304307 * (2 : ZMod 21369774403) ^ 1304307) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 10416064551 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 21369774403) ^ 5217230 = 12279798129 := by
        calc
          (2 : ZMod 21369774403) ^ 5217230 = (2 : ZMod 21369774403) ^ (2608615 + 2608615) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2608615 * (2 : ZMod 21369774403) ^ 2608615 := by rw [pow_add]
          _ = 12279798129 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 21369774403) ^ 10434460 = 12062187894 := by
        calc
          (2 : ZMod 21369774403) ^ 10434460 = (2 : ZMod 21369774403) ^ (5217230 + 5217230) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 5217230 * (2 : ZMod 21369774403) ^ 5217230 := by rw [pow_add]
          _ = 12062187894 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 21369774403) ^ 20868920 = 4061385646 := by
        calc
          (2 : ZMod 21369774403) ^ 20868920 = (2 : ZMod 21369774403) ^ (10434460 + 10434460) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 10434460 * (2 : ZMod 21369774403) ^ 10434460 := by rw [pow_add]
          _ = 4061385646 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 21369774403) ^ 41737840 = 2709378469 := by
        calc
          (2 : ZMod 21369774403) ^ 41737840 = (2 : ZMod 21369774403) ^ (20868920 + 20868920) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 20868920 * (2 : ZMod 21369774403) ^ 20868920 := by rw [pow_add]
          _ = 2709378469 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 21369774403) ^ 83475681 = 4572659787 := by
        calc
          (2 : ZMod 21369774403) ^ 83475681 = (2 : ZMod 21369774403) ^ (41737840 + 41737840 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 41737840 * (2 : ZMod 21369774403) ^ 41737840) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 4572659787 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 21369774403) ^ 166951362 = 14927716739 := by
        calc
          (2 : ZMod 21369774403) ^ 166951362 = (2 : ZMod 21369774403) ^ (83475681 + 83475681) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 83475681 * (2 : ZMod 21369774403) ^ 83475681 := by rw [pow_add]
          _ = 14927716739 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 21369774403) ^ 333902725 = 3446981173 := by
        calc
          (2 : ZMod 21369774403) ^ 333902725 = (2 : ZMod 21369774403) ^ (166951362 + 166951362 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 166951362 * (2 : ZMod 21369774403) ^ 166951362) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 3446981173 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 21369774403) ^ 667805450 = 14641820049 := by
        calc
          (2 : ZMod 21369774403) ^ 667805450 = (2 : ZMod 21369774403) ^ (333902725 + 333902725) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 333902725 * (2 : ZMod 21369774403) ^ 333902725 := by rw [pow_add]
          _ = 14641820049 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 21369774403) ^ 1335610900 = 4331319839 := by
        calc
          (2 : ZMod 21369774403) ^ 1335610900 = (2 : ZMod 21369774403) ^ (667805450 + 667805450) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 667805450 * (2 : ZMod 21369774403) ^ 667805450 := by rw [pow_add]
          _ = 4331319839 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 21369774403) ^ 2671221800 = 17149407474 := by
        calc
          (2 : ZMod 21369774403) ^ 2671221800 = (2 : ZMod 21369774403) ^ (1335610900 + 1335610900) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 1335610900 * (2 : ZMod 21369774403) ^ 1335610900 := by rw [pow_add]
          _ = 17149407474 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 21369774403) ^ 5342443600 = 8529900516 := by
        calc
          (2 : ZMod 21369774403) ^ 5342443600 = (2 : ZMod 21369774403) ^ (2671221800 + 2671221800) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2671221800 * (2 : ZMod 21369774403) ^ 2671221800 := by rw [pow_add]
          _ = 8529900516 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 21369774403) ^ 10684887201 = 21369774402 := by
        calc
          (2 : ZMod 21369774403) ^ 10684887201 = (2 : ZMod 21369774403) ^ (5342443600 + 5342443600 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 5342443600 * (2 : ZMod 21369774403) ^ 5342443600) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 21369774402 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 21369774403) ^ 21369774402 = 1 := by
        calc
          (2 : ZMod 21369774403) ^ 21369774402 = (2 : ZMod 21369774403) ^ (10684887201 + 10684887201) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 10684887201 * (2 : ZMod 21369774403) ^ 10684887201 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (10607, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (10607, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 21369774403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 21369774403) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 21369774403) ^ 2 = 4 := by
        calc
          (2 : ZMod 21369774403) ^ 2 = (2 : ZMod 21369774403) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 1 * (2 : ZMod 21369774403) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 21369774403) ^ 4 = 16 := by
        calc
          (2 : ZMod 21369774403) ^ 4 = (2 : ZMod 21369774403) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2 * (2 : ZMod 21369774403) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 21369774403) ^ 9 = 512 := by
        calc
          (2 : ZMod 21369774403) ^ 9 = (2 : ZMod 21369774403) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 4 * (2 : ZMod 21369774403) ^ 4) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 21369774403) ^ 19 = 524288 := by
        calc
          (2 : ZMod 21369774403) ^ 19 = (2 : ZMod 21369774403) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 9 * (2 : ZMod 21369774403) ^ 9) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 21369774403) ^ 39 = 15511453813 := by
        calc
          (2 : ZMod 21369774403) ^ 39 = (2 : ZMod 21369774403) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 19 * (2 : ZMod 21369774403) ^ 19) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 15511453813 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 21369774403) ^ 79 = 3038285068 := by
        calc
          (2 : ZMod 21369774403) ^ 79 = (2 : ZMod 21369774403) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 39 * (2 : ZMod 21369774403) ^ 39) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 3038285068 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 21369774403) ^ 159 = 15042857875 := by
        calc
          (2 : ZMod 21369774403) ^ 159 = (2 : ZMod 21369774403) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 79 * (2 : ZMod 21369774403) ^ 79) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 15042857875 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 21369774403) ^ 318 = 14599541194 := by
        calc
          (2 : ZMod 21369774403) ^ 318 = (2 : ZMod 21369774403) ^ (159 + 159) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 159 * (2 : ZMod 21369774403) ^ 159 := by rw [pow_add]
          _ = 14599541194 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 21369774403) ^ 636 = 15863360870 := by
        calc
          (2 : ZMod 21369774403) ^ 636 = (2 : ZMod 21369774403) ^ (318 + 318) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 318 * (2 : ZMod 21369774403) ^ 318 := by rw [pow_add]
          _ = 15863360870 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 21369774403) ^ 1273 = 18894790551 := by
        calc
          (2 : ZMod 21369774403) ^ 1273 = (2 : ZMod 21369774403) ^ (636 + 636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 636 * (2 : ZMod 21369774403) ^ 636) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 18894790551 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 21369774403) ^ 2547 = 8424010501 := by
        calc
          (2 : ZMod 21369774403) ^ 2547 = (2 : ZMod 21369774403) ^ (1273 + 1273 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 1273 * (2 : ZMod 21369774403) ^ 1273) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 8424010501 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 21369774403) ^ 5094 = 13334491257 := by
        calc
          (2 : ZMod 21369774403) ^ 5094 = (2 : ZMod 21369774403) ^ (2547 + 2547) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2547 * (2 : ZMod 21369774403) ^ 2547 := by rw [pow_add]
          _ = 13334491257 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 21369774403) ^ 10189 = 7302924417 := by
        calc
          (2 : ZMod 21369774403) ^ 10189 = (2 : ZMod 21369774403) ^ (5094 + 5094 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 5094 * (2 : ZMod 21369774403) ^ 5094) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 7302924417 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 21369774403) ^ 20379 = 15233616720 := by
        calc
          (2 : ZMod 21369774403) ^ 20379 = (2 : ZMod 21369774403) ^ (10189 + 10189 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 10189 * (2 : ZMod 21369774403) ^ 10189) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 15233616720 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 21369774403) ^ 40759 = 2192385023 := by
        calc
          (2 : ZMod 21369774403) ^ 40759 = (2 : ZMod 21369774403) ^ (20379 + 20379 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 20379 * (2 : ZMod 21369774403) ^ 20379) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 2192385023 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 21369774403) ^ 81519 = 18481838732 := by
        calc
          (2 : ZMod 21369774403) ^ 81519 = (2 : ZMod 21369774403) ^ (40759 + 40759 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 40759 * (2 : ZMod 21369774403) ^ 40759) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 18481838732 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 21369774403) ^ 163038 = 7927284287 := by
        calc
          (2 : ZMod 21369774403) ^ 163038 = (2 : ZMod 21369774403) ^ (81519 + 81519) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 81519 * (2 : ZMod 21369774403) ^ 81519 := by rw [pow_add]
          _ = 7927284287 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 21369774403) ^ 326076 = 9076250789 := by
        calc
          (2 : ZMod 21369774403) ^ 326076 = (2 : ZMod 21369774403) ^ (163038 + 163038) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 163038 * (2 : ZMod 21369774403) ^ 163038 := by rw [pow_add]
          _ = 9076250789 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 21369774403) ^ 652153 = 16450783645 := by
        calc
          (2 : ZMod 21369774403) ^ 652153 = (2 : ZMod 21369774403) ^ (326076 + 326076 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 326076 * (2 : ZMod 21369774403) ^ 326076) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 16450783645 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 21369774403) ^ 1304307 = 7050168668 := by
        calc
          (2 : ZMod 21369774403) ^ 1304307 = (2 : ZMod 21369774403) ^ (652153 + 652153 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 652153 * (2 : ZMod 21369774403) ^ 652153) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 7050168668 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 21369774403) ^ 2608615 = 10416064551 := by
        calc
          (2 : ZMod 21369774403) ^ 2608615 = (2 : ZMod 21369774403) ^ (1304307 + 1304307 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 1304307 * (2 : ZMod 21369774403) ^ 1304307) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 10416064551 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 21369774403) ^ 5217230 = 12279798129 := by
        calc
          (2 : ZMod 21369774403) ^ 5217230 = (2 : ZMod 21369774403) ^ (2608615 + 2608615) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2608615 * (2 : ZMod 21369774403) ^ 2608615 := by rw [pow_add]
          _ = 12279798129 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 21369774403) ^ 10434460 = 12062187894 := by
        calc
          (2 : ZMod 21369774403) ^ 10434460 = (2 : ZMod 21369774403) ^ (5217230 + 5217230) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 5217230 * (2 : ZMod 21369774403) ^ 5217230 := by rw [pow_add]
          _ = 12062187894 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 21369774403) ^ 20868920 = 4061385646 := by
        calc
          (2 : ZMod 21369774403) ^ 20868920 = (2 : ZMod 21369774403) ^ (10434460 + 10434460) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 10434460 * (2 : ZMod 21369774403) ^ 10434460 := by rw [pow_add]
          _ = 4061385646 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 21369774403) ^ 41737840 = 2709378469 := by
        calc
          (2 : ZMod 21369774403) ^ 41737840 = (2 : ZMod 21369774403) ^ (20868920 + 20868920) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 20868920 * (2 : ZMod 21369774403) ^ 20868920 := by rw [pow_add]
          _ = 2709378469 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 21369774403) ^ 83475681 = 4572659787 := by
        calc
          (2 : ZMod 21369774403) ^ 83475681 = (2 : ZMod 21369774403) ^ (41737840 + 41737840 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 41737840 * (2 : ZMod 21369774403) ^ 41737840) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 4572659787 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 21369774403) ^ 166951362 = 14927716739 := by
        calc
          (2 : ZMod 21369774403) ^ 166951362 = (2 : ZMod 21369774403) ^ (83475681 + 83475681) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 83475681 * (2 : ZMod 21369774403) ^ 83475681 := by rw [pow_add]
          _ = 14927716739 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 21369774403) ^ 333902725 = 3446981173 := by
        calc
          (2 : ZMod 21369774403) ^ 333902725 = (2 : ZMod 21369774403) ^ (166951362 + 166951362 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 166951362 * (2 : ZMod 21369774403) ^ 166951362) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 3446981173 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 21369774403) ^ 667805450 = 14641820049 := by
        calc
          (2 : ZMod 21369774403) ^ 667805450 = (2 : ZMod 21369774403) ^ (333902725 + 333902725) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 333902725 * (2 : ZMod 21369774403) ^ 333902725 := by rw [pow_add]
          _ = 14641820049 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 21369774403) ^ 1335610900 = 4331319839 := by
        calc
          (2 : ZMod 21369774403) ^ 1335610900 = (2 : ZMod 21369774403) ^ (667805450 + 667805450) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 667805450 * (2 : ZMod 21369774403) ^ 667805450 := by rw [pow_add]
          _ = 4331319839 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 21369774403) ^ 2671221800 = 17149407474 := by
        calc
          (2 : ZMod 21369774403) ^ 2671221800 = (2 : ZMod 21369774403) ^ (1335610900 + 1335610900) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 1335610900 * (2 : ZMod 21369774403) ^ 1335610900 := by rw [pow_add]
          _ = 17149407474 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 21369774403) ^ 5342443600 = 8529900516 := by
        calc
          (2 : ZMod 21369774403) ^ 5342443600 = (2 : ZMod 21369774403) ^ (2671221800 + 2671221800) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2671221800 * (2 : ZMod 21369774403) ^ 2671221800 := by rw [pow_add]
          _ = 8529900516 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 21369774403) ^ 10684887201 = 21369774402 := by
        calc
          (2 : ZMod 21369774403) ^ 10684887201 = (2 : ZMod 21369774403) ^ (5342443600 + 5342443600 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 5342443600 * (2 : ZMod 21369774403) ^ 5342443600) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 21369774402 := by rw [factor_0_32]; decide
      change (2 : ZMod 21369774403) ^ 10684887201 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (2 : ZMod 21369774403) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 21369774403) ^ 3 = 8 := by
        calc
          (2 : ZMod 21369774403) ^ 3 = (2 : ZMod 21369774403) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 1 * (2 : ZMod 21369774403) ^ 1) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 21369774403) ^ 6 = 64 := by
        calc
          (2 : ZMod 21369774403) ^ 6 = (2 : ZMod 21369774403) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 3 * (2 : ZMod 21369774403) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 21369774403) ^ 13 = 8192 := by
        calc
          (2 : ZMod 21369774403) ^ 13 = (2 : ZMod 21369774403) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 6 * (2 : ZMod 21369774403) ^ 6) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 21369774403) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 21369774403) ^ 26 = (2 : ZMod 21369774403) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 13 * (2 : ZMod 21369774403) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 21369774403) ^ 53 = 10302071716 := by
        calc
          (2 : ZMod 21369774403) ^ 53 = (2 : ZMod 21369774403) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 26 * (2 : ZMod 21369774403) ^ 26) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 10302071716 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 21369774403) ^ 106 = 7029621584 := by
        calc
          (2 : ZMod 21369774403) ^ 106 = (2 : ZMod 21369774403) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 53 * (2 : ZMod 21369774403) ^ 53 := by rw [pow_add]
          _ = 7029621584 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 21369774403) ^ 212 = 3567358753 := by
        calc
          (2 : ZMod 21369774403) ^ 212 = (2 : ZMod 21369774403) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 106 * (2 : ZMod 21369774403) ^ 106 := by rw [pow_add]
          _ = 3567358753 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 21369774403) ^ 424 = 1171031781 := by
        calc
          (2 : ZMod 21369774403) ^ 424 = (2 : ZMod 21369774403) ^ (212 + 212) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 212 * (2 : ZMod 21369774403) ^ 212 := by rw [pow_add]
          _ = 1171031781 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 21369774403) ^ 849 = 18031968749 := by
        calc
          (2 : ZMod 21369774403) ^ 849 = (2 : ZMod 21369774403) ^ (424 + 424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 424 * (2 : ZMod 21369774403) ^ 424) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 18031968749 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 21369774403) ^ 1698 = 17553940532 := by
        calc
          (2 : ZMod 21369774403) ^ 1698 = (2 : ZMod 21369774403) ^ (849 + 849) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 849 * (2 : ZMod 21369774403) ^ 849 := by rw [pow_add]
          _ = 17553940532 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 21369774403) ^ 3396 = 3072961601 := by
        calc
          (2 : ZMod 21369774403) ^ 3396 = (2 : ZMod 21369774403) ^ (1698 + 1698) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 1698 * (2 : ZMod 21369774403) ^ 1698 := by rw [pow_add]
          _ = 3072961601 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 21369774403) ^ 6793 = 6339140651 := by
        calc
          (2 : ZMod 21369774403) ^ 6793 = (2 : ZMod 21369774403) ^ (3396 + 3396 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 3396 * (2 : ZMod 21369774403) ^ 3396) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 6339140651 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 21369774403) ^ 13586 = 3249442967 := by
        calc
          (2 : ZMod 21369774403) ^ 13586 = (2 : ZMod 21369774403) ^ (6793 + 6793) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 6793 * (2 : ZMod 21369774403) ^ 6793 := by rw [pow_add]
          _ = 3249442967 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 21369774403) ^ 27173 = 12620538985 := by
        calc
          (2 : ZMod 21369774403) ^ 27173 = (2 : ZMod 21369774403) ^ (13586 + 13586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 13586 * (2 : ZMod 21369774403) ^ 13586) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 12620538985 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 21369774403) ^ 54346 = 10005748140 := by
        calc
          (2 : ZMod 21369774403) ^ 54346 = (2 : ZMod 21369774403) ^ (27173 + 27173) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 27173 * (2 : ZMod 21369774403) ^ 27173 := by rw [pow_add]
          _ = 10005748140 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 21369774403) ^ 108692 = 2981213737 := by
        calc
          (2 : ZMod 21369774403) ^ 108692 = (2 : ZMod 21369774403) ^ (54346 + 54346) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 54346 * (2 : ZMod 21369774403) ^ 54346 := by rw [pow_add]
          _ = 2981213737 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 21369774403) ^ 217384 = 1931526326 := by
        calc
          (2 : ZMod 21369774403) ^ 217384 = (2 : ZMod 21369774403) ^ (108692 + 108692) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 108692 * (2 : ZMod 21369774403) ^ 108692 := by rw [pow_add]
          _ = 1931526326 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 21369774403) ^ 434769 = 17230517664 := by
        calc
          (2 : ZMod 21369774403) ^ 434769 = (2 : ZMod 21369774403) ^ (217384 + 217384 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 217384 * (2 : ZMod 21369774403) ^ 217384) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 17230517664 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 21369774403) ^ 869538 = 20046606274 := by
        calc
          (2 : ZMod 21369774403) ^ 869538 = (2 : ZMod 21369774403) ^ (434769 + 434769) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 434769 * (2 : ZMod 21369774403) ^ 434769 := by rw [pow_add]
          _ = 20046606274 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 21369774403) ^ 1739076 = 16987400304 := by
        calc
          (2 : ZMod 21369774403) ^ 1739076 = (2 : ZMod 21369774403) ^ (869538 + 869538) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 869538 * (2 : ZMod 21369774403) ^ 869538 := by rw [pow_add]
          _ = 16987400304 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 21369774403) ^ 3478153 = 8547268043 := by
        calc
          (2 : ZMod 21369774403) ^ 3478153 = (2 : ZMod 21369774403) ^ (1739076 + 1739076 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 1739076 * (2 : ZMod 21369774403) ^ 1739076) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 8547268043 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 21369774403) ^ 6956306 = 4066952602 := by
        calc
          (2 : ZMod 21369774403) ^ 6956306 = (2 : ZMod 21369774403) ^ (3478153 + 3478153) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 3478153 * (2 : ZMod 21369774403) ^ 3478153 := by rw [pow_add]
          _ = 4066952602 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 21369774403) ^ 13912613 = 4263171025 := by
        calc
          (2 : ZMod 21369774403) ^ 13912613 = (2 : ZMod 21369774403) ^ (6956306 + 6956306 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 6956306 * (2 : ZMod 21369774403) ^ 6956306) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 4263171025 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 21369774403) ^ 27825227 = 10699629597 := by
        calc
          (2 : ZMod 21369774403) ^ 27825227 = (2 : ZMod 21369774403) ^ (13912613 + 13912613 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 13912613 * (2 : ZMod 21369774403) ^ 13912613) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 10699629597 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 21369774403) ^ 55650454 = 12961843511 := by
        calc
          (2 : ZMod 21369774403) ^ 55650454 = (2 : ZMod 21369774403) ^ (27825227 + 27825227) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 27825227 * (2 : ZMod 21369774403) ^ 27825227 := by rw [pow_add]
          _ = 12961843511 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 21369774403) ^ 111300908 = 12018126519 := by
        calc
          (2 : ZMod 21369774403) ^ 111300908 = (2 : ZMod 21369774403) ^ (55650454 + 55650454) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 55650454 * (2 : ZMod 21369774403) ^ 55650454 := by rw [pow_add]
          _ = 12018126519 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 21369774403) ^ 222601816 = 18595068519 := by
        calc
          (2 : ZMod 21369774403) ^ 222601816 = (2 : ZMod 21369774403) ^ (111300908 + 111300908) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 111300908 * (2 : ZMod 21369774403) ^ 111300908 := by rw [pow_add]
          _ = 18595068519 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 21369774403) ^ 445203633 = 9989040080 := by
        calc
          (2 : ZMod 21369774403) ^ 445203633 = (2 : ZMod 21369774403) ^ (222601816 + 222601816 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 222601816 * (2 : ZMod 21369774403) ^ 222601816) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 9989040080 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 21369774403) ^ 890407266 = 13721522000 := by
        calc
          (2 : ZMod 21369774403) ^ 890407266 = (2 : ZMod 21369774403) ^ (445203633 + 445203633) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 445203633 * (2 : ZMod 21369774403) ^ 445203633 := by rw [pow_add]
          _ = 13721522000 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 21369774403) ^ 1780814533 = 5796943425 := by
        calc
          (2 : ZMod 21369774403) ^ 1780814533 = (2 : ZMod 21369774403) ^ (890407266 + 890407266 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 890407266 * (2 : ZMod 21369774403) ^ 890407266) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 5796943425 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 21369774403) ^ 3561629067 = 12151875212 := by
        calc
          (2 : ZMod 21369774403) ^ 3561629067 = (2 : ZMod 21369774403) ^ (1780814533 + 1780814533 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 1780814533 * (2 : ZMod 21369774403) ^ 1780814533) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 12151875212 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 21369774403) ^ 7123258134 = 12151875211 := by
        calc
          (2 : ZMod 21369774403) ^ 7123258134 = (2 : ZMod 21369774403) ^ (3561629067 + 3561629067) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 3561629067 * (2 : ZMod 21369774403) ^ 3561629067 := by rw [pow_add]
          _ = 12151875211 := by rw [factor_1_31]; decide
      change (2 : ZMod 21369774403) ^ 7123258134 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (2 : ZMod 21369774403) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 21369774403) ^ 3 = 8 := by
        calc
          (2 : ZMod 21369774403) ^ 3 = (2 : ZMod 21369774403) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 1 * (2 : ZMod 21369774403) ^ 1) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 21369774403) ^ 7 = 128 := by
        calc
          (2 : ZMod 21369774403) ^ 7 = (2 : ZMod 21369774403) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 3 * (2 : ZMod 21369774403) ^ 3) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 21369774403) ^ 15 = 32768 := by
        calc
          (2 : ZMod 21369774403) ^ 15 = (2 : ZMod 21369774403) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 7 * (2 : ZMod 21369774403) ^ 7) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 21369774403) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 21369774403) ^ 30 = (2 : ZMod 21369774403) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 15 * (2 : ZMod 21369774403) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 21369774403) ^ 61 = 8848107727 := by
        calc
          (2 : ZMod 21369774403) ^ 61 = (2 : ZMod 21369774403) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 30 * (2 : ZMod 21369774403) ^ 30) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 8848107727 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 21369774403) ^ 122 = 3683549150 := by
        calc
          (2 : ZMod 21369774403) ^ 122 = (2 : ZMod 21369774403) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 61 * (2 : ZMod 21369774403) ^ 61 := by rw [pow_add]
          _ = 3683549150 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 21369774403) ^ 245 = 8706226255 := by
        calc
          (2 : ZMod 21369774403) ^ 245 = (2 : ZMod 21369774403) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 122 * (2 : ZMod 21369774403) ^ 122) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 8706226255 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 21369774403) ^ 491 = 12857881394 := by
        calc
          (2 : ZMod 21369774403) ^ 491 = (2 : ZMod 21369774403) ^ (245 + 245 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 245 * (2 : ZMod 21369774403) ^ 245) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 12857881394 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 21369774403) ^ 983 = 3449602529 := by
        calc
          (2 : ZMod 21369774403) ^ 983 = (2 : ZMod 21369774403) ^ (491 + 491 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 491 * (2 : ZMod 21369774403) ^ 491) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 3449602529 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 21369774403) ^ 1967 = 6548445639 := by
        calc
          (2 : ZMod 21369774403) ^ 1967 = (2 : ZMod 21369774403) ^ (983 + 983 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 983 * (2 : ZMod 21369774403) ^ 983) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 6548445639 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 21369774403) ^ 3934 = 15761471790 := by
        calc
          (2 : ZMod 21369774403) ^ 3934 = (2 : ZMod 21369774403) ^ (1967 + 1967) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 1967 * (2 : ZMod 21369774403) ^ 1967 := by rw [pow_add]
          _ = 15761471790 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 21369774403) ^ 7869 = 1459732764 := by
        calc
          (2 : ZMod 21369774403) ^ 7869 = (2 : ZMod 21369774403) ^ (3934 + 3934 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 3934 * (2 : ZMod 21369774403) ^ 3934) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 1459732764 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 21369774403) ^ 15739 = 4978608292 := by
        calc
          (2 : ZMod 21369774403) ^ 15739 = (2 : ZMod 21369774403) ^ (7869 + 7869 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 7869 * (2 : ZMod 21369774403) ^ 7869) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 4978608292 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 21369774403) ^ 31479 = 5086317355 := by
        calc
          (2 : ZMod 21369774403) ^ 31479 = (2 : ZMod 21369774403) ^ (15739 + 15739 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 15739 * (2 : ZMod 21369774403) ^ 15739) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 5086317355 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 21369774403) ^ 62958 = 4784781733 := by
        calc
          (2 : ZMod 21369774403) ^ 62958 = (2 : ZMod 21369774403) ^ (31479 + 31479) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 31479 * (2 : ZMod 21369774403) ^ 31479 := by rw [pow_add]
          _ = 4784781733 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 21369774403) ^ 125917 = 6867505306 := by
        calc
          (2 : ZMod 21369774403) ^ 125917 = (2 : ZMod 21369774403) ^ (62958 + 62958 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 62958 * (2 : ZMod 21369774403) ^ 62958) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 6867505306 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 21369774403) ^ 251835 = 14728963665 := by
        calc
          (2 : ZMod 21369774403) ^ 251835 = (2 : ZMod 21369774403) ^ (125917 + 125917 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 125917 * (2 : ZMod 21369774403) ^ 125917) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 14728963665 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 21369774403) ^ 503671 = 1860688554 := by
        calc
          (2 : ZMod 21369774403) ^ 503671 = (2 : ZMod 21369774403) ^ (251835 + 251835 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 251835 * (2 : ZMod 21369774403) ^ 251835) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 1860688554 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 21369774403) ^ 1007343 = 12667736471 := by
        calc
          (2 : ZMod 21369774403) ^ 1007343 = (2 : ZMod 21369774403) ^ (503671 + 503671 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 503671 * (2 : ZMod 21369774403) ^ 503671) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 12667736471 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 21369774403) ^ 2014686 = 20950950384 := by
        calc
          (2 : ZMod 21369774403) ^ 2014686 = (2 : ZMod 21369774403) ^ (1007343 + 1007343) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 1007343 * (2 : ZMod 21369774403) ^ 1007343 := by rw [pow_add]
          _ = 20950950384 := by rw [factor_2_19]; decide
      change (2 : ZMod 21369774403) ^ 2014686 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (2 : ZMod 21369774403) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 21369774403) ^ 2 = 4 := by
        calc
          (2 : ZMod 21369774403) ^ 2 = (2 : ZMod 21369774403) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 1 * (2 : ZMod 21369774403) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 21369774403) ^ 4 = 16 := by
        calc
          (2 : ZMod 21369774403) ^ 4 = (2 : ZMod 21369774403) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2 * (2 : ZMod 21369774403) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 21369774403) ^ 8 = 256 := by
        calc
          (2 : ZMod 21369774403) ^ 8 = (2 : ZMod 21369774403) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 4 * (2 : ZMod 21369774403) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 21369774403) ^ 17 = 131072 := by
        calc
          (2 : ZMod 21369774403) ^ 17 = (2 : ZMod 21369774403) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 8 * (2 : ZMod 21369774403) ^ 8) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 21369774403) ^ 34 = 17179869184 := by
        calc
          (2 : ZMod 21369774403) ^ 34 = (2 : ZMod 21369774403) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 17 * (2 : ZMod 21369774403) ^ 17 := by rw [pow_add]
          _ = 17179869184 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 21369774403) ^ 69 = 21289265797 := by
        calc
          (2 : ZMod 21369774403) ^ 69 = (2 : ZMod 21369774403) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 34 * (2 : ZMod 21369774403) ^ 34) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 21289265797 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 21369774403) ^ 139 = 2841101821 := by
        calc
          (2 : ZMod 21369774403) ^ 139 = (2 : ZMod 21369774403) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 69 * (2 : ZMod 21369774403) ^ 69) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 2841101821 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 21369774403) ^ 279 = 15760081688 := by
        calc
          (2 : ZMod 21369774403) ^ 279 = (2 : ZMod 21369774403) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 139 * (2 : ZMod 21369774403) ^ 139) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 15760081688 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 21369774403) ^ 559 = 7362191699 := by
        calc
          (2 : ZMod 21369774403) ^ 559 = (2 : ZMod 21369774403) ^ (279 + 279 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 279 * (2 : ZMod 21369774403) ^ 279) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 7362191699 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 21369774403) ^ 1118 = 7604416453 := by
        calc
          (2 : ZMod 21369774403) ^ 1118 = (2 : ZMod 21369774403) ^ (559 + 559) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 559 * (2 : ZMod 21369774403) ^ 559 := by rw [pow_add]
          _ = 7604416453 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 21369774403) ^ 2237 = 19770551589 := by
        calc
          (2 : ZMod 21369774403) ^ 2237 = (2 : ZMod 21369774403) ^ (1118 + 1118 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 1118 * (2 : ZMod 21369774403) ^ 1118) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 19770551589 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 21369774403) ^ 4474 = 14755276745 := by
        calc
          (2 : ZMod 21369774403) ^ 4474 = (2 : ZMod 21369774403) ^ (2237 + 2237) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 2237 * (2 : ZMod 21369774403) ^ 2237 := by rw [pow_add]
          _ = 14755276745 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 21369774403) ^ 8949 = 3354860136 := by
        calc
          (2 : ZMod 21369774403) ^ 8949 = (2 : ZMod 21369774403) ^ (4474 + 4474 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 4474 * (2 : ZMod 21369774403) ^ 4474) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 3354860136 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 21369774403) ^ 17899 = 9134549902 := by
        calc
          (2 : ZMod 21369774403) ^ 17899 = (2 : ZMod 21369774403) ^ (8949 + 8949 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 8949 * (2 : ZMod 21369774403) ^ 8949) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 9134549902 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 21369774403) ^ 35798 = 10408647658 := by
        calc
          (2 : ZMod 21369774403) ^ 35798 = (2 : ZMod 21369774403) ^ (17899 + 17899) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 17899 * (2 : ZMod 21369774403) ^ 17899 := by rw [pow_add]
          _ = 10408647658 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 21369774403) ^ 71597 = 20877610080 := by
        calc
          (2 : ZMod 21369774403) ^ 71597 = (2 : ZMod 21369774403) ^ (35798 + 35798 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 35798 * (2 : ZMod 21369774403) ^ 35798) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 20877610080 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 21369774403) ^ 143194 = 11808824225 := by
        calc
          (2 : ZMod 21369774403) ^ 143194 = (2 : ZMod 21369774403) ^ (71597 + 71597) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 71597 * (2 : ZMod 21369774403) ^ 71597 := by rw [pow_add]
          _ = 11808824225 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 21369774403) ^ 286389 = 8276378675 := by
        calc
          (2 : ZMod 21369774403) ^ 286389 = (2 : ZMod 21369774403) ^ (143194 + 143194 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = ((2 : ZMod 21369774403) ^ 143194 * (2 : ZMod 21369774403) ^ 143194) * (2 : ZMod 21369774403) := by rw [pow_succ, pow_add]
          _ = 8276378675 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 21369774403) ^ 572778 = 1030980040 := by
        calc
          (2 : ZMod 21369774403) ^ 572778 = (2 : ZMod 21369774403) ^ (286389 + 286389) :=
            congrArg (fun n : ℕ => (2 : ZMod 21369774403) ^ n) (by norm_num)
          _ = (2 : ZMod 21369774403) ^ 286389 * (2 : ZMod 21369774403) ^ 286389 := by rw [pow_add]
          _ = 1030980040 := by rw [factor_3_18]; decide
      change (2 : ZMod 21369774403) ^ 572778 ≠ 1
      rw [factor_3_19]
      decide

#print axioms prime_lucas_21369774403

end TotientTailPeriodKiller
end Erdos249257
