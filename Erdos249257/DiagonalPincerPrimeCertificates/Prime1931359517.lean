import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1931359517 : Nat.Prime 1931359517 := by
  apply lucas_primality 1931359517 (2 : ZMod 1931359517)
  ·
      have fermat_0 : (2 : ZMod 1931359517) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1931359517) ^ 3 = 8 := by
        calc
          (2 : ZMod 1931359517) ^ 3 = (2 : ZMod 1931359517) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 1 * (2 : ZMod 1931359517) ^ 1) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1931359517) ^ 7 = 128 := by
        calc
          (2 : ZMod 1931359517) ^ 7 = (2 : ZMod 1931359517) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 3 * (2 : ZMod 1931359517) ^ 3) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1931359517) ^ 14 = 16384 := by
        calc
          (2 : ZMod 1931359517) ^ 14 = (2 : ZMod 1931359517) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 7 * (2 : ZMod 1931359517) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1931359517) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 1931359517) ^ 28 = (2 : ZMod 1931359517) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 14 * (2 : ZMod 1931359517) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1931359517) ^ 57 = 1260760549 := by
        calc
          (2 : ZMod 1931359517) ^ 57 = (2 : ZMod 1931359517) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 28 * (2 : ZMod 1931359517) ^ 28) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1260760549 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1931359517) ^ 115 = 1302423561 := by
        calc
          (2 : ZMod 1931359517) ^ 115 = (2 : ZMod 1931359517) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 57 * (2 : ZMod 1931359517) ^ 57) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1302423561 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1931359517) ^ 230 = 1603256945 := by
        calc
          (2 : ZMod 1931359517) ^ 230 = (2 : ZMod 1931359517) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 115 * (2 : ZMod 1931359517) ^ 115 := by rw [pow_add]
          _ = 1603256945 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1931359517) ^ 460 = 933804297 := by
        calc
          (2 : ZMod 1931359517) ^ 460 = (2 : ZMod 1931359517) ^ (230 + 230) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 230 * (2 : ZMod 1931359517) ^ 230 := by rw [pow_add]
          _ = 933804297 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1931359517) ^ 920 = 742373294 := by
        calc
          (2 : ZMod 1931359517) ^ 920 = (2 : ZMod 1931359517) ^ (460 + 460) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 460 * (2 : ZMod 1931359517) ^ 460 := by rw [pow_add]
          _ = 742373294 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1931359517) ^ 1841 = 813656177 := by
        calc
          (2 : ZMod 1931359517) ^ 1841 = (2 : ZMod 1931359517) ^ (920 + 920 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 920 * (2 : ZMod 1931359517) ^ 920) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 813656177 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1931359517) ^ 3683 = 734870863 := by
        calc
          (2 : ZMod 1931359517) ^ 3683 = (2 : ZMod 1931359517) ^ (1841 + 1841 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 1841 * (2 : ZMod 1931359517) ^ 1841) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 734870863 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1931359517) ^ 7367 = 384506096 := by
        calc
          (2 : ZMod 1931359517) ^ 7367 = (2 : ZMod 1931359517) ^ (3683 + 3683 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 3683 * (2 : ZMod 1931359517) ^ 3683) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 384506096 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1931359517) ^ 14735 = 641465584 := by
        calc
          (2 : ZMod 1931359517) ^ 14735 = (2 : ZMod 1931359517) ^ (7367 + 7367 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 7367 * (2 : ZMod 1931359517) ^ 7367) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 641465584 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1931359517) ^ 29470 = 1617858403 := by
        calc
          (2 : ZMod 1931359517) ^ 29470 = (2 : ZMod 1931359517) ^ (14735 + 14735) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 14735 * (2 : ZMod 1931359517) ^ 14735 := by rw [pow_add]
          _ = 1617858403 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1931359517) ^ 58940 = 701166159 := by
        calc
          (2 : ZMod 1931359517) ^ 58940 = (2 : ZMod 1931359517) ^ (29470 + 29470) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 29470 * (2 : ZMod 1931359517) ^ 29470 := by rw [pow_add]
          _ = 701166159 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1931359517) ^ 117880 = 1498147807 := by
        calc
          (2 : ZMod 1931359517) ^ 117880 = (2 : ZMod 1931359517) ^ (58940 + 58940) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 58940 * (2 : ZMod 1931359517) ^ 58940 := by rw [pow_add]
          _ = 1498147807 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1931359517) ^ 235761 = 1818678814 := by
        calc
          (2 : ZMod 1931359517) ^ 235761 = (2 : ZMod 1931359517) ^ (117880 + 117880 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 117880 * (2 : ZMod 1931359517) ^ 117880) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1818678814 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1931359517) ^ 471523 = 1700683705 := by
        calc
          (2 : ZMod 1931359517) ^ 471523 = (2 : ZMod 1931359517) ^ (235761 + 235761 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 235761 * (2 : ZMod 1931359517) ^ 235761) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1700683705 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1931359517) ^ 943046 = 1907662951 := by
        calc
          (2 : ZMod 1931359517) ^ 943046 = (2 : ZMod 1931359517) ^ (471523 + 471523) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 471523 * (2 : ZMod 1931359517) ^ 471523 := by rw [pow_add]
          _ = 1907662951 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1931359517) ^ 1886093 = 1754361001 := by
        calc
          (2 : ZMod 1931359517) ^ 1886093 = (2 : ZMod 1931359517) ^ (943046 + 943046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 943046 * (2 : ZMod 1931359517) ^ 943046) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1754361001 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1931359517) ^ 3772186 = 97078208 := by
        calc
          (2 : ZMod 1931359517) ^ 3772186 = (2 : ZMod 1931359517) ^ (1886093 + 1886093) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 1886093 * (2 : ZMod 1931359517) ^ 1886093 := by rw [pow_add]
          _ = 97078208 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1931359517) ^ 7544373 = 1166954107 := by
        calc
          (2 : ZMod 1931359517) ^ 7544373 = (2 : ZMod 1931359517) ^ (3772186 + 3772186 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 3772186 * (2 : ZMod 1931359517) ^ 3772186) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1166954107 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1931359517) ^ 15088746 = 1931338434 := by
        calc
          (2 : ZMod 1931359517) ^ 15088746 = (2 : ZMod 1931359517) ^ (7544373 + 7544373) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 7544373 * (2 : ZMod 1931359517) ^ 7544373 := by rw [pow_add]
          _ = 1931338434 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1931359517) ^ 30177492 = 444492889 := by
        calc
          (2 : ZMod 1931359517) ^ 30177492 = (2 : ZMod 1931359517) ^ (15088746 + 15088746) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 15088746 * (2 : ZMod 1931359517) ^ 15088746 := by rw [pow_add]
          _ = 444492889 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1931359517) ^ 60354984 = 274068354 := by
        calc
          (2 : ZMod 1931359517) ^ 60354984 = (2 : ZMod 1931359517) ^ (30177492 + 30177492) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 30177492 * (2 : ZMod 1931359517) ^ 30177492 := by rw [pow_add]
          _ = 274068354 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1931359517) ^ 120709969 = 1537244251 := by
        calc
          (2 : ZMod 1931359517) ^ 120709969 = (2 : ZMod 1931359517) ^ (60354984 + 60354984 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 60354984 * (2 : ZMod 1931359517) ^ 60354984) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1537244251 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1931359517) ^ 241419939 = 265517860 := by
        calc
          (2 : ZMod 1931359517) ^ 241419939 = (2 : ZMod 1931359517) ^ (120709969 + 120709969 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 120709969 * (2 : ZMod 1931359517) ^ 120709969) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 265517860 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1931359517) ^ 482839879 = 531035719 := by
        calc
          (2 : ZMod 1931359517) ^ 482839879 = (2 : ZMod 1931359517) ^ (241419939 + 241419939 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 241419939 * (2 : ZMod 1931359517) ^ 241419939) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 531035719 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1931359517) ^ 965679758 = 1931359516 := by
        calc
          (2 : ZMod 1931359517) ^ 965679758 = (2 : ZMod 1931359517) ^ (482839879 + 482839879) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 482839879 * (2 : ZMod 1931359517) ^ 482839879 := by rw [pow_add]
          _ = 1931359516 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1931359517) ^ 1931359516 = 1 := by
        calc
          (2 : ZMod 1931359517) ^ 1931359516 = (2 : ZMod 1931359517) ^ (965679758 + 965679758) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 965679758 * (2 : ZMod 1931359517) ^ 965679758 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (16649651, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (16649651, 1)] : List FactorBlock).map factorBlockValue).prod = 1931359517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1931359517) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1931359517) ^ 3 = 8 := by
        calc
          (2 : ZMod 1931359517) ^ 3 = (2 : ZMod 1931359517) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 1 * (2 : ZMod 1931359517) ^ 1) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1931359517) ^ 7 = 128 := by
        calc
          (2 : ZMod 1931359517) ^ 7 = (2 : ZMod 1931359517) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 3 * (2 : ZMod 1931359517) ^ 3) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1931359517) ^ 14 = 16384 := by
        calc
          (2 : ZMod 1931359517) ^ 14 = (2 : ZMod 1931359517) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 7 * (2 : ZMod 1931359517) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1931359517) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 1931359517) ^ 28 = (2 : ZMod 1931359517) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 14 * (2 : ZMod 1931359517) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1931359517) ^ 57 = 1260760549 := by
        calc
          (2 : ZMod 1931359517) ^ 57 = (2 : ZMod 1931359517) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 28 * (2 : ZMod 1931359517) ^ 28) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1260760549 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1931359517) ^ 115 = 1302423561 := by
        calc
          (2 : ZMod 1931359517) ^ 115 = (2 : ZMod 1931359517) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 57 * (2 : ZMod 1931359517) ^ 57) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1302423561 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1931359517) ^ 230 = 1603256945 := by
        calc
          (2 : ZMod 1931359517) ^ 230 = (2 : ZMod 1931359517) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 115 * (2 : ZMod 1931359517) ^ 115 := by rw [pow_add]
          _ = 1603256945 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1931359517) ^ 460 = 933804297 := by
        calc
          (2 : ZMod 1931359517) ^ 460 = (2 : ZMod 1931359517) ^ (230 + 230) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 230 * (2 : ZMod 1931359517) ^ 230 := by rw [pow_add]
          _ = 933804297 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1931359517) ^ 920 = 742373294 := by
        calc
          (2 : ZMod 1931359517) ^ 920 = (2 : ZMod 1931359517) ^ (460 + 460) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 460 * (2 : ZMod 1931359517) ^ 460 := by rw [pow_add]
          _ = 742373294 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1931359517) ^ 1841 = 813656177 := by
        calc
          (2 : ZMod 1931359517) ^ 1841 = (2 : ZMod 1931359517) ^ (920 + 920 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 920 * (2 : ZMod 1931359517) ^ 920) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 813656177 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1931359517) ^ 3683 = 734870863 := by
        calc
          (2 : ZMod 1931359517) ^ 3683 = (2 : ZMod 1931359517) ^ (1841 + 1841 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 1841 * (2 : ZMod 1931359517) ^ 1841) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 734870863 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1931359517) ^ 7367 = 384506096 := by
        calc
          (2 : ZMod 1931359517) ^ 7367 = (2 : ZMod 1931359517) ^ (3683 + 3683 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 3683 * (2 : ZMod 1931359517) ^ 3683) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 384506096 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1931359517) ^ 14735 = 641465584 := by
        calc
          (2 : ZMod 1931359517) ^ 14735 = (2 : ZMod 1931359517) ^ (7367 + 7367 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 7367 * (2 : ZMod 1931359517) ^ 7367) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 641465584 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1931359517) ^ 29470 = 1617858403 := by
        calc
          (2 : ZMod 1931359517) ^ 29470 = (2 : ZMod 1931359517) ^ (14735 + 14735) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 14735 * (2 : ZMod 1931359517) ^ 14735 := by rw [pow_add]
          _ = 1617858403 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1931359517) ^ 58940 = 701166159 := by
        calc
          (2 : ZMod 1931359517) ^ 58940 = (2 : ZMod 1931359517) ^ (29470 + 29470) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 29470 * (2 : ZMod 1931359517) ^ 29470 := by rw [pow_add]
          _ = 701166159 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1931359517) ^ 117880 = 1498147807 := by
        calc
          (2 : ZMod 1931359517) ^ 117880 = (2 : ZMod 1931359517) ^ (58940 + 58940) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 58940 * (2 : ZMod 1931359517) ^ 58940 := by rw [pow_add]
          _ = 1498147807 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1931359517) ^ 235761 = 1818678814 := by
        calc
          (2 : ZMod 1931359517) ^ 235761 = (2 : ZMod 1931359517) ^ (117880 + 117880 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 117880 * (2 : ZMod 1931359517) ^ 117880) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1818678814 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1931359517) ^ 471523 = 1700683705 := by
        calc
          (2 : ZMod 1931359517) ^ 471523 = (2 : ZMod 1931359517) ^ (235761 + 235761 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 235761 * (2 : ZMod 1931359517) ^ 235761) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1700683705 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1931359517) ^ 943046 = 1907662951 := by
        calc
          (2 : ZMod 1931359517) ^ 943046 = (2 : ZMod 1931359517) ^ (471523 + 471523) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 471523 * (2 : ZMod 1931359517) ^ 471523 := by rw [pow_add]
          _ = 1907662951 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1931359517) ^ 1886093 = 1754361001 := by
        calc
          (2 : ZMod 1931359517) ^ 1886093 = (2 : ZMod 1931359517) ^ (943046 + 943046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 943046 * (2 : ZMod 1931359517) ^ 943046) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1754361001 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1931359517) ^ 3772186 = 97078208 := by
        calc
          (2 : ZMod 1931359517) ^ 3772186 = (2 : ZMod 1931359517) ^ (1886093 + 1886093) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 1886093 * (2 : ZMod 1931359517) ^ 1886093 := by rw [pow_add]
          _ = 97078208 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1931359517) ^ 7544373 = 1166954107 := by
        calc
          (2 : ZMod 1931359517) ^ 7544373 = (2 : ZMod 1931359517) ^ (3772186 + 3772186 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 3772186 * (2 : ZMod 1931359517) ^ 3772186) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1166954107 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1931359517) ^ 15088746 = 1931338434 := by
        calc
          (2 : ZMod 1931359517) ^ 15088746 = (2 : ZMod 1931359517) ^ (7544373 + 7544373) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 7544373 * (2 : ZMod 1931359517) ^ 7544373 := by rw [pow_add]
          _ = 1931338434 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1931359517) ^ 30177492 = 444492889 := by
        calc
          (2 : ZMod 1931359517) ^ 30177492 = (2 : ZMod 1931359517) ^ (15088746 + 15088746) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 15088746 * (2 : ZMod 1931359517) ^ 15088746 := by rw [pow_add]
          _ = 444492889 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1931359517) ^ 60354984 = 274068354 := by
        calc
          (2 : ZMod 1931359517) ^ 60354984 = (2 : ZMod 1931359517) ^ (30177492 + 30177492) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 30177492 * (2 : ZMod 1931359517) ^ 30177492 := by rw [pow_add]
          _ = 274068354 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1931359517) ^ 120709969 = 1537244251 := by
        calc
          (2 : ZMod 1931359517) ^ 120709969 = (2 : ZMod 1931359517) ^ (60354984 + 60354984 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 60354984 * (2 : ZMod 1931359517) ^ 60354984) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1537244251 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1931359517) ^ 241419939 = 265517860 := by
        calc
          (2 : ZMod 1931359517) ^ 241419939 = (2 : ZMod 1931359517) ^ (120709969 + 120709969 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 120709969 * (2 : ZMod 1931359517) ^ 120709969) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 265517860 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1931359517) ^ 482839879 = 531035719 := by
        calc
          (2 : ZMod 1931359517) ^ 482839879 = (2 : ZMod 1931359517) ^ (241419939 + 241419939 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 241419939 * (2 : ZMod 1931359517) ^ 241419939) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 531035719 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1931359517) ^ 965679758 = 1931359516 := by
        calc
          (2 : ZMod 1931359517) ^ 965679758 = (2 : ZMod 1931359517) ^ (482839879 + 482839879) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 482839879 * (2 : ZMod 1931359517) ^ 482839879 := by rw [pow_add]
          _ = 1931359516 := by rw [factor_0_28]; decide
      change (2 : ZMod 1931359517) ^ 965679758 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1931359517) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1931359517) ^ 3 = 8 := by
        calc
          (2 : ZMod 1931359517) ^ 3 = (2 : ZMod 1931359517) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 1 * (2 : ZMod 1931359517) ^ 1) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1931359517) ^ 7 = 128 := by
        calc
          (2 : ZMod 1931359517) ^ 7 = (2 : ZMod 1931359517) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 3 * (2 : ZMod 1931359517) ^ 3) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1931359517) ^ 15 = 32768 := by
        calc
          (2 : ZMod 1931359517) ^ 15 = (2 : ZMod 1931359517) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 7 * (2 : ZMod 1931359517) ^ 7) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1931359517) ^ 31 = 216124131 := by
        calc
          (2 : ZMod 1931359517) ^ 31 = (2 : ZMod 1931359517) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 15 * (2 : ZMod 1931359517) ^ 15) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 216124131 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1931359517) ^ 63 = 1502934939 := by
        calc
          (2 : ZMod 1931359517) ^ 63 = (2 : ZMod 1931359517) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 31 * (2 : ZMod 1931359517) ^ 31) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1502934939 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1931359517) ^ 127 = 311919902 := by
        calc
          (2 : ZMod 1931359517) ^ 127 = (2 : ZMod 1931359517) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 63 * (2 : ZMod 1931359517) ^ 63) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 311919902 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1931359517) ^ 254 = 1155901862 := by
        calc
          (2 : ZMod 1931359517) ^ 254 = (2 : ZMod 1931359517) ^ (127 + 127) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 127 * (2 : ZMod 1931359517) ^ 127 := by rw [pow_add]
          _ = 1155901862 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1931359517) ^ 508 = 795676576 := by
        calc
          (2 : ZMod 1931359517) ^ 508 = (2 : ZMod 1931359517) ^ (254 + 254) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 254 * (2 : ZMod 1931359517) ^ 254 := by rw [pow_add]
          _ = 795676576 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1931359517) ^ 1016 = 1452634523 := by
        calc
          (2 : ZMod 1931359517) ^ 1016 = (2 : ZMod 1931359517) ^ (508 + 508) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 508 * (2 : ZMod 1931359517) ^ 508 := by rw [pow_add]
          _ = 1452634523 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1931359517) ^ 2032 = 413865038 := by
        calc
          (2 : ZMod 1931359517) ^ 2032 = (2 : ZMod 1931359517) ^ (1016 + 1016) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 1016 * (2 : ZMod 1931359517) ^ 1016 := by rw [pow_add]
          _ = 413865038 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1931359517) ^ 4064 = 1532568926 := by
        calc
          (2 : ZMod 1931359517) ^ 4064 = (2 : ZMod 1931359517) ^ (2032 + 2032) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 2032 * (2 : ZMod 1931359517) ^ 2032 := by rw [pow_add]
          _ = 1532568926 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1931359517) ^ 8129 = 1386315596 := by
        calc
          (2 : ZMod 1931359517) ^ 8129 = (2 : ZMod 1931359517) ^ (4064 + 4064 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 4064 * (2 : ZMod 1931359517) ^ 4064) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1386315596 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1931359517) ^ 16259 = 1081404202 := by
        calc
          (2 : ZMod 1931359517) ^ 16259 = (2 : ZMod 1931359517) ^ (8129 + 8129 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 8129 * (2 : ZMod 1931359517) ^ 8129) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1081404202 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1931359517) ^ 32518 = 950331446 := by
        calc
          (2 : ZMod 1931359517) ^ 32518 = (2 : ZMod 1931359517) ^ (16259 + 16259) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 16259 * (2 : ZMod 1931359517) ^ 16259 := by rw [pow_add]
          _ = 950331446 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1931359517) ^ 65037 = 724219540 := by
        calc
          (2 : ZMod 1931359517) ^ 65037 = (2 : ZMod 1931359517) ^ (32518 + 32518 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 32518 * (2 : ZMod 1931359517) ^ 32518) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 724219540 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1931359517) ^ 130075 = 1011641101 := by
        calc
          (2 : ZMod 1931359517) ^ 130075 = (2 : ZMod 1931359517) ^ (65037 + 65037 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 65037 * (2 : ZMod 1931359517) ^ 65037) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 1011641101 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1931359517) ^ 260150 = 736248507 := by
        calc
          (2 : ZMod 1931359517) ^ 260150 = (2 : ZMod 1931359517) ^ (130075 + 130075) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 130075 * (2 : ZMod 1931359517) ^ 130075 := by rw [pow_add]
          _ = 736248507 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1931359517) ^ 520301 = 193390137 := by
        calc
          (2 : ZMod 1931359517) ^ 520301 = (2 : ZMod 1931359517) ^ (260150 + 260150 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 260150 * (2 : ZMod 1931359517) ^ 260150) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 193390137 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1931359517) ^ 1040603 = 707671211 := by
        calc
          (2 : ZMod 1931359517) ^ 1040603 = (2 : ZMod 1931359517) ^ (520301 + 520301 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 520301 * (2 : ZMod 1931359517) ^ 520301) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 707671211 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1931359517) ^ 2081206 = 207841252 := by
        calc
          (2 : ZMod 1931359517) ^ 2081206 = (2 : ZMod 1931359517) ^ (1040603 + 1040603) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 1040603 * (2 : ZMod 1931359517) ^ 1040603 := by rw [pow_add]
          _ = 207841252 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1931359517) ^ 4162412 = 1632804964 := by
        calc
          (2 : ZMod 1931359517) ^ 4162412 = (2 : ZMod 1931359517) ^ (2081206 + 2081206) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 2081206 * (2 : ZMod 1931359517) ^ 2081206 := by rw [pow_add]
          _ = 1632804964 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1931359517) ^ 8324825 = 153689711 := by
        calc
          (2 : ZMod 1931359517) ^ 8324825 = (2 : ZMod 1931359517) ^ (4162412 + 4162412 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 4162412 * (2 : ZMod 1931359517) ^ 4162412) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 153689711 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1931359517) ^ 16649651 = 748707042 := by
        calc
          (2 : ZMod 1931359517) ^ 16649651 = (2 : ZMod 1931359517) ^ (8324825 + 8324825 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 8324825 * (2 : ZMod 1931359517) ^ 8324825) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 748707042 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1931359517) ^ 33299302 = 605342113 := by
        calc
          (2 : ZMod 1931359517) ^ 33299302 = (2 : ZMod 1931359517) ^ (16649651 + 16649651) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 16649651 * (2 : ZMod 1931359517) ^ 16649651 := by rw [pow_add]
          _ = 605342113 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1931359517) ^ 66598604 = 1890652634 := by
        calc
          (2 : ZMod 1931359517) ^ 66598604 = (2 : ZMod 1931359517) ^ (33299302 + 33299302) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 33299302 * (2 : ZMod 1931359517) ^ 33299302 := by rw [pow_add]
          _ = 1890652634 := by rw [factor_1_24]; decide
      change (2 : ZMod 1931359517) ^ 66598604 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1931359517) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1931359517) ^ 3 = 8 := by
        calc
          (2 : ZMod 1931359517) ^ 3 = (2 : ZMod 1931359517) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 1 * (2 : ZMod 1931359517) ^ 1) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1931359517) ^ 7 = 128 := by
        calc
          (2 : ZMod 1931359517) ^ 7 = (2 : ZMod 1931359517) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 3 * (2 : ZMod 1931359517) ^ 3) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1931359517) ^ 14 = 16384 := by
        calc
          (2 : ZMod 1931359517) ^ 14 = (2 : ZMod 1931359517) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 7 * (2 : ZMod 1931359517) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1931359517) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 1931359517) ^ 29 = (2 : ZMod 1931359517) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = ((2 : ZMod 1931359517) ^ 14 * (2 : ZMod 1931359517) ^ 14) * (2 : ZMod 1931359517) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1931359517) ^ 58 = 590161581 := by
        calc
          (2 : ZMod 1931359517) ^ 58 = (2 : ZMod 1931359517) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 29 * (2 : ZMod 1931359517) ^ 29 := by rw [pow_add]
          _ = 590161581 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1931359517) ^ 116 = 673487605 := by
        calc
          (2 : ZMod 1931359517) ^ 116 = (2 : ZMod 1931359517) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (2 : ZMod 1931359517) ^ n) (by norm_num)
          _ = (2 : ZMod 1931359517) ^ 58 * (2 : ZMod 1931359517) ^ 58 := by rw [pow_add]
          _ = 673487605 := by rw [factor_2_5]; decide
      change (2 : ZMod 1931359517) ^ 116 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_1931359517

end TotientTailPeriodKiller
end Erdos249257
