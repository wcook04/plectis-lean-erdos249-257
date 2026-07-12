import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1795455707 : Nat.Prime 1795455707 := by
  apply lucas_primality 1795455707 (2 : ZMod 1795455707)
  ·
      have fermat_0 : (2 : ZMod 1795455707) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1795455707) ^ 3 = 8 := by
        calc
          (2 : ZMod 1795455707) ^ 3 = (2 : ZMod 1795455707) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 1 * (2 : ZMod 1795455707) ^ 1) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1795455707) ^ 6 = 64 := by
        calc
          (2 : ZMod 1795455707) ^ 6 = (2 : ZMod 1795455707) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 3 * (2 : ZMod 1795455707) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1795455707) ^ 13 = 8192 := by
        calc
          (2 : ZMod 1795455707) ^ 13 = (2 : ZMod 1795455707) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 6 * (2 : ZMod 1795455707) ^ 6) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1795455707) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 1795455707) ^ 26 = (2 : ZMod 1795455707) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 13 * (2 : ZMod 1795455707) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1795455707) ^ 53 = 1245839544 := by
        calc
          (2 : ZMod 1795455707) ^ 53 = (2 : ZMod 1795455707) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 26 * (2 : ZMod 1795455707) ^ 26) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1245839544 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1795455707) ^ 107 = 1706794295 := by
        calc
          (2 : ZMod 1795455707) ^ 107 = (2 : ZMod 1795455707) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 53 * (2 : ZMod 1795455707) ^ 53) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1706794295 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1795455707) ^ 214 = 1551459121 := by
        calc
          (2 : ZMod 1795455707) ^ 214 = (2 : ZMod 1795455707) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 107 * (2 : ZMod 1795455707) ^ 107 := by rw [pow_add]
          _ = 1551459121 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1795455707) ^ 428 = 1396553309 := by
        calc
          (2 : ZMod 1795455707) ^ 428 = (2 : ZMod 1795455707) ^ (214 + 214) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 214 * (2 : ZMod 1795455707) ^ 214 := by rw [pow_add]
          _ = 1396553309 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1795455707) ^ 856 = 1073991751 := by
        calc
          (2 : ZMod 1795455707) ^ 856 = (2 : ZMod 1795455707) ^ (428 + 428) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 428 * (2 : ZMod 1795455707) ^ 428 := by rw [pow_add]
          _ = 1073991751 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1795455707) ^ 1712 = 1456570893 := by
        calc
          (2 : ZMod 1795455707) ^ 1712 = (2 : ZMod 1795455707) ^ (856 + 856) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 856 * (2 : ZMod 1795455707) ^ 856 := by rw [pow_add]
          _ = 1456570893 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1795455707) ^ 3424 = 636491482 := by
        calc
          (2 : ZMod 1795455707) ^ 3424 = (2 : ZMod 1795455707) ^ (1712 + 1712) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 1712 * (2 : ZMod 1795455707) ^ 1712 := by rw [pow_add]
          _ = 636491482 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1795455707) ^ 6849 = 641633146 := by
        calc
          (2 : ZMod 1795455707) ^ 6849 = (2 : ZMod 1795455707) ^ (3424 + 3424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 3424 * (2 : ZMod 1795455707) ^ 3424) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 641633146 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1795455707) ^ 13698 = 229381719 := by
        calc
          (2 : ZMod 1795455707) ^ 13698 = (2 : ZMod 1795455707) ^ (6849 + 6849) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 6849 * (2 : ZMod 1795455707) ^ 6849 := by rw [pow_add]
          _ = 229381719 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1795455707) ^ 27396 = 1676759108 := by
        calc
          (2 : ZMod 1795455707) ^ 27396 = (2 : ZMod 1795455707) ^ (13698 + 13698) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 13698 * (2 : ZMod 1795455707) ^ 13698 := by rw [pow_add]
          _ = 1676759108 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1795455707) ^ 54792 = 931376132 := by
        calc
          (2 : ZMod 1795455707) ^ 54792 = (2 : ZMod 1795455707) ^ (27396 + 27396) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 27396 * (2 : ZMod 1795455707) ^ 27396 := by rw [pow_add]
          _ = 931376132 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1795455707) ^ 109585 = 1611187941 := by
        calc
          (2 : ZMod 1795455707) ^ 109585 = (2 : ZMod 1795455707) ^ (54792 + 54792 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 54792 * (2 : ZMod 1795455707) ^ 54792) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1611187941 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1795455707) ^ 219171 = 1399414995 := by
        calc
          (2 : ZMod 1795455707) ^ 219171 = (2 : ZMod 1795455707) ^ (109585 + 109585 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 109585 * (2 : ZMod 1795455707) ^ 109585) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1399414995 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1795455707) ^ 438343 = 1794927155 := by
        calc
          (2 : ZMod 1795455707) ^ 438343 = (2 : ZMod 1795455707) ^ (219171 + 219171 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 219171 * (2 : ZMod 1795455707) ^ 219171) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1794927155 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1795455707) ^ 876687 = 347708531 := by
        calc
          (2 : ZMod 1795455707) ^ 876687 = (2 : ZMod 1795455707) ^ (438343 + 438343 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 438343 * (2 : ZMod 1795455707) ^ 438343) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 347708531 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1795455707) ^ 1753374 = 360244339 := by
        calc
          (2 : ZMod 1795455707) ^ 1753374 = (2 : ZMod 1795455707) ^ (876687 + 876687) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 876687 * (2 : ZMod 1795455707) ^ 876687 := by rw [pow_add]
          _ = 360244339 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1795455707) ^ 3506749 = 13143170 := by
        calc
          (2 : ZMod 1795455707) ^ 3506749 = (2 : ZMod 1795455707) ^ (1753374 + 1753374 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 1753374 * (2 : ZMod 1795455707) ^ 1753374) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 13143170 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1795455707) ^ 7013498 = 328622723 := by
        calc
          (2 : ZMod 1795455707) ^ 7013498 = (2 : ZMod 1795455707) ^ (3506749 + 3506749) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 3506749 * (2 : ZMod 1795455707) ^ 3506749 := by rw [pow_add]
          _ = 328622723 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1795455707) ^ 14026997 = 323916030 := by
        calc
          (2 : ZMod 1795455707) ^ 14026997 = (2 : ZMod 1795455707) ^ (7013498 + 7013498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 7013498 * (2 : ZMod 1795455707) ^ 7013498) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 323916030 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1795455707) ^ 28053995 = 1658566823 := by
        calc
          (2 : ZMod 1795455707) ^ 28053995 = (2 : ZMod 1795455707) ^ (14026997 + 14026997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 14026997 * (2 : ZMod 1795455707) ^ 14026997) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1658566823 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1795455707) ^ 56107990 = 417379715 := by
        calc
          (2 : ZMod 1795455707) ^ 56107990 = (2 : ZMod 1795455707) ^ (28053995 + 28053995) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 28053995 * (2 : ZMod 1795455707) ^ 28053995 := by rw [pow_add]
          _ = 417379715 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1795455707) ^ 112215981 = 632275112 := by
        calc
          (2 : ZMod 1795455707) ^ 112215981 = (2 : ZMod 1795455707) ^ (56107990 + 56107990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 56107990 * (2 : ZMod 1795455707) ^ 56107990) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 632275112 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1795455707) ^ 224431963 = 1641796917 := by
        calc
          (2 : ZMod 1795455707) ^ 224431963 = (2 : ZMod 1795455707) ^ (112215981 + 112215981 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 112215981 * (2 : ZMod 1795455707) ^ 112215981) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1641796917 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1795455707) ^ 448863926 = 173981555 := by
        calc
          (2 : ZMod 1795455707) ^ 448863926 = (2 : ZMod 1795455707) ^ (224431963 + 224431963) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 224431963 * (2 : ZMod 1795455707) ^ 224431963 := by rw [pow_add]
          _ = 173981555 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1795455707) ^ 897727853 = 1795455706 := by
        calc
          (2 : ZMod 1795455707) ^ 897727853 = (2 : ZMod 1795455707) ^ (448863926 + 448863926 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 448863926 * (2 : ZMod 1795455707) ^ 448863926) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1795455706 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1795455707) ^ 1795455706 = 1 := by
        calc
          (2 : ZMod 1795455707) ^ 1795455706 = (2 : ZMod 1795455707) ^ (897727853 + 897727853) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 897727853 * (2 : ZMod 1795455707) ^ 897727853 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (31, 1), (2632633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (31, 1), (2632633, 1)] : List FactorBlock).map factorBlockValue).prod = 1795455707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1795455707) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1795455707) ^ 3 = 8 := by
        calc
          (2 : ZMod 1795455707) ^ 3 = (2 : ZMod 1795455707) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 1 * (2 : ZMod 1795455707) ^ 1) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1795455707) ^ 6 = 64 := by
        calc
          (2 : ZMod 1795455707) ^ 6 = (2 : ZMod 1795455707) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 3 * (2 : ZMod 1795455707) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1795455707) ^ 13 = 8192 := by
        calc
          (2 : ZMod 1795455707) ^ 13 = (2 : ZMod 1795455707) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 6 * (2 : ZMod 1795455707) ^ 6) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1795455707) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 1795455707) ^ 26 = (2 : ZMod 1795455707) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 13 * (2 : ZMod 1795455707) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1795455707) ^ 53 = 1245839544 := by
        calc
          (2 : ZMod 1795455707) ^ 53 = (2 : ZMod 1795455707) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 26 * (2 : ZMod 1795455707) ^ 26) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1245839544 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1795455707) ^ 107 = 1706794295 := by
        calc
          (2 : ZMod 1795455707) ^ 107 = (2 : ZMod 1795455707) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 53 * (2 : ZMod 1795455707) ^ 53) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1706794295 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1795455707) ^ 214 = 1551459121 := by
        calc
          (2 : ZMod 1795455707) ^ 214 = (2 : ZMod 1795455707) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 107 * (2 : ZMod 1795455707) ^ 107 := by rw [pow_add]
          _ = 1551459121 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1795455707) ^ 428 = 1396553309 := by
        calc
          (2 : ZMod 1795455707) ^ 428 = (2 : ZMod 1795455707) ^ (214 + 214) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 214 * (2 : ZMod 1795455707) ^ 214 := by rw [pow_add]
          _ = 1396553309 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1795455707) ^ 856 = 1073991751 := by
        calc
          (2 : ZMod 1795455707) ^ 856 = (2 : ZMod 1795455707) ^ (428 + 428) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 428 * (2 : ZMod 1795455707) ^ 428 := by rw [pow_add]
          _ = 1073991751 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1795455707) ^ 1712 = 1456570893 := by
        calc
          (2 : ZMod 1795455707) ^ 1712 = (2 : ZMod 1795455707) ^ (856 + 856) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 856 * (2 : ZMod 1795455707) ^ 856 := by rw [pow_add]
          _ = 1456570893 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1795455707) ^ 3424 = 636491482 := by
        calc
          (2 : ZMod 1795455707) ^ 3424 = (2 : ZMod 1795455707) ^ (1712 + 1712) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 1712 * (2 : ZMod 1795455707) ^ 1712 := by rw [pow_add]
          _ = 636491482 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1795455707) ^ 6849 = 641633146 := by
        calc
          (2 : ZMod 1795455707) ^ 6849 = (2 : ZMod 1795455707) ^ (3424 + 3424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 3424 * (2 : ZMod 1795455707) ^ 3424) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 641633146 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1795455707) ^ 13698 = 229381719 := by
        calc
          (2 : ZMod 1795455707) ^ 13698 = (2 : ZMod 1795455707) ^ (6849 + 6849) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 6849 * (2 : ZMod 1795455707) ^ 6849 := by rw [pow_add]
          _ = 229381719 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1795455707) ^ 27396 = 1676759108 := by
        calc
          (2 : ZMod 1795455707) ^ 27396 = (2 : ZMod 1795455707) ^ (13698 + 13698) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 13698 * (2 : ZMod 1795455707) ^ 13698 := by rw [pow_add]
          _ = 1676759108 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1795455707) ^ 54792 = 931376132 := by
        calc
          (2 : ZMod 1795455707) ^ 54792 = (2 : ZMod 1795455707) ^ (27396 + 27396) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 27396 * (2 : ZMod 1795455707) ^ 27396 := by rw [pow_add]
          _ = 931376132 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1795455707) ^ 109585 = 1611187941 := by
        calc
          (2 : ZMod 1795455707) ^ 109585 = (2 : ZMod 1795455707) ^ (54792 + 54792 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 54792 * (2 : ZMod 1795455707) ^ 54792) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1611187941 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1795455707) ^ 219171 = 1399414995 := by
        calc
          (2 : ZMod 1795455707) ^ 219171 = (2 : ZMod 1795455707) ^ (109585 + 109585 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 109585 * (2 : ZMod 1795455707) ^ 109585) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1399414995 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1795455707) ^ 438343 = 1794927155 := by
        calc
          (2 : ZMod 1795455707) ^ 438343 = (2 : ZMod 1795455707) ^ (219171 + 219171 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 219171 * (2 : ZMod 1795455707) ^ 219171) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1794927155 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1795455707) ^ 876687 = 347708531 := by
        calc
          (2 : ZMod 1795455707) ^ 876687 = (2 : ZMod 1795455707) ^ (438343 + 438343 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 438343 * (2 : ZMod 1795455707) ^ 438343) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 347708531 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1795455707) ^ 1753374 = 360244339 := by
        calc
          (2 : ZMod 1795455707) ^ 1753374 = (2 : ZMod 1795455707) ^ (876687 + 876687) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 876687 * (2 : ZMod 1795455707) ^ 876687 := by rw [pow_add]
          _ = 360244339 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1795455707) ^ 3506749 = 13143170 := by
        calc
          (2 : ZMod 1795455707) ^ 3506749 = (2 : ZMod 1795455707) ^ (1753374 + 1753374 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 1753374 * (2 : ZMod 1795455707) ^ 1753374) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 13143170 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1795455707) ^ 7013498 = 328622723 := by
        calc
          (2 : ZMod 1795455707) ^ 7013498 = (2 : ZMod 1795455707) ^ (3506749 + 3506749) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 3506749 * (2 : ZMod 1795455707) ^ 3506749 := by rw [pow_add]
          _ = 328622723 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1795455707) ^ 14026997 = 323916030 := by
        calc
          (2 : ZMod 1795455707) ^ 14026997 = (2 : ZMod 1795455707) ^ (7013498 + 7013498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 7013498 * (2 : ZMod 1795455707) ^ 7013498) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 323916030 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1795455707) ^ 28053995 = 1658566823 := by
        calc
          (2 : ZMod 1795455707) ^ 28053995 = (2 : ZMod 1795455707) ^ (14026997 + 14026997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 14026997 * (2 : ZMod 1795455707) ^ 14026997) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1658566823 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1795455707) ^ 56107990 = 417379715 := by
        calc
          (2 : ZMod 1795455707) ^ 56107990 = (2 : ZMod 1795455707) ^ (28053995 + 28053995) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 28053995 * (2 : ZMod 1795455707) ^ 28053995 := by rw [pow_add]
          _ = 417379715 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1795455707) ^ 112215981 = 632275112 := by
        calc
          (2 : ZMod 1795455707) ^ 112215981 = (2 : ZMod 1795455707) ^ (56107990 + 56107990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 56107990 * (2 : ZMod 1795455707) ^ 56107990) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 632275112 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1795455707) ^ 224431963 = 1641796917 := by
        calc
          (2 : ZMod 1795455707) ^ 224431963 = (2 : ZMod 1795455707) ^ (112215981 + 112215981 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 112215981 * (2 : ZMod 1795455707) ^ 112215981) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1641796917 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1795455707) ^ 448863926 = 173981555 := by
        calc
          (2 : ZMod 1795455707) ^ 448863926 = (2 : ZMod 1795455707) ^ (224431963 + 224431963) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 224431963 * (2 : ZMod 1795455707) ^ 224431963 := by rw [pow_add]
          _ = 173981555 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1795455707) ^ 897727853 = 1795455706 := by
        calc
          (2 : ZMod 1795455707) ^ 897727853 = (2 : ZMod 1795455707) ^ (448863926 + 448863926 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 448863926 * (2 : ZMod 1795455707) ^ 448863926) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1795455706 := by rw [factor_0_28]; decide
      change (2 : ZMod 1795455707) ^ 897727853 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1795455707) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1795455707) ^ 2 = 4 := by
        calc
          (2 : ZMod 1795455707) ^ 2 = (2 : ZMod 1795455707) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 1 * (2 : ZMod 1795455707) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1795455707) ^ 4 = 16 := by
        calc
          (2 : ZMod 1795455707) ^ 4 = (2 : ZMod 1795455707) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 2 * (2 : ZMod 1795455707) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1795455707) ^ 9 = 512 := by
        calc
          (2 : ZMod 1795455707) ^ 9 = (2 : ZMod 1795455707) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 4 * (2 : ZMod 1795455707) ^ 4) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1795455707) ^ 19 = 524288 := by
        calc
          (2 : ZMod 1795455707) ^ 19 = (2 : ZMod 1795455707) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 9 * (2 : ZMod 1795455707) ^ 9) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1795455707) ^ 38 = 173183773 := by
        calc
          (2 : ZMod 1795455707) ^ 38 = (2 : ZMod 1795455707) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 19 * (2 : ZMod 1795455707) ^ 19 := by rw [pow_add]
          _ = 173183773 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1795455707) ^ 77 = 518040112 := by
        calc
          (2 : ZMod 1795455707) ^ 77 = (2 : ZMod 1795455707) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 38 * (2 : ZMod 1795455707) ^ 38) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 518040112 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1795455707) ^ 155 = 1119291003 := by
        calc
          (2 : ZMod 1795455707) ^ 155 = (2 : ZMod 1795455707) ^ (77 + 77 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 77 * (2 : ZMod 1795455707) ^ 77) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1119291003 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1795455707) ^ 311 = 177580890 := by
        calc
          (2 : ZMod 1795455707) ^ 311 = (2 : ZMod 1795455707) ^ (155 + 155 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 155 * (2 : ZMod 1795455707) ^ 155) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 177580890 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1795455707) ^ 622 = 1410256710 := by
        calc
          (2 : ZMod 1795455707) ^ 622 = (2 : ZMod 1795455707) ^ (311 + 311) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 311 * (2 : ZMod 1795455707) ^ 311 := by rw [pow_add]
          _ = 1410256710 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1795455707) ^ 1245 = 1074313827 := by
        calc
          (2 : ZMod 1795455707) ^ 1245 = (2 : ZMod 1795455707) ^ (622 + 622 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 622 * (2 : ZMod 1795455707) ^ 622) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1074313827 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1795455707) ^ 2490 = 767192817 := by
        calc
          (2 : ZMod 1795455707) ^ 2490 = (2 : ZMod 1795455707) ^ (1245 + 1245) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 1245 * (2 : ZMod 1795455707) ^ 1245 := by rw [pow_add]
          _ = 767192817 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1795455707) ^ 4981 = 1722670458 := by
        calc
          (2 : ZMod 1795455707) ^ 4981 = (2 : ZMod 1795455707) ^ (2490 + 2490 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 2490 * (2 : ZMod 1795455707) ^ 2490) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1722670458 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1795455707) ^ 9962 = 1112905024 := by
        calc
          (2 : ZMod 1795455707) ^ 9962 = (2 : ZMod 1795455707) ^ (4981 + 4981) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 4981 * (2 : ZMod 1795455707) ^ 4981 := by rw [pow_add]
          _ = 1112905024 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1795455707) ^ 19924 = 1585678290 := by
        calc
          (2 : ZMod 1795455707) ^ 19924 = (2 : ZMod 1795455707) ^ (9962 + 9962) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 9962 * (2 : ZMod 1795455707) ^ 9962 := by rw [pow_add]
          _ = 1585678290 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1795455707) ^ 39849 = 132041905 := by
        calc
          (2 : ZMod 1795455707) ^ 39849 = (2 : ZMod 1795455707) ^ (19924 + 19924 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 19924 * (2 : ZMod 1795455707) ^ 19924) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 132041905 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1795455707) ^ 79698 = 1169380991 := by
        calc
          (2 : ZMod 1795455707) ^ 79698 = (2 : ZMod 1795455707) ^ (39849 + 39849) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 39849 * (2 : ZMod 1795455707) ^ 39849 := by rw [pow_add]
          _ = 1169380991 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1795455707) ^ 159397 = 733944930 := by
        calc
          (2 : ZMod 1795455707) ^ 159397 = (2 : ZMod 1795455707) ^ (79698 + 79698 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 79698 * (2 : ZMod 1795455707) ^ 79698) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 733944930 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1795455707) ^ 318795 = 568390404 := by
        calc
          (2 : ZMod 1795455707) ^ 318795 = (2 : ZMod 1795455707) ^ (159397 + 159397 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 159397 * (2 : ZMod 1795455707) ^ 159397) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 568390404 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1795455707) ^ 637590 = 14186237 := by
        calc
          (2 : ZMod 1795455707) ^ 637590 = (2 : ZMod 1795455707) ^ (318795 + 318795) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 318795 * (2 : ZMod 1795455707) ^ 318795 := by rw [pow_add]
          _ = 14186237 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1795455707) ^ 1275181 = 561867906 := by
        calc
          (2 : ZMod 1795455707) ^ 1275181 = (2 : ZMod 1795455707) ^ (637590 + 637590 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 637590 * (2 : ZMod 1795455707) ^ 637590) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 561867906 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1795455707) ^ 2550363 = 729478555 := by
        calc
          (2 : ZMod 1795455707) ^ 2550363 = (2 : ZMod 1795455707) ^ (1275181 + 1275181 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 1275181 * (2 : ZMod 1795455707) ^ 1275181) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 729478555 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1795455707) ^ 5100726 = 717609611 := by
        calc
          (2 : ZMod 1795455707) ^ 5100726 = (2 : ZMod 1795455707) ^ (2550363 + 2550363) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 2550363 * (2 : ZMod 1795455707) ^ 2550363 := by rw [pow_add]
          _ = 717609611 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1795455707) ^ 10201452 = 605506015 := by
        calc
          (2 : ZMod 1795455707) ^ 10201452 = (2 : ZMod 1795455707) ^ (5100726 + 5100726) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 5100726 * (2 : ZMod 1795455707) ^ 5100726 := by rw [pow_add]
          _ = 605506015 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1795455707) ^ 20402905 = 1792836336 := by
        calc
          (2 : ZMod 1795455707) ^ 20402905 = (2 : ZMod 1795455707) ^ (10201452 + 10201452 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 10201452 * (2 : ZMod 1795455707) ^ 10201452) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1792836336 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1795455707) ^ 40805811 = 1336358388 := by
        calc
          (2 : ZMod 1795455707) ^ 40805811 = (2 : ZMod 1795455707) ^ (20402905 + 20402905 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 20402905 * (2 : ZMod 1795455707) ^ 20402905) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1336358388 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1795455707) ^ 81611623 = 461455866 := by
        calc
          (2 : ZMod 1795455707) ^ 81611623 = (2 : ZMod 1795455707) ^ (40805811 + 40805811 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 40805811 * (2 : ZMod 1795455707) ^ 40805811) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 461455866 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1795455707) ^ 163223246 = 801670429 := by
        calc
          (2 : ZMod 1795455707) ^ 163223246 = (2 : ZMod 1795455707) ^ (81611623 + 81611623) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 81611623 * (2 : ZMod 1795455707) ^ 81611623 := by rw [pow_add]
          _ = 801670429 := by rw [factor_1_26]; decide
      change (2 : ZMod 1795455707) ^ 163223246 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1795455707) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1795455707) ^ 3 = 8 := by
        calc
          (2 : ZMod 1795455707) ^ 3 = (2 : ZMod 1795455707) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 1 * (2 : ZMod 1795455707) ^ 1) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1795455707) ^ 6 = 64 := by
        calc
          (2 : ZMod 1795455707) ^ 6 = (2 : ZMod 1795455707) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 3 * (2 : ZMod 1795455707) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1795455707) ^ 13 = 8192 := by
        calc
          (2 : ZMod 1795455707) ^ 13 = (2 : ZMod 1795455707) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 6 * (2 : ZMod 1795455707) ^ 6) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1795455707) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 1795455707) ^ 27 = (2 : ZMod 1795455707) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 13 * (2 : ZMod 1795455707) ^ 13) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1795455707) ^ 55 = 1392446762 := by
        calc
          (2 : ZMod 1795455707) ^ 55 = (2 : ZMod 1795455707) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 27 * (2 : ZMod 1795455707) ^ 27) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1392446762 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1795455707) ^ 110 = 1086164411 := by
        calc
          (2 : ZMod 1795455707) ^ 110 = (2 : ZMod 1795455707) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 55 * (2 : ZMod 1795455707) ^ 55 := by rw [pow_add]
          _ = 1086164411 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1795455707) ^ 220 = 543319859 := by
        calc
          (2 : ZMod 1795455707) ^ 220 = (2 : ZMod 1795455707) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 110 * (2 : ZMod 1795455707) ^ 110 := by rw [pow_add]
          _ = 543319859 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1795455707) ^ 441 = 1716398031 := by
        calc
          (2 : ZMod 1795455707) ^ 441 = (2 : ZMod 1795455707) ^ (220 + 220 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 220 * (2 : ZMod 1795455707) ^ 220) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1716398031 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1795455707) ^ 883 = 318551902 := by
        calc
          (2 : ZMod 1795455707) ^ 883 = (2 : ZMod 1795455707) ^ (441 + 441 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 441 * (2 : ZMod 1795455707) ^ 441) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 318551902 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1795455707) ^ 1767 = 1762236875 := by
        calc
          (2 : ZMod 1795455707) ^ 1767 = (2 : ZMod 1795455707) ^ (883 + 883 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 883 * (2 : ZMod 1795455707) ^ 883) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1762236875 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1795455707) ^ 3535 = 262021220 := by
        calc
          (2 : ZMod 1795455707) ^ 3535 = (2 : ZMod 1795455707) ^ (1767 + 1767 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 1767 * (2 : ZMod 1795455707) ^ 1767) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 262021220 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1795455707) ^ 7070 = 1428437217 := by
        calc
          (2 : ZMod 1795455707) ^ 7070 = (2 : ZMod 1795455707) ^ (3535 + 3535) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 3535 * (2 : ZMod 1795455707) ^ 3535 := by rw [pow_add]
          _ = 1428437217 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1795455707) ^ 14140 = 1403353324 := by
        calc
          (2 : ZMod 1795455707) ^ 14140 = (2 : ZMod 1795455707) ^ (7070 + 7070) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 7070 * (2 : ZMod 1795455707) ^ 7070 := by rw [pow_add]
          _ = 1403353324 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1795455707) ^ 28280 = 859707706 := by
        calc
          (2 : ZMod 1795455707) ^ 28280 = (2 : ZMod 1795455707) ^ (14140 + 14140) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 14140 * (2 : ZMod 1795455707) ^ 14140 := by rw [pow_add]
          _ = 859707706 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1795455707) ^ 56560 = 1697801448 := by
        calc
          (2 : ZMod 1795455707) ^ 56560 = (2 : ZMod 1795455707) ^ (28280 + 28280) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 28280 * (2 : ZMod 1795455707) ^ 28280 := by rw [pow_add]
          _ = 1697801448 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1795455707) ^ 113120 = 1381426300 := by
        calc
          (2 : ZMod 1795455707) ^ 113120 = (2 : ZMod 1795455707) ^ (56560 + 56560) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 56560 * (2 : ZMod 1795455707) ^ 56560 := by rw [pow_add]
          _ = 1381426300 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1795455707) ^ 226241 = 1698181216 := by
        calc
          (2 : ZMod 1795455707) ^ 226241 = (2 : ZMod 1795455707) ^ (113120 + 113120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 113120 * (2 : ZMod 1795455707) ^ 113120) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1698181216 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1795455707) ^ 452483 = 637391820 := by
        calc
          (2 : ZMod 1795455707) ^ 452483 = (2 : ZMod 1795455707) ^ (226241 + 226241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 226241 * (2 : ZMod 1795455707) ^ 226241) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 637391820 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1795455707) ^ 904967 = 860006289 := by
        calc
          (2 : ZMod 1795455707) ^ 904967 = (2 : ZMod 1795455707) ^ (452483 + 452483 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 452483 * (2 : ZMod 1795455707) ^ 452483) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 860006289 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1795455707) ^ 1809935 = 549674034 := by
        calc
          (2 : ZMod 1795455707) ^ 1809935 = (2 : ZMod 1795455707) ^ (904967 + 904967 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 904967 * (2 : ZMod 1795455707) ^ 904967) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 549674034 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1795455707) ^ 3619870 = 392049457 := by
        calc
          (2 : ZMod 1795455707) ^ 3619870 = (2 : ZMod 1795455707) ^ (1809935 + 1809935) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 1809935 * (2 : ZMod 1795455707) ^ 1809935 := by rw [pow_add]
          _ = 392049457 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1795455707) ^ 7239740 = 798091171 := by
        calc
          (2 : ZMod 1795455707) ^ 7239740 = (2 : ZMod 1795455707) ^ (3619870 + 3619870) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 3619870 * (2 : ZMod 1795455707) ^ 3619870 := by rw [pow_add]
          _ = 798091171 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 1795455707) ^ 14479481 = 483878093 := by
        calc
          (2 : ZMod 1795455707) ^ 14479481 = (2 : ZMod 1795455707) ^ (7239740 + 7239740 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 7239740 * (2 : ZMod 1795455707) ^ 7239740) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 483878093 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 1795455707) ^ 28958963 = 962247768 := by
        calc
          (2 : ZMod 1795455707) ^ 28958963 = (2 : ZMod 1795455707) ^ (14479481 + 14479481 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 14479481 * (2 : ZMod 1795455707) ^ 14479481) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 962247768 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 1795455707) ^ 57917926 = 100144820 := by
        calc
          (2 : ZMod 1795455707) ^ 57917926 = (2 : ZMod 1795455707) ^ (28958963 + 28958963) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 28958963 * (2 : ZMod 1795455707) ^ 28958963 := by rw [pow_add]
          _ = 100144820 := by rw [factor_2_24]; decide
      change (2 : ZMod 1795455707) ^ 57917926 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1795455707) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1795455707) ^ 2 = 4 := by
        calc
          (2 : ZMod 1795455707) ^ 2 = (2 : ZMod 1795455707) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 1 * (2 : ZMod 1795455707) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1795455707) ^ 5 = 32 := by
        calc
          (2 : ZMod 1795455707) ^ 5 = (2 : ZMod 1795455707) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 2 * (2 : ZMod 1795455707) ^ 2) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1795455707) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1795455707) ^ 10 = (2 : ZMod 1795455707) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 5 * (2 : ZMod 1795455707) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1795455707) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 1795455707) ^ 21 = (2 : ZMod 1795455707) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 10 * (2 : ZMod 1795455707) ^ 10) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 1795455707) ^ 42 = 975484661 := by
        calc
          (2 : ZMod 1795455707) ^ 42 = (2 : ZMod 1795455707) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 21 * (2 : ZMod 1795455707) ^ 21 := by rw [pow_add]
          _ = 975484661 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 1795455707) ^ 85 = 1550002061 := by
        calc
          (2 : ZMod 1795455707) ^ 85 = (2 : ZMod 1795455707) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 42 * (2 : ZMod 1795455707) ^ 42) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 1550002061 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 1795455707) ^ 170 = 1153859415 := by
        calc
          (2 : ZMod 1795455707) ^ 170 = (2 : ZMod 1795455707) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 85 * (2 : ZMod 1795455707) ^ 85 := by rw [pow_add]
          _ = 1153859415 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 1795455707) ^ 341 = 789992094 := by
        calc
          (2 : ZMod 1795455707) ^ 341 = (2 : ZMod 1795455707) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = ((2 : ZMod 1795455707) ^ 170 * (2 : ZMod 1795455707) ^ 170) * (2 : ZMod 1795455707) := by rw [pow_succ, pow_add]
          _ = 789992094 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 1795455707) ^ 682 = 1587648217 := by
        calc
          (2 : ZMod 1795455707) ^ 682 = (2 : ZMod 1795455707) ^ (341 + 341) :=
            congrArg (fun n : ℕ => (2 : ZMod 1795455707) ^ n) (by norm_num)
          _ = (2 : ZMod 1795455707) ^ 341 * (2 : ZMod 1795455707) ^ 341 := by rw [pow_add]
          _ = 1587648217 := by rw [factor_3_8]; decide
      change (2 : ZMod 1795455707) ^ 682 ≠ 1
      rw [factor_3_9]
      decide

#print axioms prime_lucas_1795455707

end TotientTailPeriodKiller
end Erdos249257
