import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_6177956401 : Nat.Prime 6177956401 := by
  apply lucas_primality 6177956401 (13 : ZMod 6177956401)
  ·
      have fermat_0 : (13 : ZMod 6177956401) ^ 1 = 13 := by norm_num
      have fermat_1 : (13 : ZMod 6177956401) ^ 2 = 169 := by
        calc
          (13 : ZMod 6177956401) ^ 2 = (13 : ZMod 6177956401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1 * (13 : ZMod 6177956401) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [fermat_0]; decide
      have fermat_2 : (13 : ZMod 6177956401) ^ 5 = 371293 := by
        calc
          (13 : ZMod 6177956401) ^ 5 = (13 : ZMod 6177956401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2 * (13 : ZMod 6177956401) ^ 2) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [fermat_1]; decide
      have fermat_3 : (13 : ZMod 6177956401) ^ 11 = 553037747 := by
        calc
          (13 : ZMod 6177956401) ^ 11 = (13 : ZMod 6177956401) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 5 * (13 : ZMod 6177956401) ^ 5) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 553037747 := by rw [fermat_2]; decide
      have fermat_4 : (13 : ZMod 6177956401) ^ 23 = 3938102333 := by
        calc
          (13 : ZMod 6177956401) ^ 23 = (13 : ZMod 6177956401) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 11 * (13 : ZMod 6177956401) ^ 11) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3938102333 := by rw [fermat_3]; decide
      have fermat_5 : (13 : ZMod 6177956401) ^ 46 = 1439162489 := by
        calc
          (13 : ZMod 6177956401) ^ 46 = (13 : ZMod 6177956401) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 23 * (13 : ZMod 6177956401) ^ 23 := by rw [pow_add]
          _ = 1439162489 := by rw [fermat_4]; decide
      have fermat_6 : (13 : ZMod 6177956401) ^ 92 = 3210552862 := by
        calc
          (13 : ZMod 6177956401) ^ 92 = (13 : ZMod 6177956401) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 46 * (13 : ZMod 6177956401) ^ 46 := by rw [pow_add]
          _ = 3210552862 := by rw [fermat_5]; decide
      have fermat_7 : (13 : ZMod 6177956401) ^ 184 = 584385641 := by
        calc
          (13 : ZMod 6177956401) ^ 184 = (13 : ZMod 6177956401) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 92 * (13 : ZMod 6177956401) ^ 92 := by rw [pow_add]
          _ = 584385641 := by rw [fermat_6]; decide
      have fermat_8 : (13 : ZMod 6177956401) ^ 368 = 2229097438 := by
        calc
          (13 : ZMod 6177956401) ^ 368 = (13 : ZMod 6177956401) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 184 * (13 : ZMod 6177956401) ^ 184 := by rw [pow_add]
          _ = 2229097438 := by rw [fermat_7]; decide
      have fermat_9 : (13 : ZMod 6177956401) ^ 736 = 1518094338 := by
        calc
          (13 : ZMod 6177956401) ^ 736 = (13 : ZMod 6177956401) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 368 * (13 : ZMod 6177956401) ^ 368 := by rw [pow_add]
          _ = 1518094338 := by rw [fermat_8]; decide
      have fermat_10 : (13 : ZMod 6177956401) ^ 1472 = 1122727381 := by
        calc
          (13 : ZMod 6177956401) ^ 1472 = (13 : ZMod 6177956401) ^ (736 + 736) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 736 * (13 : ZMod 6177956401) ^ 736 := by rw [pow_add]
          _ = 1122727381 := by rw [fermat_9]; decide
      have fermat_11 : (13 : ZMod 6177956401) ^ 2945 = 2539008285 := by
        calc
          (13 : ZMod 6177956401) ^ 2945 = (13 : ZMod 6177956401) ^ (1472 + 1472 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 1472 * (13 : ZMod 6177956401) ^ 1472) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2539008285 := by rw [fermat_10]; decide
      have fermat_12 : (13 : ZMod 6177956401) ^ 5891 = 1779463607 := by
        calc
          (13 : ZMod 6177956401) ^ 5891 = (13 : ZMod 6177956401) ^ (2945 + 2945 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2945 * (13 : ZMod 6177956401) ^ 2945) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1779463607 := by rw [fermat_11]; decide
      have fermat_13 : (13 : ZMod 6177956401) ^ 11783 = 3191154058 := by
        calc
          (13 : ZMod 6177956401) ^ 11783 = (13 : ZMod 6177956401) ^ (5891 + 5891 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 5891 * (13 : ZMod 6177956401) ^ 5891) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3191154058 := by rw [fermat_12]; decide
      have fermat_14 : (13 : ZMod 6177956401) ^ 23567 = 1256598250 := by
        calc
          (13 : ZMod 6177956401) ^ 23567 = (13 : ZMod 6177956401) ^ (11783 + 11783 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 11783 * (13 : ZMod 6177956401) ^ 11783) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1256598250 := by rw [fermat_13]; decide
      have fermat_15 : (13 : ZMod 6177956401) ^ 47134 = 1107336426 := by
        calc
          (13 : ZMod 6177956401) ^ 47134 = (13 : ZMod 6177956401) ^ (23567 + 23567) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 23567 * (13 : ZMod 6177956401) ^ 23567 := by rw [pow_add]
          _ = 1107336426 := by rw [fermat_14]; decide
      have fermat_16 : (13 : ZMod 6177956401) ^ 94268 = 517796581 := by
        calc
          (13 : ZMod 6177956401) ^ 94268 = (13 : ZMod 6177956401) ^ (47134 + 47134) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 47134 * (13 : ZMod 6177956401) ^ 47134 := by rw [pow_add]
          _ = 517796581 := by rw [fermat_15]; decide
      have fermat_17 : (13 : ZMod 6177956401) ^ 188536 = 5959215582 := by
        calc
          (13 : ZMod 6177956401) ^ 188536 = (13 : ZMod 6177956401) ^ (94268 + 94268) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 94268 * (13 : ZMod 6177956401) ^ 94268 := by rw [pow_add]
          _ = 5959215582 := by rw [fermat_16]; decide
      have fermat_18 : (13 : ZMod 6177956401) ^ 377072 = 2569901079 := by
        calc
          (13 : ZMod 6177956401) ^ 377072 = (13 : ZMod 6177956401) ^ (188536 + 188536) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 188536 * (13 : ZMod 6177956401) ^ 188536 := by rw [pow_add]
          _ = 2569901079 := by rw [fermat_17]; decide
      have fermat_19 : (13 : ZMod 6177956401) ^ 754145 = 1573671726 := by
        calc
          (13 : ZMod 6177956401) ^ 754145 = (13 : ZMod 6177956401) ^ (377072 + 377072 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 377072 * (13 : ZMod 6177956401) ^ 377072) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1573671726 := by rw [fermat_18]; decide
      have fermat_20 : (13 : ZMod 6177956401) ^ 1508290 = 147620839 := by
        calc
          (13 : ZMod 6177956401) ^ 1508290 = (13 : ZMod 6177956401) ^ (754145 + 754145) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 754145 * (13 : ZMod 6177956401) ^ 754145 := by rw [pow_add]
          _ = 147620839 := by rw [fermat_19]; decide
      have fermat_21 : (13 : ZMod 6177956401) ^ 3016580 = 4926650556 := by
        calc
          (13 : ZMod 6177956401) ^ 3016580 = (13 : ZMod 6177956401) ^ (1508290 + 1508290) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1508290 * (13 : ZMod 6177956401) ^ 1508290 := by rw [pow_add]
          _ = 4926650556 := by rw [fermat_20]; decide
      have fermat_22 : (13 : ZMod 6177956401) ^ 6033160 = 2026474371 := by
        calc
          (13 : ZMod 6177956401) ^ 6033160 = (13 : ZMod 6177956401) ^ (3016580 + 3016580) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 3016580 * (13 : ZMod 6177956401) ^ 3016580 := by rw [pow_add]
          _ = 2026474371 := by rw [fermat_21]; decide
      have fermat_23 : (13 : ZMod 6177956401) ^ 12066321 = 958076273 := by
        calc
          (13 : ZMod 6177956401) ^ 12066321 = (13 : ZMod 6177956401) ^ (6033160 + 6033160 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 6033160 * (13 : ZMod 6177956401) ^ 6033160) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 958076273 := by rw [fermat_22]; decide
      have fermat_24 : (13 : ZMod 6177956401) ^ 24132642 = 2732043848 := by
        calc
          (13 : ZMod 6177956401) ^ 24132642 = (13 : ZMod 6177956401) ^ (12066321 + 12066321) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 12066321 * (13 : ZMod 6177956401) ^ 12066321 := by rw [pow_add]
          _ = 2732043848 := by rw [fermat_23]; decide
      have fermat_25 : (13 : ZMod 6177956401) ^ 48265284 = 4650863106 := by
        calc
          (13 : ZMod 6177956401) ^ 48265284 = (13 : ZMod 6177956401) ^ (24132642 + 24132642) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 24132642 * (13 : ZMod 6177956401) ^ 24132642 := by rw [pow_add]
          _ = 4650863106 := by rw [fermat_24]; decide
      have fermat_26 : (13 : ZMod 6177956401) ^ 96530568 = 1904761670 := by
        calc
          (13 : ZMod 6177956401) ^ 96530568 = (13 : ZMod 6177956401) ^ (48265284 + 48265284) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 48265284 * (13 : ZMod 6177956401) ^ 48265284 := by rw [pow_add]
          _ = 1904761670 := by rw [fermat_25]; decide
      have fermat_27 : (13 : ZMod 6177956401) ^ 193061137 = 3037735765 := by
        calc
          (13 : ZMod 6177956401) ^ 193061137 = (13 : ZMod 6177956401) ^ (96530568 + 96530568 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 96530568 * (13 : ZMod 6177956401) ^ 96530568) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3037735765 := by rw [fermat_26]; decide
      have fermat_28 : (13 : ZMod 6177956401) ^ 386122275 = 2695874356 := by
        calc
          (13 : ZMod 6177956401) ^ 386122275 = (13 : ZMod 6177956401) ^ (193061137 + 193061137 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 193061137 * (13 : ZMod 6177956401) ^ 193061137) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2695874356 := by rw [fermat_27]; decide
      have fermat_29 : (13 : ZMod 6177956401) ^ 772244550 = 5161875053 := by
        calc
          (13 : ZMod 6177956401) ^ 772244550 = (13 : ZMod 6177956401) ^ (386122275 + 386122275) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 386122275 * (13 : ZMod 6177956401) ^ 386122275 := by rw [pow_add]
          _ = 5161875053 := by rw [fermat_28]; decide
      have fermat_30 : (13 : ZMod 6177956401) ^ 1544489100 = 4872749780 := by
        calc
          (13 : ZMod 6177956401) ^ 1544489100 = (13 : ZMod 6177956401) ^ (772244550 + 772244550) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 772244550 * (13 : ZMod 6177956401) ^ 772244550 := by rw [pow_add]
          _ = 4872749780 := by rw [fermat_29]; decide
      have fermat_31 : (13 : ZMod 6177956401) ^ 3088978200 = 6177956400 := by
        calc
          (13 : ZMod 6177956401) ^ 3088978200 = (13 : ZMod 6177956401) ^ (1544489100 + 1544489100) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1544489100 * (13 : ZMod 6177956401) ^ 1544489100 := by rw [pow_add]
          _ = 6177956400 := by rw [fermat_30]; decide
      have fermat_32 : (13 : ZMod 6177956401) ^ 6177956400 = 1 := by
        calc
          (13 : ZMod 6177956401) ^ 6177956400 = (13 : ZMod 6177956401) ^ (3088978200 + 3088978200) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 3088978200 * (13 : ZMod 6177956401) ^ 3088978200 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 6177956401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (13 : ZMod 6177956401) ^ 1 = 13 := by norm_num
      have factor_0_1 : (13 : ZMod 6177956401) ^ 2 = 169 := by
        calc
          (13 : ZMod 6177956401) ^ 2 = (13 : ZMod 6177956401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1 * (13 : ZMod 6177956401) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_0_0]; decide
      have factor_0_2 : (13 : ZMod 6177956401) ^ 5 = 371293 := by
        calc
          (13 : ZMod 6177956401) ^ 5 = (13 : ZMod 6177956401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2 * (13 : ZMod 6177956401) ^ 2) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_0_1]; decide
      have factor_0_3 : (13 : ZMod 6177956401) ^ 11 = 553037747 := by
        calc
          (13 : ZMod 6177956401) ^ 11 = (13 : ZMod 6177956401) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 5 * (13 : ZMod 6177956401) ^ 5) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 553037747 := by rw [factor_0_2]; decide
      have factor_0_4 : (13 : ZMod 6177956401) ^ 23 = 3938102333 := by
        calc
          (13 : ZMod 6177956401) ^ 23 = (13 : ZMod 6177956401) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 11 * (13 : ZMod 6177956401) ^ 11) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3938102333 := by rw [factor_0_3]; decide
      have factor_0_5 : (13 : ZMod 6177956401) ^ 46 = 1439162489 := by
        calc
          (13 : ZMod 6177956401) ^ 46 = (13 : ZMod 6177956401) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 23 * (13 : ZMod 6177956401) ^ 23 := by rw [pow_add]
          _ = 1439162489 := by rw [factor_0_4]; decide
      have factor_0_6 : (13 : ZMod 6177956401) ^ 92 = 3210552862 := by
        calc
          (13 : ZMod 6177956401) ^ 92 = (13 : ZMod 6177956401) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 46 * (13 : ZMod 6177956401) ^ 46 := by rw [pow_add]
          _ = 3210552862 := by rw [factor_0_5]; decide
      have factor_0_7 : (13 : ZMod 6177956401) ^ 184 = 584385641 := by
        calc
          (13 : ZMod 6177956401) ^ 184 = (13 : ZMod 6177956401) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 92 * (13 : ZMod 6177956401) ^ 92 := by rw [pow_add]
          _ = 584385641 := by rw [factor_0_6]; decide
      have factor_0_8 : (13 : ZMod 6177956401) ^ 368 = 2229097438 := by
        calc
          (13 : ZMod 6177956401) ^ 368 = (13 : ZMod 6177956401) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 184 * (13 : ZMod 6177956401) ^ 184 := by rw [pow_add]
          _ = 2229097438 := by rw [factor_0_7]; decide
      have factor_0_9 : (13 : ZMod 6177956401) ^ 736 = 1518094338 := by
        calc
          (13 : ZMod 6177956401) ^ 736 = (13 : ZMod 6177956401) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 368 * (13 : ZMod 6177956401) ^ 368 := by rw [pow_add]
          _ = 1518094338 := by rw [factor_0_8]; decide
      have factor_0_10 : (13 : ZMod 6177956401) ^ 1472 = 1122727381 := by
        calc
          (13 : ZMod 6177956401) ^ 1472 = (13 : ZMod 6177956401) ^ (736 + 736) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 736 * (13 : ZMod 6177956401) ^ 736 := by rw [pow_add]
          _ = 1122727381 := by rw [factor_0_9]; decide
      have factor_0_11 : (13 : ZMod 6177956401) ^ 2945 = 2539008285 := by
        calc
          (13 : ZMod 6177956401) ^ 2945 = (13 : ZMod 6177956401) ^ (1472 + 1472 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 1472 * (13 : ZMod 6177956401) ^ 1472) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2539008285 := by rw [factor_0_10]; decide
      have factor_0_12 : (13 : ZMod 6177956401) ^ 5891 = 1779463607 := by
        calc
          (13 : ZMod 6177956401) ^ 5891 = (13 : ZMod 6177956401) ^ (2945 + 2945 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2945 * (13 : ZMod 6177956401) ^ 2945) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1779463607 := by rw [factor_0_11]; decide
      have factor_0_13 : (13 : ZMod 6177956401) ^ 11783 = 3191154058 := by
        calc
          (13 : ZMod 6177956401) ^ 11783 = (13 : ZMod 6177956401) ^ (5891 + 5891 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 5891 * (13 : ZMod 6177956401) ^ 5891) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3191154058 := by rw [factor_0_12]; decide
      have factor_0_14 : (13 : ZMod 6177956401) ^ 23567 = 1256598250 := by
        calc
          (13 : ZMod 6177956401) ^ 23567 = (13 : ZMod 6177956401) ^ (11783 + 11783 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 11783 * (13 : ZMod 6177956401) ^ 11783) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1256598250 := by rw [factor_0_13]; decide
      have factor_0_15 : (13 : ZMod 6177956401) ^ 47134 = 1107336426 := by
        calc
          (13 : ZMod 6177956401) ^ 47134 = (13 : ZMod 6177956401) ^ (23567 + 23567) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 23567 * (13 : ZMod 6177956401) ^ 23567 := by rw [pow_add]
          _ = 1107336426 := by rw [factor_0_14]; decide
      have factor_0_16 : (13 : ZMod 6177956401) ^ 94268 = 517796581 := by
        calc
          (13 : ZMod 6177956401) ^ 94268 = (13 : ZMod 6177956401) ^ (47134 + 47134) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 47134 * (13 : ZMod 6177956401) ^ 47134 := by rw [pow_add]
          _ = 517796581 := by rw [factor_0_15]; decide
      have factor_0_17 : (13 : ZMod 6177956401) ^ 188536 = 5959215582 := by
        calc
          (13 : ZMod 6177956401) ^ 188536 = (13 : ZMod 6177956401) ^ (94268 + 94268) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 94268 * (13 : ZMod 6177956401) ^ 94268 := by rw [pow_add]
          _ = 5959215582 := by rw [factor_0_16]; decide
      have factor_0_18 : (13 : ZMod 6177956401) ^ 377072 = 2569901079 := by
        calc
          (13 : ZMod 6177956401) ^ 377072 = (13 : ZMod 6177956401) ^ (188536 + 188536) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 188536 * (13 : ZMod 6177956401) ^ 188536 := by rw [pow_add]
          _ = 2569901079 := by rw [factor_0_17]; decide
      have factor_0_19 : (13 : ZMod 6177956401) ^ 754145 = 1573671726 := by
        calc
          (13 : ZMod 6177956401) ^ 754145 = (13 : ZMod 6177956401) ^ (377072 + 377072 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 377072 * (13 : ZMod 6177956401) ^ 377072) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1573671726 := by rw [factor_0_18]; decide
      have factor_0_20 : (13 : ZMod 6177956401) ^ 1508290 = 147620839 := by
        calc
          (13 : ZMod 6177956401) ^ 1508290 = (13 : ZMod 6177956401) ^ (754145 + 754145) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 754145 * (13 : ZMod 6177956401) ^ 754145 := by rw [pow_add]
          _ = 147620839 := by rw [factor_0_19]; decide
      have factor_0_21 : (13 : ZMod 6177956401) ^ 3016580 = 4926650556 := by
        calc
          (13 : ZMod 6177956401) ^ 3016580 = (13 : ZMod 6177956401) ^ (1508290 + 1508290) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1508290 * (13 : ZMod 6177956401) ^ 1508290 := by rw [pow_add]
          _ = 4926650556 := by rw [factor_0_20]; decide
      have factor_0_22 : (13 : ZMod 6177956401) ^ 6033160 = 2026474371 := by
        calc
          (13 : ZMod 6177956401) ^ 6033160 = (13 : ZMod 6177956401) ^ (3016580 + 3016580) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 3016580 * (13 : ZMod 6177956401) ^ 3016580 := by rw [pow_add]
          _ = 2026474371 := by rw [factor_0_21]; decide
      have factor_0_23 : (13 : ZMod 6177956401) ^ 12066321 = 958076273 := by
        calc
          (13 : ZMod 6177956401) ^ 12066321 = (13 : ZMod 6177956401) ^ (6033160 + 6033160 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 6033160 * (13 : ZMod 6177956401) ^ 6033160) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 958076273 := by rw [factor_0_22]; decide
      have factor_0_24 : (13 : ZMod 6177956401) ^ 24132642 = 2732043848 := by
        calc
          (13 : ZMod 6177956401) ^ 24132642 = (13 : ZMod 6177956401) ^ (12066321 + 12066321) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 12066321 * (13 : ZMod 6177956401) ^ 12066321 := by rw [pow_add]
          _ = 2732043848 := by rw [factor_0_23]; decide
      have factor_0_25 : (13 : ZMod 6177956401) ^ 48265284 = 4650863106 := by
        calc
          (13 : ZMod 6177956401) ^ 48265284 = (13 : ZMod 6177956401) ^ (24132642 + 24132642) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 24132642 * (13 : ZMod 6177956401) ^ 24132642 := by rw [pow_add]
          _ = 4650863106 := by rw [factor_0_24]; decide
      have factor_0_26 : (13 : ZMod 6177956401) ^ 96530568 = 1904761670 := by
        calc
          (13 : ZMod 6177956401) ^ 96530568 = (13 : ZMod 6177956401) ^ (48265284 + 48265284) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 48265284 * (13 : ZMod 6177956401) ^ 48265284 := by rw [pow_add]
          _ = 1904761670 := by rw [factor_0_25]; decide
      have factor_0_27 : (13 : ZMod 6177956401) ^ 193061137 = 3037735765 := by
        calc
          (13 : ZMod 6177956401) ^ 193061137 = (13 : ZMod 6177956401) ^ (96530568 + 96530568 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 96530568 * (13 : ZMod 6177956401) ^ 96530568) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3037735765 := by rw [factor_0_26]; decide
      have factor_0_28 : (13 : ZMod 6177956401) ^ 386122275 = 2695874356 := by
        calc
          (13 : ZMod 6177956401) ^ 386122275 = (13 : ZMod 6177956401) ^ (193061137 + 193061137 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 193061137 * (13 : ZMod 6177956401) ^ 193061137) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2695874356 := by rw [factor_0_27]; decide
      have factor_0_29 : (13 : ZMod 6177956401) ^ 772244550 = 5161875053 := by
        calc
          (13 : ZMod 6177956401) ^ 772244550 = (13 : ZMod 6177956401) ^ (386122275 + 386122275) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 386122275 * (13 : ZMod 6177956401) ^ 386122275 := by rw [pow_add]
          _ = 5161875053 := by rw [factor_0_28]; decide
      have factor_0_30 : (13 : ZMod 6177956401) ^ 1544489100 = 4872749780 := by
        calc
          (13 : ZMod 6177956401) ^ 1544489100 = (13 : ZMod 6177956401) ^ (772244550 + 772244550) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 772244550 * (13 : ZMod 6177956401) ^ 772244550 := by rw [pow_add]
          _ = 4872749780 := by rw [factor_0_29]; decide
      have factor_0_31 : (13 : ZMod 6177956401) ^ 3088978200 = 6177956400 := by
        calc
          (13 : ZMod 6177956401) ^ 3088978200 = (13 : ZMod 6177956401) ^ (1544489100 + 1544489100) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1544489100 * (13 : ZMod 6177956401) ^ 1544489100 := by rw [pow_add]
          _ = 6177956400 := by rw [factor_0_30]; decide
      change (13 : ZMod 6177956401) ^ 3088978200 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (13 : ZMod 6177956401) ^ 1 = 13 := by norm_num
      have factor_1_1 : (13 : ZMod 6177956401) ^ 3 = 2197 := by
        calc
          (13 : ZMod 6177956401) ^ 3 = (13 : ZMod 6177956401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 1 * (13 : ZMod 6177956401) ^ 1) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_1_0]; decide
      have factor_1_2 : (13 : ZMod 6177956401) ^ 7 = 62748517 := by
        calc
          (13 : ZMod 6177956401) ^ 7 = (13 : ZMod 6177956401) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 3 * (13 : ZMod 6177956401) ^ 3) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 62748517 := by rw [factor_1_1]; decide
      have factor_1_3 : (13 : ZMod 6177956401) ^ 15 = 4454531111 := by
        calc
          (13 : ZMod 6177956401) ^ 15 = (13 : ZMod 6177956401) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 7 * (13 : ZMod 6177956401) ^ 7) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4454531111 := by rw [factor_1_2]; decide
      have factor_1_4 : (13 : ZMod 6177956401) ^ 30 = 4764265085 := by
        calc
          (13 : ZMod 6177956401) ^ 30 = (13 : ZMod 6177956401) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 15 * (13 : ZMod 6177956401) ^ 15 := by rw [pow_add]
          _ = 4764265085 := by rw [factor_1_3]; decide
      have factor_1_5 : (13 : ZMod 6177956401) ^ 61 = 4977950017 := by
        calc
          (13 : ZMod 6177956401) ^ 61 = (13 : ZMod 6177956401) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 30 * (13 : ZMod 6177956401) ^ 30) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4977950017 := by rw [factor_1_4]; decide
      have factor_1_6 : (13 : ZMod 6177956401) ^ 122 = 4929620191 := by
        calc
          (13 : ZMod 6177956401) ^ 122 = (13 : ZMod 6177956401) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 61 * (13 : ZMod 6177956401) ^ 61 := by rw [pow_add]
          _ = 4929620191 := by rw [factor_1_5]; decide
      have factor_1_7 : (13 : ZMod 6177956401) ^ 245 = 3352490936 := by
        calc
          (13 : ZMod 6177956401) ^ 245 = (13 : ZMod 6177956401) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 122 * (13 : ZMod 6177956401) ^ 122) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3352490936 := by rw [factor_1_6]; decide
      have factor_1_8 : (13 : ZMod 6177956401) ^ 490 = 2937982466 := by
        calc
          (13 : ZMod 6177956401) ^ 490 = (13 : ZMod 6177956401) ^ (245 + 245) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 245 * (13 : ZMod 6177956401) ^ 245 := by rw [pow_add]
          _ = 2937982466 := by rw [factor_1_7]; decide
      have factor_1_9 : (13 : ZMod 6177956401) ^ 981 = 2769105650 := by
        calc
          (13 : ZMod 6177956401) ^ 981 = (13 : ZMod 6177956401) ^ (490 + 490 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 490 * (13 : ZMod 6177956401) ^ 490) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2769105650 := by rw [factor_1_8]; decide
      have factor_1_10 : (13 : ZMod 6177956401) ^ 1963 = 5142243175 := by
        calc
          (13 : ZMod 6177956401) ^ 1963 = (13 : ZMod 6177956401) ^ (981 + 981 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 981 * (13 : ZMod 6177956401) ^ 981) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5142243175 := by rw [factor_1_9]; decide
      have factor_1_11 : (13 : ZMod 6177956401) ^ 3927 = 621203324 := by
        calc
          (13 : ZMod 6177956401) ^ 3927 = (13 : ZMod 6177956401) ^ (1963 + 1963 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 1963 * (13 : ZMod 6177956401) ^ 1963) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 621203324 := by rw [factor_1_10]; decide
      have factor_1_12 : (13 : ZMod 6177956401) ^ 7855 = 3327699943 := by
        calc
          (13 : ZMod 6177956401) ^ 7855 = (13 : ZMod 6177956401) ^ (3927 + 3927 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 3927 * (13 : ZMod 6177956401) ^ 3927) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3327699943 := by rw [factor_1_11]; decide
      have factor_1_13 : (13 : ZMod 6177956401) ^ 15711 = 5348401010 := by
        calc
          (13 : ZMod 6177956401) ^ 15711 = (13 : ZMod 6177956401) ^ (7855 + 7855 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 7855 * (13 : ZMod 6177956401) ^ 7855) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5348401010 := by rw [factor_1_12]; decide
      have factor_1_14 : (13 : ZMod 6177956401) ^ 31422 = 3330808149 := by
        calc
          (13 : ZMod 6177956401) ^ 31422 = (13 : ZMod 6177956401) ^ (15711 + 15711) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 15711 * (13 : ZMod 6177956401) ^ 15711 := by rw [pow_add]
          _ = 3330808149 := by rw [factor_1_13]; decide
      have factor_1_15 : (13 : ZMod 6177956401) ^ 62845 = 481958478 := by
        calc
          (13 : ZMod 6177956401) ^ 62845 = (13 : ZMod 6177956401) ^ (31422 + 31422 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 31422 * (13 : ZMod 6177956401) ^ 31422) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 481958478 := by rw [factor_1_14]; decide
      have factor_1_16 : (13 : ZMod 6177956401) ^ 125690 = 4979727248 := by
        calc
          (13 : ZMod 6177956401) ^ 125690 = (13 : ZMod 6177956401) ^ (62845 + 62845) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 62845 * (13 : ZMod 6177956401) ^ 62845 := by rw [pow_add]
          _ = 4979727248 := by rw [factor_1_15]; decide
      have factor_1_17 : (13 : ZMod 6177956401) ^ 251381 = 4277319860 := by
        calc
          (13 : ZMod 6177956401) ^ 251381 = (13 : ZMod 6177956401) ^ (125690 + 125690 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 125690 * (13 : ZMod 6177956401) ^ 125690) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4277319860 := by rw [factor_1_16]; decide
      have factor_1_18 : (13 : ZMod 6177956401) ^ 502763 = 3597620216 := by
        calc
          (13 : ZMod 6177956401) ^ 502763 = (13 : ZMod 6177956401) ^ (251381 + 251381 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 251381 * (13 : ZMod 6177956401) ^ 251381) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3597620216 := by rw [factor_1_17]; decide
      have factor_1_19 : (13 : ZMod 6177956401) ^ 1005526 = 2601783349 := by
        calc
          (13 : ZMod 6177956401) ^ 1005526 = (13 : ZMod 6177956401) ^ (502763 + 502763) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 502763 * (13 : ZMod 6177956401) ^ 502763 := by rw [pow_add]
          _ = 2601783349 := by rw [factor_1_18]; decide
      have factor_1_20 : (13 : ZMod 6177956401) ^ 2011053 = 4890884122 := by
        calc
          (13 : ZMod 6177956401) ^ 2011053 = (13 : ZMod 6177956401) ^ (1005526 + 1005526 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 1005526 * (13 : ZMod 6177956401) ^ 1005526) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4890884122 := by rw [factor_1_19]; decide
      have factor_1_21 : (13 : ZMod 6177956401) ^ 4022107 = 5831622117 := by
        calc
          (13 : ZMod 6177956401) ^ 4022107 = (13 : ZMod 6177956401) ^ (2011053 + 2011053 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2011053 * (13 : ZMod 6177956401) ^ 2011053) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5831622117 := by rw [factor_1_20]; decide
      have factor_1_22 : (13 : ZMod 6177956401) ^ 8044214 = 3345381266 := by
        calc
          (13 : ZMod 6177956401) ^ 8044214 = (13 : ZMod 6177956401) ^ (4022107 + 4022107) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 4022107 * (13 : ZMod 6177956401) ^ 4022107 := by rw [pow_add]
          _ = 3345381266 := by rw [factor_1_21]; decide
      have factor_1_23 : (13 : ZMod 6177956401) ^ 16088428 = 5106671522 := by
        calc
          (13 : ZMod 6177956401) ^ 16088428 = (13 : ZMod 6177956401) ^ (8044214 + 8044214) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 8044214 * (13 : ZMod 6177956401) ^ 8044214 := by rw [pow_add]
          _ = 5106671522 := by rw [factor_1_22]; decide
      have factor_1_24 : (13 : ZMod 6177956401) ^ 32176856 = 2426994720 := by
        calc
          (13 : ZMod 6177956401) ^ 32176856 = (13 : ZMod 6177956401) ^ (16088428 + 16088428) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 16088428 * (13 : ZMod 6177956401) ^ 16088428 := by rw [pow_add]
          _ = 2426994720 := by rw [factor_1_23]; decide
      have factor_1_25 : (13 : ZMod 6177956401) ^ 64353712 = 2596337595 := by
        calc
          (13 : ZMod 6177956401) ^ 64353712 = (13 : ZMod 6177956401) ^ (32176856 + 32176856) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 32176856 * (13 : ZMod 6177956401) ^ 32176856 := by rw [pow_add]
          _ = 2596337595 := by rw [factor_1_24]; decide
      have factor_1_26 : (13 : ZMod 6177956401) ^ 128707425 = 6135547248 := by
        calc
          (13 : ZMod 6177956401) ^ 128707425 = (13 : ZMod 6177956401) ^ (64353712 + 64353712 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 64353712 * (13 : ZMod 6177956401) ^ 64353712) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 6135547248 := by rw [factor_1_25]; decide
      have factor_1_27 : (13 : ZMod 6177956401) ^ 257414850 = 3412761888 := by
        calc
          (13 : ZMod 6177956401) ^ 257414850 = (13 : ZMod 6177956401) ^ (128707425 + 128707425) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 128707425 * (13 : ZMod 6177956401) ^ 128707425 := by rw [pow_add]
          _ = 3412761888 := by rw [factor_1_26]; decide
      have factor_1_28 : (13 : ZMod 6177956401) ^ 514829700 = 1183081211 := by
        calc
          (13 : ZMod 6177956401) ^ 514829700 = (13 : ZMod 6177956401) ^ (257414850 + 257414850) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 257414850 * (13 : ZMod 6177956401) ^ 257414850 := by rw [pow_add]
          _ = 1183081211 := by rw [factor_1_27]; decide
      have factor_1_29 : (13 : ZMod 6177956401) ^ 1029659400 = 1158297179 := by
        calc
          (13 : ZMod 6177956401) ^ 1029659400 = (13 : ZMod 6177956401) ^ (514829700 + 514829700) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 514829700 * (13 : ZMod 6177956401) ^ 514829700 := by rw [pow_add]
          _ = 1158297179 := by rw [factor_1_28]; decide
      have factor_1_30 : (13 : ZMod 6177956401) ^ 2059318800 = 1158297178 := by
        calc
          (13 : ZMod 6177956401) ^ 2059318800 = (13 : ZMod 6177956401) ^ (1029659400 + 1029659400) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1029659400 * (13 : ZMod 6177956401) ^ 1029659400 := by rw [pow_add]
          _ = 1158297178 := by rw [factor_1_29]; decide
      change (13 : ZMod 6177956401) ^ 2059318800 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (13 : ZMod 6177956401) ^ 1 = 13 := by norm_num
      have factor_2_1 : (13 : ZMod 6177956401) ^ 2 = 169 := by
        calc
          (13 : ZMod 6177956401) ^ 2 = (13 : ZMod 6177956401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1 * (13 : ZMod 6177956401) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_2_0]; decide
      have factor_2_2 : (13 : ZMod 6177956401) ^ 4 = 28561 := by
        calc
          (13 : ZMod 6177956401) ^ 4 = (13 : ZMod 6177956401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 2 * (13 : ZMod 6177956401) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_2_1]; decide
      have factor_2_3 : (13 : ZMod 6177956401) ^ 9 = 4426542972 := by
        calc
          (13 : ZMod 6177956401) ^ 9 = (13 : ZMod 6177956401) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 4 * (13 : ZMod 6177956401) ^ 4) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4426542972 := by rw [factor_2_2]; decide
      have factor_2_4 : (13 : ZMod 6177956401) ^ 18 = 721911683 := by
        calc
          (13 : ZMod 6177956401) ^ 18 = (13 : ZMod 6177956401) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 9 * (13 : ZMod 6177956401) ^ 9 := by rw [pow_add]
          _ = 721911683 := by rw [factor_2_3]; decide
      have factor_2_5 : (13 : ZMod 6177956401) ^ 36 = 2835134267 := by
        calc
          (13 : ZMod 6177956401) ^ 36 = (13 : ZMod 6177956401) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 18 * (13 : ZMod 6177956401) ^ 18 := by rw [pow_add]
          _ = 2835134267 := by rw [factor_2_4]; decide
      have factor_2_6 : (13 : ZMod 6177956401) ^ 73 = 5579956207 := by
        calc
          (13 : ZMod 6177956401) ^ 73 = (13 : ZMod 6177956401) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 36 * (13 : ZMod 6177956401) ^ 36) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5579956207 := by rw [factor_2_5]; decide
      have factor_2_7 : (13 : ZMod 6177956401) ^ 147 = 1546480523 := by
        calc
          (13 : ZMod 6177956401) ^ 147 = (13 : ZMod 6177956401) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 73 * (13 : ZMod 6177956401) ^ 73) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1546480523 := by rw [factor_2_6]; decide
      have factor_2_8 : (13 : ZMod 6177956401) ^ 294 = 2219415701 := by
        calc
          (13 : ZMod 6177956401) ^ 294 = (13 : ZMod 6177956401) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 147 * (13 : ZMod 6177956401) ^ 147 := by rw [pow_add]
          _ = 2219415701 := by rw [factor_2_7]; decide
      have factor_2_9 : (13 : ZMod 6177956401) ^ 589 = 5539299525 := by
        calc
          (13 : ZMod 6177956401) ^ 589 = (13 : ZMod 6177956401) ^ (294 + 294 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 294 * (13 : ZMod 6177956401) ^ 294) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5539299525 := by rw [factor_2_8]; decide
      have factor_2_10 : (13 : ZMod 6177956401) ^ 1178 = 4732287923 := by
        calc
          (13 : ZMod 6177956401) ^ 1178 = (13 : ZMod 6177956401) ^ (589 + 589) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 589 * (13 : ZMod 6177956401) ^ 589 := by rw [pow_add]
          _ = 4732287923 := by rw [factor_2_9]; decide
      have factor_2_11 : (13 : ZMod 6177956401) ^ 2356 = 778825017 := by
        calc
          (13 : ZMod 6177956401) ^ 2356 = (13 : ZMod 6177956401) ^ (1178 + 1178) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1178 * (13 : ZMod 6177956401) ^ 1178 := by rw [pow_add]
          _ = 778825017 := by rw [factor_2_10]; decide
      have factor_2_12 : (13 : ZMod 6177956401) ^ 4713 = 5700586727 := by
        calc
          (13 : ZMod 6177956401) ^ 4713 = (13 : ZMod 6177956401) ^ (2356 + 2356 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2356 * (13 : ZMod 6177956401) ^ 2356) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5700586727 := by rw [factor_2_11]; decide
      have factor_2_13 : (13 : ZMod 6177956401) ^ 9426 = 731613600 := by
        calc
          (13 : ZMod 6177956401) ^ 9426 = (13 : ZMod 6177956401) ^ (4713 + 4713) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 4713 * (13 : ZMod 6177956401) ^ 4713 := by rw [pow_add]
          _ = 731613600 := by rw [factor_2_12]; decide
      have factor_2_14 : (13 : ZMod 6177956401) ^ 18853 = 1893240533 := by
        calc
          (13 : ZMod 6177956401) ^ 18853 = (13 : ZMod 6177956401) ^ (9426 + 9426 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 9426 * (13 : ZMod 6177956401) ^ 9426) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1893240533 := by rw [factor_2_13]; decide
      have factor_2_15 : (13 : ZMod 6177956401) ^ 37707 = 3368128178 := by
        calc
          (13 : ZMod 6177956401) ^ 37707 = (13 : ZMod 6177956401) ^ (18853 + 18853 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 18853 * (13 : ZMod 6177956401) ^ 18853) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3368128178 := by rw [factor_2_14]; decide
      have factor_2_16 : (13 : ZMod 6177956401) ^ 75414 = 557077259 := by
        calc
          (13 : ZMod 6177956401) ^ 75414 = (13 : ZMod 6177956401) ^ (37707 + 37707) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 37707 * (13 : ZMod 6177956401) ^ 37707 := by rw [pow_add]
          _ = 557077259 := by rw [factor_2_15]; decide
      have factor_2_17 : (13 : ZMod 6177956401) ^ 150829 = 4054851307 := by
        calc
          (13 : ZMod 6177956401) ^ 150829 = (13 : ZMod 6177956401) ^ (75414 + 75414 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 75414 * (13 : ZMod 6177956401) ^ 75414) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4054851307 := by rw [factor_2_16]; decide
      have factor_2_18 : (13 : ZMod 6177956401) ^ 301658 = 5868763659 := by
        calc
          (13 : ZMod 6177956401) ^ 301658 = (13 : ZMod 6177956401) ^ (150829 + 150829) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 150829 * (13 : ZMod 6177956401) ^ 150829 := by rw [pow_add]
          _ = 5868763659 := by rw [factor_2_17]; decide
      have factor_2_19 : (13 : ZMod 6177956401) ^ 603316 = 1707713367 := by
        calc
          (13 : ZMod 6177956401) ^ 603316 = (13 : ZMod 6177956401) ^ (301658 + 301658) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 301658 * (13 : ZMod 6177956401) ^ 301658 := by rw [pow_add]
          _ = 1707713367 := by rw [factor_2_18]; decide
      have factor_2_20 : (13 : ZMod 6177956401) ^ 1206632 = 4987656626 := by
        calc
          (13 : ZMod 6177956401) ^ 1206632 = (13 : ZMod 6177956401) ^ (603316 + 603316) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 603316 * (13 : ZMod 6177956401) ^ 603316 := by rw [pow_add]
          _ = 4987656626 := by rw [factor_2_19]; decide
      have factor_2_21 : (13 : ZMod 6177956401) ^ 2413264 = 3908688133 := by
        calc
          (13 : ZMod 6177956401) ^ 2413264 = (13 : ZMod 6177956401) ^ (1206632 + 1206632) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1206632 * (13 : ZMod 6177956401) ^ 1206632 := by rw [pow_add]
          _ = 3908688133 := by rw [factor_2_20]; decide
      have factor_2_22 : (13 : ZMod 6177956401) ^ 4826528 = 4593271465 := by
        calc
          (13 : ZMod 6177956401) ^ 4826528 = (13 : ZMod 6177956401) ^ (2413264 + 2413264) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 2413264 * (13 : ZMod 6177956401) ^ 2413264 := by rw [pow_add]
          _ = 4593271465 := by rw [factor_2_21]; decide
      have factor_2_23 : (13 : ZMod 6177956401) ^ 9653056 = 2421834376 := by
        calc
          (13 : ZMod 6177956401) ^ 9653056 = (13 : ZMod 6177956401) ^ (4826528 + 4826528) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 4826528 * (13 : ZMod 6177956401) ^ 4826528 := by rw [pow_add]
          _ = 2421834376 := by rw [factor_2_22]; decide
      have factor_2_24 : (13 : ZMod 6177956401) ^ 19306113 = 5769021318 := by
        calc
          (13 : ZMod 6177956401) ^ 19306113 = (13 : ZMod 6177956401) ^ (9653056 + 9653056 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 9653056 * (13 : ZMod 6177956401) ^ 9653056) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5769021318 := by rw [factor_2_23]; decide
      have factor_2_25 : (13 : ZMod 6177956401) ^ 38612227 = 6122526891 := by
        calc
          (13 : ZMod 6177956401) ^ 38612227 = (13 : ZMod 6177956401) ^ (19306113 + 19306113 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 19306113 * (13 : ZMod 6177956401) ^ 19306113) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 6122526891 := by rw [factor_2_24]; decide
      have factor_2_26 : (13 : ZMod 6177956401) ^ 77224455 = 3538260521 := by
        calc
          (13 : ZMod 6177956401) ^ 77224455 = (13 : ZMod 6177956401) ^ (38612227 + 38612227 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 38612227 * (13 : ZMod 6177956401) ^ 38612227) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3538260521 := by rw [factor_2_25]; decide
      have factor_2_27 : (13 : ZMod 6177956401) ^ 154448910 = 2237241859 := by
        calc
          (13 : ZMod 6177956401) ^ 154448910 = (13 : ZMod 6177956401) ^ (77224455 + 77224455) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 77224455 * (13 : ZMod 6177956401) ^ 77224455 := by rw [pow_add]
          _ = 2237241859 := by rw [factor_2_26]; decide
      have factor_2_28 : (13 : ZMod 6177956401) ^ 308897820 = 3572182385 := by
        calc
          (13 : ZMod 6177956401) ^ 308897820 = (13 : ZMod 6177956401) ^ (154448910 + 154448910) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 154448910 * (13 : ZMod 6177956401) ^ 154448910 := by rw [pow_add]
          _ = 3572182385 := by rw [factor_2_27]; decide
      have factor_2_29 : (13 : ZMod 6177956401) ^ 617795640 = 2208403891 := by
        calc
          (13 : ZMod 6177956401) ^ 617795640 = (13 : ZMod 6177956401) ^ (308897820 + 308897820) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 308897820 * (13 : ZMod 6177956401) ^ 308897820 := by rw [pow_add]
          _ = 2208403891 := by rw [factor_2_28]; decide
      have factor_2_30 : (13 : ZMod 6177956401) ^ 1235591280 = 1904928932 := by
        calc
          (13 : ZMod 6177956401) ^ 1235591280 = (13 : ZMod 6177956401) ^ (617795640 + 617795640) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 617795640 * (13 : ZMod 6177956401) ^ 617795640 := by rw [pow_add]
          _ = 1904928932 := by rw [factor_2_29]; decide
      change (13 : ZMod 6177956401) ^ 1235591280 ≠ 1
      rw [factor_2_30]
      decide
    ·
      have factor_3_0 : (13 : ZMod 6177956401) ^ 1 = 13 := by norm_num
      have factor_3_1 : (13 : ZMod 6177956401) ^ 3 = 2197 := by
        calc
          (13 : ZMod 6177956401) ^ 3 = (13 : ZMod 6177956401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 1 * (13 : ZMod 6177956401) ^ 1) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_3_0]; decide
      have factor_3_2 : (13 : ZMod 6177956401) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 6177956401) ^ 6 = (13 : ZMod 6177956401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 3 * (13 : ZMod 6177956401) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_3_1]; decide
      have factor_3_3 : (13 : ZMod 6177956401) ^ 13 = 794033228 := by
        calc
          (13 : ZMod 6177956401) ^ 13 = (13 : ZMod 6177956401) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 6 * (13 : ZMod 6177956401) ^ 6) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 794033228 := by rw [factor_3_2]; decide
      have factor_3_4 : (13 : ZMod 6177956401) ^ 26 = 2871864201 := by
        calc
          (13 : ZMod 6177956401) ^ 26 = (13 : ZMod 6177956401) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 13 * (13 : ZMod 6177956401) ^ 13 := by rw [pow_add]
          _ = 2871864201 := by rw [factor_3_3]; decide
      have factor_3_5 : (13 : ZMod 6177956401) ^ 52 = 319562790 := by
        calc
          (13 : ZMod 6177956401) ^ 52 = (13 : ZMod 6177956401) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 26 * (13 : ZMod 6177956401) ^ 26 := by rw [pow_add]
          _ = 319562790 := by rw [factor_3_4]; decide
      have factor_3_6 : (13 : ZMod 6177956401) ^ 105 = 2128691915 := by
        calc
          (13 : ZMod 6177956401) ^ 105 = (13 : ZMod 6177956401) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 52 * (13 : ZMod 6177956401) ^ 52) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2128691915 := by rw [factor_3_5]; decide
      have factor_3_7 : (13 : ZMod 6177956401) ^ 210 = 2375054682 := by
        calc
          (13 : ZMod 6177956401) ^ 210 = (13 : ZMod 6177956401) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 105 * (13 : ZMod 6177956401) ^ 105 := by rw [pow_add]
          _ = 2375054682 := by rw [factor_3_6]; decide
      have factor_3_8 : (13 : ZMod 6177956401) ^ 420 = 4640405471 := by
        calc
          (13 : ZMod 6177956401) ^ 420 = (13 : ZMod 6177956401) ^ (210 + 210) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 210 * (13 : ZMod 6177956401) ^ 210 := by rw [pow_add]
          _ = 4640405471 := by rw [factor_3_7]; decide
      have factor_3_9 : (13 : ZMod 6177956401) ^ 841 = 1748161336 := by
        calc
          (13 : ZMod 6177956401) ^ 841 = (13 : ZMod 6177956401) ^ (420 + 420 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 420 * (13 : ZMod 6177956401) ^ 420) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1748161336 := by rw [factor_3_8]; decide
      have factor_3_10 : (13 : ZMod 6177956401) ^ 1683 = 843006206 := by
        calc
          (13 : ZMod 6177956401) ^ 1683 = (13 : ZMod 6177956401) ^ (841 + 841 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 841 * (13 : ZMod 6177956401) ^ 841) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 843006206 := by rw [factor_3_9]; decide
      have factor_3_11 : (13 : ZMod 6177956401) ^ 3366 = 1349967357 := by
        calc
          (13 : ZMod 6177956401) ^ 3366 = (13 : ZMod 6177956401) ^ (1683 + 1683) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1683 * (13 : ZMod 6177956401) ^ 1683 := by rw [pow_add]
          _ = 1349967357 := by rw [factor_3_10]; decide
      have factor_3_12 : (13 : ZMod 6177956401) ^ 6733 = 680077074 := by
        calc
          (13 : ZMod 6177956401) ^ 6733 = (13 : ZMod 6177956401) ^ (3366 + 3366 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 3366 * (13 : ZMod 6177956401) ^ 3366) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 680077074 := by rw [factor_3_11]; decide
      have factor_3_13 : (13 : ZMod 6177956401) ^ 13466 = 3691904152 := by
        calc
          (13 : ZMod 6177956401) ^ 13466 = (13 : ZMod 6177956401) ^ (6733 + 6733) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 6733 * (13 : ZMod 6177956401) ^ 6733 := by rw [pow_add]
          _ = 3691904152 := by rw [factor_3_12]; decide
      have factor_3_14 : (13 : ZMod 6177956401) ^ 26933 = 3279505871 := by
        calc
          (13 : ZMod 6177956401) ^ 26933 = (13 : ZMod 6177956401) ^ (13466 + 13466 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 13466 * (13 : ZMod 6177956401) ^ 13466) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3279505871 := by rw [factor_3_13]; decide
      have factor_3_15 : (13 : ZMod 6177956401) ^ 53867 = 6055300163 := by
        calc
          (13 : ZMod 6177956401) ^ 53867 = (13 : ZMod 6177956401) ^ (26933 + 26933 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 26933 * (13 : ZMod 6177956401) ^ 26933) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 6055300163 := by rw [factor_3_14]; decide
      have factor_3_16 : (13 : ZMod 6177956401) ^ 107735 = 5473112787 := by
        calc
          (13 : ZMod 6177956401) ^ 107735 = (13 : ZMod 6177956401) ^ (53867 + 53867 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 53867 * (13 : ZMod 6177956401) ^ 53867) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5473112787 := by rw [factor_3_15]; decide
      have factor_3_17 : (13 : ZMod 6177956401) ^ 215470 = 4623464524 := by
        calc
          (13 : ZMod 6177956401) ^ 215470 = (13 : ZMod 6177956401) ^ (107735 + 107735) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 107735 * (13 : ZMod 6177956401) ^ 107735 := by rw [pow_add]
          _ = 4623464524 := by rw [factor_3_16]; decide
      have factor_3_18 : (13 : ZMod 6177956401) ^ 430940 = 63695670 := by
        calc
          (13 : ZMod 6177956401) ^ 430940 = (13 : ZMod 6177956401) ^ (215470 + 215470) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 215470 * (13 : ZMod 6177956401) ^ 215470 := by rw [pow_add]
          _ = 63695670 := by rw [factor_3_17]; decide
      have factor_3_19 : (13 : ZMod 6177956401) ^ 861880 = 272735388 := by
        calc
          (13 : ZMod 6177956401) ^ 861880 = (13 : ZMod 6177956401) ^ (430940 + 430940) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 430940 * (13 : ZMod 6177956401) ^ 430940 := by rw [pow_add]
          _ = 272735388 := by rw [factor_3_18]; decide
      have factor_3_20 : (13 : ZMod 6177956401) ^ 1723760 = 1319553021 := by
        calc
          (13 : ZMod 6177956401) ^ 1723760 = (13 : ZMod 6177956401) ^ (861880 + 861880) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 861880 * (13 : ZMod 6177956401) ^ 861880 := by rw [pow_add]
          _ = 1319553021 := by rw [factor_3_19]; decide
      have factor_3_21 : (13 : ZMod 6177956401) ^ 3447520 = 2762395604 := by
        calc
          (13 : ZMod 6177956401) ^ 3447520 = (13 : ZMod 6177956401) ^ (1723760 + 1723760) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1723760 * (13 : ZMod 6177956401) ^ 1723760 := by rw [pow_add]
          _ = 2762395604 := by rw [factor_3_20]; decide
      have factor_3_22 : (13 : ZMod 6177956401) ^ 6895040 = 908979920 := by
        calc
          (13 : ZMod 6177956401) ^ 6895040 = (13 : ZMod 6177956401) ^ (3447520 + 3447520) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 3447520 * (13 : ZMod 6177956401) ^ 3447520 := by rw [pow_add]
          _ = 908979920 := by rw [factor_3_21]; decide
      have factor_3_23 : (13 : ZMod 6177956401) ^ 13790081 = 6039581109 := by
        calc
          (13 : ZMod 6177956401) ^ 13790081 = (13 : ZMod 6177956401) ^ (6895040 + 6895040 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 6895040 * (13 : ZMod 6177956401) ^ 6895040) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 6039581109 := by rw [factor_3_22]; decide
      have factor_3_24 : (13 : ZMod 6177956401) ^ 27580162 = 4307125503 := by
        calc
          (13 : ZMod 6177956401) ^ 27580162 = (13 : ZMod 6177956401) ^ (13790081 + 13790081) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 13790081 * (13 : ZMod 6177956401) ^ 13790081 := by rw [pow_add]
          _ = 4307125503 := by rw [factor_3_23]; decide
      have factor_3_25 : (13 : ZMod 6177956401) ^ 55160325 = 989737328 := by
        calc
          (13 : ZMod 6177956401) ^ 55160325 = (13 : ZMod 6177956401) ^ (27580162 + 27580162 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 27580162 * (13 : ZMod 6177956401) ^ 27580162) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 989737328 := by rw [factor_3_24]; decide
      have factor_3_26 : (13 : ZMod 6177956401) ^ 110320650 = 5134647465 := by
        calc
          (13 : ZMod 6177956401) ^ 110320650 = (13 : ZMod 6177956401) ^ (55160325 + 55160325) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 55160325 * (13 : ZMod 6177956401) ^ 55160325 := by rw [pow_add]
          _ = 5134647465 := by rw [factor_3_25]; decide
      have factor_3_27 : (13 : ZMod 6177956401) ^ 220641300 = 3084989394 := by
        calc
          (13 : ZMod 6177956401) ^ 220641300 = (13 : ZMod 6177956401) ^ (110320650 + 110320650) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 110320650 * (13 : ZMod 6177956401) ^ 110320650 := by rw [pow_add]
          _ = 3084989394 := by rw [factor_3_26]; decide
      have factor_3_28 : (13 : ZMod 6177956401) ^ 441282600 = 795072767 := by
        calc
          (13 : ZMod 6177956401) ^ 441282600 = (13 : ZMod 6177956401) ^ (220641300 + 220641300) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 220641300 * (13 : ZMod 6177956401) ^ 220641300 := by rw [pow_add]
          _ = 795072767 := by rw [factor_3_27]; decide
      have factor_3_29 : (13 : ZMod 6177956401) ^ 882565200 = 4410824314 := by
        calc
          (13 : ZMod 6177956401) ^ 882565200 = (13 : ZMod 6177956401) ^ (441282600 + 441282600) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 441282600 * (13 : ZMod 6177956401) ^ 441282600 := by rw [pow_add]
          _ = 4410824314 := by rw [factor_3_28]; decide
      change (13 : ZMod 6177956401) ^ 882565200 ≠ 1
      rw [factor_3_29]
      decide
    ·
      have factor_4_0 : (13 : ZMod 6177956401) ^ 1 = 13 := by norm_num
      have factor_4_1 : (13 : ZMod 6177956401) ^ 2 = 169 := by
        calc
          (13 : ZMod 6177956401) ^ 2 = (13 : ZMod 6177956401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1 * (13 : ZMod 6177956401) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_4_0]; decide
      have factor_4_2 : (13 : ZMod 6177956401) ^ 4 = 28561 := by
        calc
          (13 : ZMod 6177956401) ^ 4 = (13 : ZMod 6177956401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 2 * (13 : ZMod 6177956401) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_4_1]; decide
      have factor_4_3 : (13 : ZMod 6177956401) ^ 8 = 815730721 := by
        calc
          (13 : ZMod 6177956401) ^ 8 = (13 : ZMod 6177956401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 4 * (13 : ZMod 6177956401) ^ 4 := by rw [pow_add]
          _ = 815730721 := by rw [factor_4_2]; decide
      have factor_4_4 : (13 : ZMod 6177956401) ^ 16 = 2307296834 := by
        calc
          (13 : ZMod 6177956401) ^ 16 = (13 : ZMod 6177956401) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 8 * (13 : ZMod 6177956401) ^ 8 := by rw [pow_add]
          _ = 2307296834 := by rw [factor_4_3]; decide
      have factor_4_5 : (13 : ZMod 6177956401) ^ 33 = 1632248451 := by
        calc
          (13 : ZMod 6177956401) ^ 33 = (13 : ZMod 6177956401) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 16 * (13 : ZMod 6177956401) ^ 16) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1632248451 := by rw [factor_4_4]; decide
      have factor_4_6 : (13 : ZMod 6177956401) ^ 66 = 245305608 := by
        calc
          (13 : ZMod 6177956401) ^ 66 = (13 : ZMod 6177956401) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 33 * (13 : ZMod 6177956401) ^ 33 := by rw [pow_add]
          _ = 245305608 := by rw [factor_4_5]; decide
      have factor_4_7 : (13 : ZMod 6177956401) ^ 133 = 724453179 := by
        calc
          (13 : ZMod 6177956401) ^ 133 = (13 : ZMod 6177956401) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 66 * (13 : ZMod 6177956401) ^ 66) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 724453179 := by rw [factor_4_6]; decide
      have factor_4_8 : (13 : ZMod 6177956401) ^ 267 = 4412577344 := by
        calc
          (13 : ZMod 6177956401) ^ 267 = (13 : ZMod 6177956401) ^ (133 + 133 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 133 * (13 : ZMod 6177956401) ^ 133) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4412577344 := by rw [factor_4_7]; decide
      have factor_4_9 : (13 : ZMod 6177956401) ^ 535 = 5574917114 := by
        calc
          (13 : ZMod 6177956401) ^ 535 = (13 : ZMod 6177956401) ^ (267 + 267 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 267 * (13 : ZMod 6177956401) ^ 267) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5574917114 := by rw [factor_4_8]; decide
      have factor_4_10 : (13 : ZMod 6177956401) ^ 1071 = 4070116782 := by
        calc
          (13 : ZMod 6177956401) ^ 1071 = (13 : ZMod 6177956401) ^ (535 + 535 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 535 * (13 : ZMod 6177956401) ^ 535) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4070116782 := by rw [factor_4_9]; decide
      have factor_4_11 : (13 : ZMod 6177956401) ^ 2142 = 2362814073 := by
        calc
          (13 : ZMod 6177956401) ^ 2142 = (13 : ZMod 6177956401) ^ (1071 + 1071) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1071 * (13 : ZMod 6177956401) ^ 1071 := by rw [pow_add]
          _ = 2362814073 := by rw [factor_4_10]; decide
      have factor_4_12 : (13 : ZMod 6177956401) ^ 4284 = 3797761387 := by
        calc
          (13 : ZMod 6177956401) ^ 4284 = (13 : ZMod 6177956401) ^ (2142 + 2142) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 2142 * (13 : ZMod 6177956401) ^ 2142 := by rw [pow_add]
          _ = 3797761387 := by rw [factor_4_11]; decide
      have factor_4_13 : (13 : ZMod 6177956401) ^ 8569 = 5714653945 := by
        calc
          (13 : ZMod 6177956401) ^ 8569 = (13 : ZMod 6177956401) ^ (4284 + 4284 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 4284 * (13 : ZMod 6177956401) ^ 4284) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5714653945 := by rw [factor_4_12]; decide
      have factor_4_14 : (13 : ZMod 6177956401) ^ 17139 = 3099010037 := by
        calc
          (13 : ZMod 6177956401) ^ 17139 = (13 : ZMod 6177956401) ^ (8569 + 8569 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 8569 * (13 : ZMod 6177956401) ^ 8569) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3099010037 := by rw [factor_4_13]; decide
      have factor_4_15 : (13 : ZMod 6177956401) ^ 34279 = 1828655852 := by
        calc
          (13 : ZMod 6177956401) ^ 34279 = (13 : ZMod 6177956401) ^ (17139 + 17139 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 17139 * (13 : ZMod 6177956401) ^ 17139) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1828655852 := by rw [factor_4_14]; decide
      have factor_4_16 : (13 : ZMod 6177956401) ^ 68558 = 2557179068 := by
        calc
          (13 : ZMod 6177956401) ^ 68558 = (13 : ZMod 6177956401) ^ (34279 + 34279) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 34279 * (13 : ZMod 6177956401) ^ 34279 := by rw [pow_add]
          _ = 2557179068 := by rw [factor_4_15]; decide
      have factor_4_17 : (13 : ZMod 6177956401) ^ 137117 = 2014911708 := by
        calc
          (13 : ZMod 6177956401) ^ 137117 = (13 : ZMod 6177956401) ^ (68558 + 68558 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 68558 * (13 : ZMod 6177956401) ^ 68558) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2014911708 := by rw [factor_4_16]; decide
      have factor_4_18 : (13 : ZMod 6177956401) ^ 274234 = 4013731595 := by
        calc
          (13 : ZMod 6177956401) ^ 274234 = (13 : ZMod 6177956401) ^ (137117 + 137117) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 137117 * (13 : ZMod 6177956401) ^ 137117 := by rw [pow_add]
          _ = 4013731595 := by rw [factor_4_17]; decide
      have factor_4_19 : (13 : ZMod 6177956401) ^ 548469 = 743080782 := by
        calc
          (13 : ZMod 6177956401) ^ 548469 = (13 : ZMod 6177956401) ^ (274234 + 274234 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 274234 * (13 : ZMod 6177956401) ^ 274234) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 743080782 := by rw [factor_4_18]; decide
      have factor_4_20 : (13 : ZMod 6177956401) ^ 1096938 = 4472503427 := by
        calc
          (13 : ZMod 6177956401) ^ 1096938 = (13 : ZMod 6177956401) ^ (548469 + 548469) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 548469 * (13 : ZMod 6177956401) ^ 548469 := by rw [pow_add]
          _ = 4472503427 := by rw [factor_4_19]; decide
      have factor_4_21 : (13 : ZMod 6177956401) ^ 2193876 = 1415757423 := by
        calc
          (13 : ZMod 6177956401) ^ 2193876 = (13 : ZMod 6177956401) ^ (1096938 + 1096938) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1096938 * (13 : ZMod 6177956401) ^ 1096938 := by rw [pow_add]
          _ = 1415757423 := by rw [factor_4_20]; decide
      have factor_4_22 : (13 : ZMod 6177956401) ^ 4387753 = 3042246205 := by
        calc
          (13 : ZMod 6177956401) ^ 4387753 = (13 : ZMod 6177956401) ^ (2193876 + 2193876 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2193876 * (13 : ZMod 6177956401) ^ 2193876) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3042246205 := by rw [factor_4_21]; decide
      have factor_4_23 : (13 : ZMod 6177956401) ^ 8775506 = 1160951425 := by
        calc
          (13 : ZMod 6177956401) ^ 8775506 = (13 : ZMod 6177956401) ^ (4387753 + 4387753) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 4387753 * (13 : ZMod 6177956401) ^ 4387753 := by rw [pow_add]
          _ = 1160951425 := by rw [factor_4_22]; decide
      have factor_4_24 : (13 : ZMod 6177956401) ^ 17551012 = 5815472540 := by
        calc
          (13 : ZMod 6177956401) ^ 17551012 = (13 : ZMod 6177956401) ^ (8775506 + 8775506) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 8775506 * (13 : ZMod 6177956401) ^ 8775506 := by rw [pow_add]
          _ = 5815472540 := by rw [factor_4_23]; decide
      have factor_4_25 : (13 : ZMod 6177956401) ^ 35102025 = 1959615443 := by
        calc
          (13 : ZMod 6177956401) ^ 35102025 = (13 : ZMod 6177956401) ^ (17551012 + 17551012 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 17551012 * (13 : ZMod 6177956401) ^ 17551012) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1959615443 := by rw [factor_4_24]; decide
      have factor_4_26 : (13 : ZMod 6177956401) ^ 70204050 = 2708216885 := by
        calc
          (13 : ZMod 6177956401) ^ 70204050 = (13 : ZMod 6177956401) ^ (35102025 + 35102025) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 35102025 * (13 : ZMod 6177956401) ^ 35102025 := by rw [pow_add]
          _ = 2708216885 := by rw [factor_4_25]; decide
      have factor_4_27 : (13 : ZMod 6177956401) ^ 140408100 = 10120666 := by
        calc
          (13 : ZMod 6177956401) ^ 140408100 = (13 : ZMod 6177956401) ^ (70204050 + 70204050) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 70204050 * (13 : ZMod 6177956401) ^ 70204050 := by rw [pow_add]
          _ = 10120666 := by rw [factor_4_26]; decide
      have factor_4_28 : (13 : ZMod 6177956401) ^ 280816200 = 3541111377 := by
        calc
          (13 : ZMod 6177956401) ^ 280816200 = (13 : ZMod 6177956401) ^ (140408100 + 140408100) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 140408100 * (13 : ZMod 6177956401) ^ 140408100 := by rw [pow_add]
          _ = 3541111377 := by rw [factor_4_27]; decide
      have factor_4_29 : (13 : ZMod 6177956401) ^ 561632400 = 558971727 := by
        calc
          (13 : ZMod 6177956401) ^ 561632400 = (13 : ZMod 6177956401) ^ (280816200 + 280816200) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 280816200 * (13 : ZMod 6177956401) ^ 280816200 := by rw [pow_add]
          _ = 558971727 := by rw [factor_4_28]; decide
      change (13 : ZMod 6177956401) ^ 561632400 ≠ 1
      rw [factor_4_29]
      decide
    ·
      have factor_5_0 : (13 : ZMod 6177956401) ^ 1 = 13 := by norm_num
      have factor_5_1 : (13 : ZMod 6177956401) ^ 2 = 169 := by
        calc
          (13 : ZMod 6177956401) ^ 2 = (13 : ZMod 6177956401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1 * (13 : ZMod 6177956401) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_5_0]; decide
      have factor_5_2 : (13 : ZMod 6177956401) ^ 5 = 371293 := by
        calc
          (13 : ZMod 6177956401) ^ 5 = (13 : ZMod 6177956401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2 * (13 : ZMod 6177956401) ^ 2) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_5_1]; decide
      have factor_5_3 : (13 : ZMod 6177956401) ^ 10 = 1943451027 := by
        calc
          (13 : ZMod 6177956401) ^ 10 = (13 : ZMod 6177956401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 5 * (13 : ZMod 6177956401) ^ 5 := by rw [pow_add]
          _ = 1943451027 := by rw [factor_5_2]; decide
      have factor_5_4 : (13 : ZMod 6177956401) ^ 21 = 4483128895 := by
        calc
          (13 : ZMod 6177956401) ^ 21 = (13 : ZMod 6177956401) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 10 * (13 : ZMod 6177956401) ^ 10) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4483128895 := by rw [factor_5_3]; decide
      have factor_5_5 : (13 : ZMod 6177956401) ^ 43 = 1159197633 := by
        calc
          (13 : ZMod 6177956401) ^ 43 = (13 : ZMod 6177956401) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 21 * (13 : ZMod 6177956401) ^ 21) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1159197633 := by rw [factor_5_4]; decide
      have factor_5_6 : (13 : ZMod 6177956401) ^ 86 = 2340655645 := by
        calc
          (13 : ZMod 6177956401) ^ 86 = (13 : ZMod 6177956401) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 43 * (13 : ZMod 6177956401) ^ 43 := by rw [pow_add]
          _ = 2340655645 := by rw [factor_5_5]; decide
      have factor_5_7 : (13 : ZMod 6177956401) ^ 173 = 2381998947 := by
        calc
          (13 : ZMod 6177956401) ^ 173 = (13 : ZMod 6177956401) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 86 * (13 : ZMod 6177956401) ^ 86) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2381998947 := by rw [factor_5_6]; decide
      have factor_5_8 : (13 : ZMod 6177956401) ^ 346 = 2318260041 := by
        calc
          (13 : ZMod 6177956401) ^ 346 = (13 : ZMod 6177956401) ^ (173 + 173) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 173 * (13 : ZMod 6177956401) ^ 173 := by rw [pow_add]
          _ = 2318260041 := by rw [factor_5_7]; decide
      have factor_5_9 : (13 : ZMod 6177956401) ^ 693 = 5007979697 := by
        calc
          (13 : ZMod 6177956401) ^ 693 = (13 : ZMod 6177956401) ^ (346 + 346 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 346 * (13 : ZMod 6177956401) ^ 346) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5007979697 := by rw [factor_5_8]; decide
      have factor_5_10 : (13 : ZMod 6177956401) ^ 1386 = 346701514 := by
        calc
          (13 : ZMod 6177956401) ^ 1386 = (13 : ZMod 6177956401) ^ (693 + 693) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 693 * (13 : ZMod 6177956401) ^ 693 := by rw [pow_add]
          _ = 346701514 := by rw [factor_5_9]; decide
      have factor_5_11 : (13 : ZMod 6177956401) ^ 2772 = 5967541611 := by
        calc
          (13 : ZMod 6177956401) ^ 2772 = (13 : ZMod 6177956401) ^ (1386 + 1386) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1386 * (13 : ZMod 6177956401) ^ 1386 := by rw [pow_add]
          _ = 5967541611 := by rw [factor_5_10]; decide
      have factor_5_12 : (13 : ZMod 6177956401) ^ 5545 = 4872115076 := by
        calc
          (13 : ZMod 6177956401) ^ 5545 = (13 : ZMod 6177956401) ^ (2772 + 2772 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2772 * (13 : ZMod 6177956401) ^ 2772) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4872115076 := by rw [factor_5_11]; decide
      have factor_5_13 : (13 : ZMod 6177956401) ^ 11090 = 5770949733 := by
        calc
          (13 : ZMod 6177956401) ^ 11090 = (13 : ZMod 6177956401) ^ (5545 + 5545) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 5545 * (13 : ZMod 6177956401) ^ 5545 := by rw [pow_add]
          _ = 5770949733 := by rw [factor_5_12]; decide
      have factor_5_14 : (13 : ZMod 6177956401) ^ 22180 = 2230892434 := by
        calc
          (13 : ZMod 6177956401) ^ 22180 = (13 : ZMod 6177956401) ^ (11090 + 11090) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 11090 * (13 : ZMod 6177956401) ^ 11090 := by rw [pow_add]
          _ = 2230892434 := by rw [factor_5_13]; decide
      have factor_5_15 : (13 : ZMod 6177956401) ^ 44361 = 1820188283 := by
        calc
          (13 : ZMod 6177956401) ^ 44361 = (13 : ZMod 6177956401) ^ (22180 + 22180 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 22180 * (13 : ZMod 6177956401) ^ 22180) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1820188283 := by rw [factor_5_14]; decide
      have factor_5_16 : (13 : ZMod 6177956401) ^ 88722 = 305031195 := by
        calc
          (13 : ZMod 6177956401) ^ 88722 = (13 : ZMod 6177956401) ^ (44361 + 44361) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 44361 * (13 : ZMod 6177956401) ^ 44361 := by rw [pow_add]
          _ = 305031195 := by rw [factor_5_15]; decide
      have factor_5_17 : (13 : ZMod 6177956401) ^ 177445 = 4640423895 := by
        calc
          (13 : ZMod 6177956401) ^ 177445 = (13 : ZMod 6177956401) ^ (88722 + 88722 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 88722 * (13 : ZMod 6177956401) ^ 88722) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4640423895 := by rw [factor_5_16]; decide
      have factor_5_18 : (13 : ZMod 6177956401) ^ 354891 = 5970452522 := by
        calc
          (13 : ZMod 6177956401) ^ 354891 = (13 : ZMod 6177956401) ^ (177445 + 177445 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 177445 * (13 : ZMod 6177956401) ^ 177445) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5970452522 := by rw [factor_5_17]; decide
      have factor_5_19 : (13 : ZMod 6177956401) ^ 709783 = 710970786 := by
        calc
          (13 : ZMod 6177956401) ^ 709783 = (13 : ZMod 6177956401) ^ (354891 + 354891 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 354891 * (13 : ZMod 6177956401) ^ 354891) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 710970786 := by rw [factor_5_18]; decide
      have factor_5_20 : (13 : ZMod 6177956401) ^ 1419567 = 1465575714 := by
        calc
          (13 : ZMod 6177956401) ^ 1419567 = (13 : ZMod 6177956401) ^ (709783 + 709783 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 709783 * (13 : ZMod 6177956401) ^ 709783) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1465575714 := by rw [factor_5_19]; decide
      have factor_5_21 : (13 : ZMod 6177956401) ^ 2839134 = 3870675424 := by
        calc
          (13 : ZMod 6177956401) ^ 2839134 = (13 : ZMod 6177956401) ^ (1419567 + 1419567) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1419567 * (13 : ZMod 6177956401) ^ 1419567 := by rw [pow_add]
          _ = 3870675424 := by rw [factor_5_20]; decide
      have factor_5_22 : (13 : ZMod 6177956401) ^ 5678268 = 381731652 := by
        calc
          (13 : ZMod 6177956401) ^ 5678268 = (13 : ZMod 6177956401) ^ (2839134 + 2839134) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 2839134 * (13 : ZMod 6177956401) ^ 2839134 := by rw [pow_add]
          _ = 381731652 := by rw [factor_5_21]; decide
      have factor_5_23 : (13 : ZMod 6177956401) ^ 11356537 = 5870348202 := by
        calc
          (13 : ZMod 6177956401) ^ 11356537 = (13 : ZMod 6177956401) ^ (5678268 + 5678268 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 5678268 * (13 : ZMod 6177956401) ^ 5678268) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5870348202 := by rw [factor_5_22]; decide
      have factor_5_24 : (13 : ZMod 6177956401) ^ 22713075 = 1868266238 := by
        calc
          (13 : ZMod 6177956401) ^ 22713075 = (13 : ZMod 6177956401) ^ (11356537 + 11356537 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 11356537 * (13 : ZMod 6177956401) ^ 11356537) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1868266238 := by rw [factor_5_23]; decide
      have factor_5_25 : (13 : ZMod 6177956401) ^ 45426150 = 5235980342 := by
        calc
          (13 : ZMod 6177956401) ^ 45426150 = (13 : ZMod 6177956401) ^ (22713075 + 22713075) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 22713075 * (13 : ZMod 6177956401) ^ 22713075 := by rw [pow_add]
          _ = 5235980342 := by rw [factor_5_24]; decide
      have factor_5_26 : (13 : ZMod 6177956401) ^ 90852300 = 4371435678 := by
        calc
          (13 : ZMod 6177956401) ^ 90852300 = (13 : ZMod 6177956401) ^ (45426150 + 45426150) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 45426150 * (13 : ZMod 6177956401) ^ 45426150 := by rw [pow_add]
          _ = 4371435678 := by rw [factor_5_25]; decide
      have factor_5_27 : (13 : ZMod 6177956401) ^ 181704600 = 2174420443 := by
        calc
          (13 : ZMod 6177956401) ^ 181704600 = (13 : ZMod 6177956401) ^ (90852300 + 90852300) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 90852300 * (13 : ZMod 6177956401) ^ 90852300 := by rw [pow_add]
          _ = 2174420443 := by rw [factor_5_26]; decide
      have factor_5_28 : (13 : ZMod 6177956401) ^ 363409200 = 5015118160 := by
        calc
          (13 : ZMod 6177956401) ^ 363409200 = (13 : ZMod 6177956401) ^ (181704600 + 181704600) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 181704600 * (13 : ZMod 6177956401) ^ 181704600 := by rw [pow_add]
          _ = 5015118160 := by rw [factor_5_27]; decide
      change (13 : ZMod 6177956401) ^ 363409200 ≠ 1
      rw [factor_5_28]
      decide
    ·
      have factor_6_0 : (13 : ZMod 6177956401) ^ 1 = 13 := by norm_num
      have factor_6_1 : (13 : ZMod 6177956401) ^ 2 = 169 := by
        calc
          (13 : ZMod 6177956401) ^ 2 = (13 : ZMod 6177956401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1 * (13 : ZMod 6177956401) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_6_0]; decide
      have factor_6_2 : (13 : ZMod 6177956401) ^ 4 = 28561 := by
        calc
          (13 : ZMod 6177956401) ^ 4 = (13 : ZMod 6177956401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 2 * (13 : ZMod 6177956401) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_6_1]; decide
      have factor_6_3 : (13 : ZMod 6177956401) ^ 9 = 4426542972 := by
        calc
          (13 : ZMod 6177956401) ^ 9 = (13 : ZMod 6177956401) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 4 * (13 : ZMod 6177956401) ^ 4) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4426542972 := by rw [factor_6_2]; decide
      have factor_6_4 : (13 : ZMod 6177956401) ^ 19 = 3206895478 := by
        calc
          (13 : ZMod 6177956401) ^ 19 = (13 : ZMod 6177956401) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 9 * (13 : ZMod 6177956401) ^ 9) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3206895478 := by rw [factor_6_3]; decide
      have factor_6_5 : (13 : ZMod 6177956401) ^ 38 = 3435048246 := by
        calc
          (13 : ZMod 6177956401) ^ 38 = (13 : ZMod 6177956401) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 19 * (13 : ZMod 6177956401) ^ 19 := by rw [pow_add]
          _ = 3435048246 := by rw [factor_6_4]; decide
      have factor_6_6 : (13 : ZMod 6177956401) ^ 77 = 2565907931 := by
        calc
          (13 : ZMod 6177956401) ^ 77 = (13 : ZMod 6177956401) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 38 * (13 : ZMod 6177956401) ^ 38) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2565907931 := by rw [factor_6_5]; decide
      have factor_6_7 : (13 : ZMod 6177956401) ^ 155 = 3514301458 := by
        calc
          (13 : ZMod 6177956401) ^ 155 = (13 : ZMod 6177956401) ^ (77 + 77 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 77 * (13 : ZMod 6177956401) ^ 77) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3514301458 := by rw [factor_6_6]; decide
      have factor_6_8 : (13 : ZMod 6177956401) ^ 310 = 4402302300 := by
        calc
          (13 : ZMod 6177956401) ^ 310 = (13 : ZMod 6177956401) ^ (155 + 155) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 155 * (13 : ZMod 6177956401) ^ 155 := by rw [pow_add]
          _ = 4402302300 := by rw [factor_6_7]; decide
      have factor_6_9 : (13 : ZMod 6177956401) ^ 620 = 843391360 := by
        calc
          (13 : ZMod 6177956401) ^ 620 = (13 : ZMod 6177956401) ^ (310 + 310) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 310 * (13 : ZMod 6177956401) ^ 310 := by rw [pow_add]
          _ = 843391360 := by rw [factor_6_8]; decide
      have factor_6_10 : (13 : ZMod 6177956401) ^ 1240 = 4671883386 := by
        calc
          (13 : ZMod 6177956401) ^ 1240 = (13 : ZMod 6177956401) ^ (620 + 620) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 620 * (13 : ZMod 6177956401) ^ 620 := by rw [pow_add]
          _ = 4671883386 := by rw [factor_6_9]; decide
      have factor_6_11 : (13 : ZMod 6177956401) ^ 2480 = 1905763912 := by
        calc
          (13 : ZMod 6177956401) ^ 2480 = (13 : ZMod 6177956401) ^ (1240 + 1240) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1240 * (13 : ZMod 6177956401) ^ 1240 := by rw [pow_add]
          _ = 1905763912 := by rw [factor_6_10]; decide
      have factor_6_12 : (13 : ZMod 6177956401) ^ 4961 = 4690861640 := by
        calc
          (13 : ZMod 6177956401) ^ 4961 = (13 : ZMod 6177956401) ^ (2480 + 2480 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2480 * (13 : ZMod 6177956401) ^ 2480) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4690861640 := by rw [factor_6_11]; decide
      have factor_6_13 : (13 : ZMod 6177956401) ^ 9922 = 1815961212 := by
        calc
          (13 : ZMod 6177956401) ^ 9922 = (13 : ZMod 6177956401) ^ (4961 + 4961) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 4961 * (13 : ZMod 6177956401) ^ 4961 := by rw [pow_add]
          _ = 1815961212 := by rw [factor_6_12]; decide
      have factor_6_14 : (13 : ZMod 6177956401) ^ 19845 = 6014876412 := by
        calc
          (13 : ZMod 6177956401) ^ 19845 = (13 : ZMod 6177956401) ^ (9922 + 9922 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 9922 * (13 : ZMod 6177956401) ^ 9922) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 6014876412 := by rw [factor_6_13]; decide
      have factor_6_15 : (13 : ZMod 6177956401) ^ 39691 = 4471593119 := by
        calc
          (13 : ZMod 6177956401) ^ 39691 = (13 : ZMod 6177956401) ^ (19845 + 19845 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 19845 * (13 : ZMod 6177956401) ^ 19845) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4471593119 := by rw [factor_6_14]; decide
      have factor_6_16 : (13 : ZMod 6177956401) ^ 79383 = 6116825316 := by
        calc
          (13 : ZMod 6177956401) ^ 79383 = (13 : ZMod 6177956401) ^ (39691 + 39691 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 39691 * (13 : ZMod 6177956401) ^ 39691) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 6116825316 := by rw [factor_6_15]; decide
      have factor_6_17 : (13 : ZMod 6177956401) ^ 158767 = 4144703102 := by
        calc
          (13 : ZMod 6177956401) ^ 158767 = (13 : ZMod 6177956401) ^ (79383 + 79383 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 79383 * (13 : ZMod 6177956401) ^ 79383) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4144703102 := by rw [factor_6_16]; decide
      have factor_6_18 : (13 : ZMod 6177956401) ^ 317534 = 3333350029 := by
        calc
          (13 : ZMod 6177956401) ^ 317534 = (13 : ZMod 6177956401) ^ (158767 + 158767) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 158767 * (13 : ZMod 6177956401) ^ 158767 := by rw [pow_add]
          _ = 3333350029 := by rw [factor_6_17]; decide
      have factor_6_19 : (13 : ZMod 6177956401) ^ 635069 = 2250572179 := by
        calc
          (13 : ZMod 6177956401) ^ 635069 = (13 : ZMod 6177956401) ^ (317534 + 317534 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 317534 * (13 : ZMod 6177956401) ^ 317534) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2250572179 := by rw [factor_6_18]; decide
      have factor_6_20 : (13 : ZMod 6177956401) ^ 1270139 = 5917642491 := by
        calc
          (13 : ZMod 6177956401) ^ 1270139 = (13 : ZMod 6177956401) ^ (635069 + 635069 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 635069 * (13 : ZMod 6177956401) ^ 635069) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5917642491 := by rw [factor_6_19]; decide
      have factor_6_21 : (13 : ZMod 6177956401) ^ 2540278 = 3032040733 := by
        calc
          (13 : ZMod 6177956401) ^ 2540278 = (13 : ZMod 6177956401) ^ (1270139 + 1270139) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1270139 * (13 : ZMod 6177956401) ^ 1270139 := by rw [pow_add]
          _ = 3032040733 := by rw [factor_6_20]; decide
      have factor_6_22 : (13 : ZMod 6177956401) ^ 5080556 = 3395312508 := by
        calc
          (13 : ZMod 6177956401) ^ 5080556 = (13 : ZMod 6177956401) ^ (2540278 + 2540278) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 2540278 * (13 : ZMod 6177956401) ^ 2540278 := by rw [pow_add]
          _ = 3395312508 := by rw [factor_6_21]; decide
      have factor_6_23 : (13 : ZMod 6177956401) ^ 10161112 = 1324516653 := by
        calc
          (13 : ZMod 6177956401) ^ 10161112 = (13 : ZMod 6177956401) ^ (5080556 + 5080556) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 5080556 * (13 : ZMod 6177956401) ^ 5080556 := by rw [pow_add]
          _ = 1324516653 := by rw [factor_6_22]; decide
      have factor_6_24 : (13 : ZMod 6177956401) ^ 20322225 = 352931781 := by
        calc
          (13 : ZMod 6177956401) ^ 20322225 = (13 : ZMod 6177956401) ^ (10161112 + 10161112 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 10161112 * (13 : ZMod 6177956401) ^ 10161112) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 352931781 := by rw [factor_6_23]; decide
      have factor_6_25 : (13 : ZMod 6177956401) ^ 40644450 = 1635104618 := by
        calc
          (13 : ZMod 6177956401) ^ 40644450 = (13 : ZMod 6177956401) ^ (20322225 + 20322225) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 20322225 * (13 : ZMod 6177956401) ^ 20322225 := by rw [pow_add]
          _ = 1635104618 := by rw [factor_6_24]; decide
      have factor_6_26 : (13 : ZMod 6177956401) ^ 81288900 = 394757982 := by
        calc
          (13 : ZMod 6177956401) ^ 81288900 = (13 : ZMod 6177956401) ^ (40644450 + 40644450) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 40644450 * (13 : ZMod 6177956401) ^ 40644450 := by rw [pow_add]
          _ = 394757982 := by rw [factor_6_25]; decide
      have factor_6_27 : (13 : ZMod 6177956401) ^ 162577800 = 4773561748 := by
        calc
          (13 : ZMod 6177956401) ^ 162577800 = (13 : ZMod 6177956401) ^ (81288900 + 81288900) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 81288900 * (13 : ZMod 6177956401) ^ 81288900 := by rw [pow_add]
          _ = 4773561748 := by rw [factor_6_26]; decide
      have factor_6_28 : (13 : ZMod 6177956401) ^ 325155600 = 3704709306 := by
        calc
          (13 : ZMod 6177956401) ^ 325155600 = (13 : ZMod 6177956401) ^ (162577800 + 162577800) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 162577800 * (13 : ZMod 6177956401) ^ 162577800 := by rw [pow_add]
          _ = 3704709306 := by rw [factor_6_27]; decide
      change (13 : ZMod 6177956401) ^ 325155600 ≠ 1
      rw [factor_6_28]
      decide
    ·
      have factor_7_0 : (13 : ZMod 6177956401) ^ 1 = 13 := by norm_num
      have factor_7_1 : (13 : ZMod 6177956401) ^ 2 = 169 := by
        calc
          (13 : ZMod 6177956401) ^ 2 = (13 : ZMod 6177956401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1 * (13 : ZMod 6177956401) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_7_0]; decide
      have factor_7_2 : (13 : ZMod 6177956401) ^ 4 = 28561 := by
        calc
          (13 : ZMod 6177956401) ^ 4 = (13 : ZMod 6177956401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 2 * (13 : ZMod 6177956401) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_7_1]; decide
      have factor_7_3 : (13 : ZMod 6177956401) ^ 8 = 815730721 := by
        calc
          (13 : ZMod 6177956401) ^ 8 = (13 : ZMod 6177956401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 4 * (13 : ZMod 6177956401) ^ 4 := by rw [pow_add]
          _ = 815730721 := by rw [factor_7_2]; decide
      have factor_7_4 : (13 : ZMod 6177956401) ^ 16 = 2307296834 := by
        calc
          (13 : ZMod 6177956401) ^ 16 = (13 : ZMod 6177956401) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 8 * (13 : ZMod 6177956401) ^ 8 := by rw [pow_add]
          _ = 2307296834 := by rw [factor_7_3]; decide
      have factor_7_5 : (13 : ZMod 6177956401) ^ 32 = 2026467235 := by
        calc
          (13 : ZMod 6177956401) ^ 32 = (13 : ZMod 6177956401) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 16 * (13 : ZMod 6177956401) ^ 16 := by rw [pow_add]
          _ = 2026467235 := by rw [factor_7_4]; decide
      have factor_7_6 : (13 : ZMod 6177956401) ^ 64 = 1573357579 := by
        calc
          (13 : ZMod 6177956401) ^ 64 = (13 : ZMod 6177956401) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 32 * (13 : ZMod 6177956401) ^ 32 := by rw [pow_add]
          _ = 1573357579 := by rw [factor_7_5]; decide
      have factor_7_7 : (13 : ZMod 6177956401) ^ 128 = 3983569430 := by
        calc
          (13 : ZMod 6177956401) ^ 128 = (13 : ZMod 6177956401) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 64 * (13 : ZMod 6177956401) ^ 64 := by rw [pow_add]
          _ = 3983569430 := by rw [factor_7_6]; decide
      have factor_7_8 : (13 : ZMod 6177956401) ^ 256 = 5695268410 := by
        calc
          (13 : ZMod 6177956401) ^ 256 = (13 : ZMod 6177956401) ^ (128 + 128) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 128 * (13 : ZMod 6177956401) ^ 128 := by rw [pow_add]
          _ = 5695268410 := by rw [factor_7_7]; decide
      have factor_7_9 : (13 : ZMod 6177956401) ^ 512 = 2283585336 := by
        calc
          (13 : ZMod 6177956401) ^ 512 = (13 : ZMod 6177956401) ^ (256 + 256) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 256 * (13 : ZMod 6177956401) ^ 256 := by rw [pow_add]
          _ = 2283585336 := by rw [factor_7_8]; decide
      have factor_7_10 : (13 : ZMod 6177956401) ^ 1024 = 96135953 := by
        calc
          (13 : ZMod 6177956401) ^ 1024 = (13 : ZMod 6177956401) ^ (512 + 512) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 512 * (13 : ZMod 6177956401) ^ 512 := by rw [pow_add]
          _ = 96135953 := by rw [factor_7_9]; decide
      have factor_7_11 : (13 : ZMod 6177956401) ^ 2049 = 4965858531 := by
        calc
          (13 : ZMod 6177956401) ^ 2049 = (13 : ZMod 6177956401) ^ (1024 + 1024 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 1024 * (13 : ZMod 6177956401) ^ 1024) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4965858531 := by rw [factor_7_10]; decide
      have factor_7_12 : (13 : ZMod 6177956401) ^ 4098 = 1450841868 := by
        calc
          (13 : ZMod 6177956401) ^ 4098 = (13 : ZMod 6177956401) ^ (2049 + 2049) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 2049 * (13 : ZMod 6177956401) ^ 2049 := by rw [pow_add]
          _ = 1450841868 := by rw [factor_7_11]; decide
      have factor_7_13 : (13 : ZMod 6177956401) ^ 8197 = 3155499636 := by
        calc
          (13 : ZMod 6177956401) ^ 8197 = (13 : ZMod 6177956401) ^ (4098 + 4098 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 4098 * (13 : ZMod 6177956401) ^ 4098) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3155499636 := by rw [factor_7_12]; decide
      have factor_7_14 : (13 : ZMod 6177956401) ^ 16394 = 2649234488 := by
        calc
          (13 : ZMod 6177956401) ^ 16394 = (13 : ZMod 6177956401) ^ (8197 + 8197) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 8197 * (13 : ZMod 6177956401) ^ 8197 := by rw [pow_add]
          _ = 2649234488 := by rw [factor_7_13]; decide
      have factor_7_15 : (13 : ZMod 6177956401) ^ 32788 = 4413190029 := by
        calc
          (13 : ZMod 6177956401) ^ 32788 = (13 : ZMod 6177956401) ^ (16394 + 16394) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 16394 * (13 : ZMod 6177956401) ^ 16394 := by rw [pow_add]
          _ = 4413190029 := by rw [factor_7_14]; decide
      have factor_7_16 : (13 : ZMod 6177956401) ^ 65577 = 2217889094 := by
        calc
          (13 : ZMod 6177956401) ^ 65577 = (13 : ZMod 6177956401) ^ (32788 + 32788 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 32788 * (13 : ZMod 6177956401) ^ 32788) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 2217889094 := by rw [factor_7_15]; decide
      have factor_7_17 : (13 : ZMod 6177956401) ^ 131155 = 3009990851 := by
        calc
          (13 : ZMod 6177956401) ^ 131155 = (13 : ZMod 6177956401) ^ (65577 + 65577 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 65577 * (13 : ZMod 6177956401) ^ 65577) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 3009990851 := by rw [factor_7_16]; decide
      have factor_7_18 : (13 : ZMod 6177956401) ^ 262311 = 6162390200 := by
        calc
          (13 : ZMod 6177956401) ^ 262311 = (13 : ZMod 6177956401) ^ (131155 + 131155 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 131155 * (13 : ZMod 6177956401) ^ 131155) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 6162390200 := by rw [factor_7_17]; decide
      have factor_7_19 : (13 : ZMod 6177956401) ^ 524622 = 985568780 := by
        calc
          (13 : ZMod 6177956401) ^ 524622 = (13 : ZMod 6177956401) ^ (262311 + 262311) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 262311 * (13 : ZMod 6177956401) ^ 262311 := by rw [pow_add]
          _ = 985568780 := by rw [factor_7_18]; decide
      have factor_7_20 : (13 : ZMod 6177956401) ^ 1049245 = 1076248017 := by
        calc
          (13 : ZMod 6177956401) ^ 1049245 = (13 : ZMod 6177956401) ^ (524622 + 524622 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 524622 * (13 : ZMod 6177956401) ^ 524622) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 1076248017 := by rw [factor_7_19]; decide
      have factor_7_21 : (13 : ZMod 6177956401) ^ 2098490 = 3802426321 := by
        calc
          (13 : ZMod 6177956401) ^ 2098490 = (13 : ZMod 6177956401) ^ (1049245 + 1049245) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 1049245 * (13 : ZMod 6177956401) ^ 1049245 := by rw [pow_add]
          _ = 3802426321 := by rw [factor_7_20]; decide
      have factor_7_22 : (13 : ZMod 6177956401) ^ 4196981 = 4729663812 := by
        calc
          (13 : ZMod 6177956401) ^ 4196981 = (13 : ZMod 6177956401) ^ (2098490 + 2098490 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 2098490 * (13 : ZMod 6177956401) ^ 2098490) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 4729663812 := by rw [factor_7_21]; decide
      have factor_7_23 : (13 : ZMod 6177956401) ^ 8393962 = 2103117833 := by
        calc
          (13 : ZMod 6177956401) ^ 8393962 = (13 : ZMod 6177956401) ^ (4196981 + 4196981) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 4196981 * (13 : ZMod 6177956401) ^ 4196981 := by rw [pow_add]
          _ = 2103117833 := by rw [factor_7_22]; decide
      have factor_7_24 : (13 : ZMod 6177956401) ^ 16787925 = 5521000630 := by
        calc
          (13 : ZMod 6177956401) ^ 16787925 = (13 : ZMod 6177956401) ^ (8393962 + 8393962 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = ((13 : ZMod 6177956401) ^ 8393962 * (13 : ZMod 6177956401) ^ 8393962) * (13 : ZMod 6177956401) := by rw [pow_succ, pow_add]
          _ = 5521000630 := by rw [factor_7_23]; decide
      have factor_7_25 : (13 : ZMod 6177956401) ^ 33575850 = 6154191428 := by
        calc
          (13 : ZMod 6177956401) ^ 33575850 = (13 : ZMod 6177956401) ^ (16787925 + 16787925) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 16787925 * (13 : ZMod 6177956401) ^ 16787925 := by rw [pow_add]
          _ = 6154191428 := by rw [factor_7_24]; decide
      have factor_7_26 : (13 : ZMod 6177956401) ^ 67151700 = 3701380512 := by
        calc
          (13 : ZMod 6177956401) ^ 67151700 = (13 : ZMod 6177956401) ^ (33575850 + 33575850) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 33575850 * (13 : ZMod 6177956401) ^ 33575850 := by rw [pow_add]
          _ = 3701380512 := by rw [factor_7_25]; decide
      have factor_7_27 : (13 : ZMod 6177956401) ^ 134303400 = 2421769926 := by
        calc
          (13 : ZMod 6177956401) ^ 134303400 = (13 : ZMod 6177956401) ^ (67151700 + 67151700) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 67151700 * (13 : ZMod 6177956401) ^ 67151700 := by rw [pow_add]
          _ = 2421769926 := by rw [factor_7_26]; decide
      have factor_7_28 : (13 : ZMod 6177956401) ^ 268606800 = 3709131747 := by
        calc
          (13 : ZMod 6177956401) ^ 268606800 = (13 : ZMod 6177956401) ^ (134303400 + 134303400) :=
            congrArg (fun n : ℕ => (13 : ZMod 6177956401) ^ n) (by norm_num)
          _ = (13 : ZMod 6177956401) ^ 134303400 * (13 : ZMod 6177956401) ^ 134303400 := by rw [pow_add]
          _ = 3709131747 := by rw [factor_7_27]; decide
      change (13 : ZMod 6177956401) ^ 268606800 ≠ 1
      rw [factor_7_28]
      decide

#print axioms prime_lucas_6177956401

end TotientTailPeriodKiller
end Erdos249257
