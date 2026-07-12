import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3064176299 : Nat.Prime 3064176299 := by
  apply lucas_primality 3064176299 (2 : ZMod 3064176299)
  ·
      have fermat_0 : (2 : ZMod 3064176299) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 3064176299) ^ 2 = 4 := by
        calc
          (2 : ZMod 3064176299) ^ 2 = (2 : ZMod 3064176299) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 1 * (2 : ZMod 3064176299) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 3064176299) ^ 5 = 32 := by
        calc
          (2 : ZMod 3064176299) ^ 5 = (2 : ZMod 3064176299) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 2 * (2 : ZMod 3064176299) ^ 2) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 3064176299) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3064176299) ^ 11 = (2 : ZMod 3064176299) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 5 * (2 : ZMod 3064176299) ^ 5) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 3064176299) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 3064176299) ^ 22 = (2 : ZMod 3064176299) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 11 * (2 : ZMod 3064176299) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 3064176299) ^ 45 = 1499823714 := by
        calc
          (2 : ZMod 3064176299) ^ 45 = (2 : ZMod 3064176299) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 22 * (2 : ZMod 3064176299) ^ 22) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1499823714 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 3064176299) ^ 91 = 836060631 := by
        calc
          (2 : ZMod 3064176299) ^ 91 = (2 : ZMod 3064176299) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 45 * (2 : ZMod 3064176299) ^ 45) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 836060631 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 3064176299) ^ 182 = 133155939 := by
        calc
          (2 : ZMod 3064176299) ^ 182 = (2 : ZMod 3064176299) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 91 * (2 : ZMod 3064176299) ^ 91 := by rw [pow_add]
          _ = 133155939 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 3064176299) ^ 365 = 634165212 := by
        calc
          (2 : ZMod 3064176299) ^ 365 = (2 : ZMod 3064176299) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 182 * (2 : ZMod 3064176299) ^ 182) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 634165212 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 3064176299) ^ 730 = 537886856 := by
        calc
          (2 : ZMod 3064176299) ^ 730 = (2 : ZMod 3064176299) ^ (365 + 365) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 365 * (2 : ZMod 3064176299) ^ 365 := by rw [pow_add]
          _ = 537886856 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 3064176299) ^ 1461 = 2536394262 := by
        calc
          (2 : ZMod 3064176299) ^ 1461 = (2 : ZMod 3064176299) ^ (730 + 730 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 730 * (2 : ZMod 3064176299) ^ 730) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2536394262 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 3064176299) ^ 2922 = 1859609278 := by
        calc
          (2 : ZMod 3064176299) ^ 2922 = (2 : ZMod 3064176299) ^ (1461 + 1461) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 1461 * (2 : ZMod 3064176299) ^ 1461 := by rw [pow_add]
          _ = 1859609278 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 3064176299) ^ 5844 = 954767593 := by
        calc
          (2 : ZMod 3064176299) ^ 5844 = (2 : ZMod 3064176299) ^ (2922 + 2922) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 2922 * (2 : ZMod 3064176299) ^ 2922 := by rw [pow_add]
          _ = 954767593 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 3064176299) ^ 11688 = 2244351763 := by
        calc
          (2 : ZMod 3064176299) ^ 11688 = (2 : ZMod 3064176299) ^ (5844 + 5844) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 5844 * (2 : ZMod 3064176299) ^ 5844 := by rw [pow_add]
          _ = 2244351763 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 3064176299) ^ 23377 = 291155231 := by
        calc
          (2 : ZMod 3064176299) ^ 23377 = (2 : ZMod 3064176299) ^ (11688 + 11688 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 11688 * (2 : ZMod 3064176299) ^ 11688) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 291155231 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 3064176299) ^ 46755 = 2498643229 := by
        calc
          (2 : ZMod 3064176299) ^ 46755 = (2 : ZMod 3064176299) ^ (23377 + 23377 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 23377 * (2 : ZMod 3064176299) ^ 23377) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2498643229 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 3064176299) ^ 93511 = 1021770075 := by
        calc
          (2 : ZMod 3064176299) ^ 93511 = (2 : ZMod 3064176299) ^ (46755 + 46755 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 46755 * (2 : ZMod 3064176299) ^ 46755) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1021770075 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 3064176299) ^ 187022 = 1232314788 := by
        calc
          (2 : ZMod 3064176299) ^ 187022 = (2 : ZMod 3064176299) ^ (93511 + 93511) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 93511 * (2 : ZMod 3064176299) ^ 93511 := by rw [pow_add]
          _ = 1232314788 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 3064176299) ^ 374044 = 2430570273 := by
        calc
          (2 : ZMod 3064176299) ^ 374044 = (2 : ZMod 3064176299) ^ (187022 + 187022) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 187022 * (2 : ZMod 3064176299) ^ 187022 := by rw [pow_add]
          _ = 2430570273 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 3064176299) ^ 748089 = 1556980961 := by
        calc
          (2 : ZMod 3064176299) ^ 748089 = (2 : ZMod 3064176299) ^ (374044 + 374044 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 374044 * (2 : ZMod 3064176299) ^ 374044) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1556980961 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 3064176299) ^ 1496179 = 2620882963 := by
        calc
          (2 : ZMod 3064176299) ^ 1496179 = (2 : ZMod 3064176299) ^ (748089 + 748089 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 748089 * (2 : ZMod 3064176299) ^ 748089) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2620882963 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 3064176299) ^ 2992359 = 828182982 := by
        calc
          (2 : ZMod 3064176299) ^ 2992359 = (2 : ZMod 3064176299) ^ (1496179 + 1496179 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 1496179 * (2 : ZMod 3064176299) ^ 1496179) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 828182982 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 3064176299) ^ 5984719 = 2250179941 := by
        calc
          (2 : ZMod 3064176299) ^ 5984719 = (2 : ZMod 3064176299) ^ (2992359 + 2992359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 2992359 * (2 : ZMod 3064176299) ^ 2992359) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2250179941 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 3064176299) ^ 11969438 = 183971445 := by
        calc
          (2 : ZMod 3064176299) ^ 11969438 = (2 : ZMod 3064176299) ^ (5984719 + 5984719) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 5984719 * (2 : ZMod 3064176299) ^ 5984719 := by rw [pow_add]
          _ = 183971445 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 3064176299) ^ 23938877 = 3010405336 := by
        calc
          (2 : ZMod 3064176299) ^ 23938877 = (2 : ZMod 3064176299) ^ (11969438 + 11969438 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 11969438 * (2 : ZMod 3064176299) ^ 11969438) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 3010405336 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 3064176299) ^ 47877754 = 2604679155 := by
        calc
          (2 : ZMod 3064176299) ^ 47877754 = (2 : ZMod 3064176299) ^ (23938877 + 23938877) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 23938877 * (2 : ZMod 3064176299) ^ 23938877 := by rw [pow_add]
          _ = 2604679155 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 3064176299) ^ 95755509 = 2627126935 := by
        calc
          (2 : ZMod 3064176299) ^ 95755509 = (2 : ZMod 3064176299) ^ (47877754 + 47877754 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 47877754 * (2 : ZMod 3064176299) ^ 47877754) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2627126935 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 3064176299) ^ 191511018 = 300192088 := by
        calc
          (2 : ZMod 3064176299) ^ 191511018 = (2 : ZMod 3064176299) ^ (95755509 + 95755509) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 95755509 * (2 : ZMod 3064176299) ^ 95755509 := by rw [pow_add]
          _ = 300192088 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 3064176299) ^ 383022037 = 950180294 := by
        calc
          (2 : ZMod 3064176299) ^ 383022037 = (2 : ZMod 3064176299) ^ (191511018 + 191511018 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 191511018 * (2 : ZMod 3064176299) ^ 191511018) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 950180294 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 3064176299) ^ 766044074 = 1757215102 := by
        calc
          (2 : ZMod 3064176299) ^ 766044074 = (2 : ZMod 3064176299) ^ (383022037 + 383022037) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 383022037 * (2 : ZMod 3064176299) ^ 383022037 := by rw [pow_add]
          _ = 1757215102 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 3064176299) ^ 1532088149 = 3064176298 := by
        calc
          (2 : ZMod 3064176299) ^ 1532088149 = (2 : ZMod 3064176299) ^ (766044074 + 766044074 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 766044074 * (2 : ZMod 3064176299) ^ 766044074) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 3064176298 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 3064176299) ^ 3064176298 = 1 := by
        calc
          (2 : ZMod 3064176299) ^ 3064176298 = (2 : ZMod 3064176299) ^ (1532088149 + 1532088149) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 1532088149 * (2 : ZMod 3064176299) ^ 1532088149 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (227, 1), (739, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (227, 1), (739, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod = 3064176299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 3064176299) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 3064176299) ^ 2 = 4 := by
        calc
          (2 : ZMod 3064176299) ^ 2 = (2 : ZMod 3064176299) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 1 * (2 : ZMod 3064176299) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 3064176299) ^ 5 = 32 := by
        calc
          (2 : ZMod 3064176299) ^ 5 = (2 : ZMod 3064176299) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 2 * (2 : ZMod 3064176299) ^ 2) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 3064176299) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3064176299) ^ 11 = (2 : ZMod 3064176299) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 5 * (2 : ZMod 3064176299) ^ 5) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 3064176299) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 3064176299) ^ 22 = (2 : ZMod 3064176299) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 11 * (2 : ZMod 3064176299) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 3064176299) ^ 45 = 1499823714 := by
        calc
          (2 : ZMod 3064176299) ^ 45 = (2 : ZMod 3064176299) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 22 * (2 : ZMod 3064176299) ^ 22) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1499823714 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 3064176299) ^ 91 = 836060631 := by
        calc
          (2 : ZMod 3064176299) ^ 91 = (2 : ZMod 3064176299) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 45 * (2 : ZMod 3064176299) ^ 45) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 836060631 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 3064176299) ^ 182 = 133155939 := by
        calc
          (2 : ZMod 3064176299) ^ 182 = (2 : ZMod 3064176299) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 91 * (2 : ZMod 3064176299) ^ 91 := by rw [pow_add]
          _ = 133155939 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 3064176299) ^ 365 = 634165212 := by
        calc
          (2 : ZMod 3064176299) ^ 365 = (2 : ZMod 3064176299) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 182 * (2 : ZMod 3064176299) ^ 182) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 634165212 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 3064176299) ^ 730 = 537886856 := by
        calc
          (2 : ZMod 3064176299) ^ 730 = (2 : ZMod 3064176299) ^ (365 + 365) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 365 * (2 : ZMod 3064176299) ^ 365 := by rw [pow_add]
          _ = 537886856 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 3064176299) ^ 1461 = 2536394262 := by
        calc
          (2 : ZMod 3064176299) ^ 1461 = (2 : ZMod 3064176299) ^ (730 + 730 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 730 * (2 : ZMod 3064176299) ^ 730) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2536394262 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 3064176299) ^ 2922 = 1859609278 := by
        calc
          (2 : ZMod 3064176299) ^ 2922 = (2 : ZMod 3064176299) ^ (1461 + 1461) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 1461 * (2 : ZMod 3064176299) ^ 1461 := by rw [pow_add]
          _ = 1859609278 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 3064176299) ^ 5844 = 954767593 := by
        calc
          (2 : ZMod 3064176299) ^ 5844 = (2 : ZMod 3064176299) ^ (2922 + 2922) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 2922 * (2 : ZMod 3064176299) ^ 2922 := by rw [pow_add]
          _ = 954767593 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 3064176299) ^ 11688 = 2244351763 := by
        calc
          (2 : ZMod 3064176299) ^ 11688 = (2 : ZMod 3064176299) ^ (5844 + 5844) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 5844 * (2 : ZMod 3064176299) ^ 5844 := by rw [pow_add]
          _ = 2244351763 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 3064176299) ^ 23377 = 291155231 := by
        calc
          (2 : ZMod 3064176299) ^ 23377 = (2 : ZMod 3064176299) ^ (11688 + 11688 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 11688 * (2 : ZMod 3064176299) ^ 11688) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 291155231 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 3064176299) ^ 46755 = 2498643229 := by
        calc
          (2 : ZMod 3064176299) ^ 46755 = (2 : ZMod 3064176299) ^ (23377 + 23377 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 23377 * (2 : ZMod 3064176299) ^ 23377) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2498643229 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 3064176299) ^ 93511 = 1021770075 := by
        calc
          (2 : ZMod 3064176299) ^ 93511 = (2 : ZMod 3064176299) ^ (46755 + 46755 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 46755 * (2 : ZMod 3064176299) ^ 46755) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1021770075 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 3064176299) ^ 187022 = 1232314788 := by
        calc
          (2 : ZMod 3064176299) ^ 187022 = (2 : ZMod 3064176299) ^ (93511 + 93511) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 93511 * (2 : ZMod 3064176299) ^ 93511 := by rw [pow_add]
          _ = 1232314788 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 3064176299) ^ 374044 = 2430570273 := by
        calc
          (2 : ZMod 3064176299) ^ 374044 = (2 : ZMod 3064176299) ^ (187022 + 187022) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 187022 * (2 : ZMod 3064176299) ^ 187022 := by rw [pow_add]
          _ = 2430570273 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 3064176299) ^ 748089 = 1556980961 := by
        calc
          (2 : ZMod 3064176299) ^ 748089 = (2 : ZMod 3064176299) ^ (374044 + 374044 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 374044 * (2 : ZMod 3064176299) ^ 374044) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1556980961 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 3064176299) ^ 1496179 = 2620882963 := by
        calc
          (2 : ZMod 3064176299) ^ 1496179 = (2 : ZMod 3064176299) ^ (748089 + 748089 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 748089 * (2 : ZMod 3064176299) ^ 748089) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2620882963 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 3064176299) ^ 2992359 = 828182982 := by
        calc
          (2 : ZMod 3064176299) ^ 2992359 = (2 : ZMod 3064176299) ^ (1496179 + 1496179 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 1496179 * (2 : ZMod 3064176299) ^ 1496179) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 828182982 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 3064176299) ^ 5984719 = 2250179941 := by
        calc
          (2 : ZMod 3064176299) ^ 5984719 = (2 : ZMod 3064176299) ^ (2992359 + 2992359 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 2992359 * (2 : ZMod 3064176299) ^ 2992359) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2250179941 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 3064176299) ^ 11969438 = 183971445 := by
        calc
          (2 : ZMod 3064176299) ^ 11969438 = (2 : ZMod 3064176299) ^ (5984719 + 5984719) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 5984719 * (2 : ZMod 3064176299) ^ 5984719 := by rw [pow_add]
          _ = 183971445 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 3064176299) ^ 23938877 = 3010405336 := by
        calc
          (2 : ZMod 3064176299) ^ 23938877 = (2 : ZMod 3064176299) ^ (11969438 + 11969438 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 11969438 * (2 : ZMod 3064176299) ^ 11969438) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 3010405336 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 3064176299) ^ 47877754 = 2604679155 := by
        calc
          (2 : ZMod 3064176299) ^ 47877754 = (2 : ZMod 3064176299) ^ (23938877 + 23938877) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 23938877 * (2 : ZMod 3064176299) ^ 23938877 := by rw [pow_add]
          _ = 2604679155 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 3064176299) ^ 95755509 = 2627126935 := by
        calc
          (2 : ZMod 3064176299) ^ 95755509 = (2 : ZMod 3064176299) ^ (47877754 + 47877754 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 47877754 * (2 : ZMod 3064176299) ^ 47877754) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2627126935 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 3064176299) ^ 191511018 = 300192088 := by
        calc
          (2 : ZMod 3064176299) ^ 191511018 = (2 : ZMod 3064176299) ^ (95755509 + 95755509) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 95755509 * (2 : ZMod 3064176299) ^ 95755509 := by rw [pow_add]
          _ = 300192088 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 3064176299) ^ 383022037 = 950180294 := by
        calc
          (2 : ZMod 3064176299) ^ 383022037 = (2 : ZMod 3064176299) ^ (191511018 + 191511018 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 191511018 * (2 : ZMod 3064176299) ^ 191511018) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 950180294 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 3064176299) ^ 766044074 = 1757215102 := by
        calc
          (2 : ZMod 3064176299) ^ 766044074 = (2 : ZMod 3064176299) ^ (383022037 + 383022037) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 383022037 * (2 : ZMod 3064176299) ^ 383022037 := by rw [pow_add]
          _ = 1757215102 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 3064176299) ^ 1532088149 = 3064176298 := by
        calc
          (2 : ZMod 3064176299) ^ 1532088149 = (2 : ZMod 3064176299) ^ (766044074 + 766044074 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 766044074 * (2 : ZMod 3064176299) ^ 766044074) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 3064176298 := by rw [factor_0_29]; decide
      change (2 : ZMod 3064176299) ^ 1532088149 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (2 : ZMod 3064176299) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 3064176299) ^ 3 = 8 := by
        calc
          (2 : ZMod 3064176299) ^ 3 = (2 : ZMod 3064176299) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 1 * (2 : ZMod 3064176299) ^ 1) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 3064176299) ^ 6 = 64 := by
        calc
          (2 : ZMod 3064176299) ^ 6 = (2 : ZMod 3064176299) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 3 * (2 : ZMod 3064176299) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 3064176299) ^ 12 = 4096 := by
        calc
          (2 : ZMod 3064176299) ^ 12 = (2 : ZMod 3064176299) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 6 * (2 : ZMod 3064176299) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 3064176299) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 3064176299) ^ 25 = (2 : ZMod 3064176299) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 12 * (2 : ZMod 3064176299) ^ 12) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 3064176299) ^ 51 = 999252427 := by
        calc
          (2 : ZMod 3064176299) ^ 51 = (2 : ZMod 3064176299) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 25 * (2 : ZMod 3064176299) ^ 25) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 999252427 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 3064176299) ^ 102 = 2441797446 := by
        calc
          (2 : ZMod 3064176299) ^ 102 = (2 : ZMod 3064176299) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 51 * (2 : ZMod 3064176299) ^ 51 := by rw [pow_add]
          _ = 2441797446 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 3064176299) ^ 205 = 2660515844 := by
        calc
          (2 : ZMod 3064176299) ^ 205 = (2 : ZMod 3064176299) ^ (102 + 102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 102 * (2 : ZMod 3064176299) ^ 102) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2660515844 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 3064176299) ^ 411 = 2069138883 := by
        calc
          (2 : ZMod 3064176299) ^ 411 = (2 : ZMod 3064176299) ^ (205 + 205 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 205 * (2 : ZMod 3064176299) ^ 205) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2069138883 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 3064176299) ^ 823 = 1186469148 := by
        calc
          (2 : ZMod 3064176299) ^ 823 = (2 : ZMod 3064176299) ^ (411 + 411 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 411 * (2 : ZMod 3064176299) ^ 411) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1186469148 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 3064176299) ^ 1647 = 979218470 := by
        calc
          (2 : ZMod 3064176299) ^ 1647 = (2 : ZMod 3064176299) ^ (823 + 823 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 823 * (2 : ZMod 3064176299) ^ 823) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 979218470 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 3064176299) ^ 3295 = 916354569 := by
        calc
          (2 : ZMod 3064176299) ^ 3295 = (2 : ZMod 3064176299) ^ (1647 + 1647 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 1647 * (2 : ZMod 3064176299) ^ 1647) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 916354569 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 3064176299) ^ 6591 = 2650005453 := by
        calc
          (2 : ZMod 3064176299) ^ 6591 = (2 : ZMod 3064176299) ^ (3295 + 3295 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 3295 * (2 : ZMod 3064176299) ^ 3295) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2650005453 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 3064176299) ^ 13182 = 840433615 := by
        calc
          (2 : ZMod 3064176299) ^ 13182 = (2 : ZMod 3064176299) ^ (6591 + 6591) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 6591 * (2 : ZMod 3064176299) ^ 6591 := by rw [pow_add]
          _ = 840433615 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 3064176299) ^ 26364 = 1845897181 := by
        calc
          (2 : ZMod 3064176299) ^ 26364 = (2 : ZMod 3064176299) ^ (13182 + 13182) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 13182 * (2 : ZMod 3064176299) ^ 13182 := by rw [pow_add]
          _ = 1845897181 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 3064176299) ^ 52728 = 270140040 := by
        calc
          (2 : ZMod 3064176299) ^ 52728 = (2 : ZMod 3064176299) ^ (26364 + 26364) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 26364 * (2 : ZMod 3064176299) ^ 26364 := by rw [pow_add]
          _ = 270140040 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 3064176299) ^ 105457 = 2742523989 := by
        calc
          (2 : ZMod 3064176299) ^ 105457 = (2 : ZMod 3064176299) ^ (52728 + 52728 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 52728 * (2 : ZMod 3064176299) ^ 52728) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2742523989 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 3064176299) ^ 210915 = 2013422987 := by
        calc
          (2 : ZMod 3064176299) ^ 210915 = (2 : ZMod 3064176299) ^ (105457 + 105457 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 105457 * (2 : ZMod 3064176299) ^ 105457) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2013422987 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 3064176299) ^ 421830 = 1684618060 := by
        calc
          (2 : ZMod 3064176299) ^ 421830 = (2 : ZMod 3064176299) ^ (210915 + 210915) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 210915 * (2 : ZMod 3064176299) ^ 210915 := by rw [pow_add]
          _ = 1684618060 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 3064176299) ^ 843660 = 2977764785 := by
        calc
          (2 : ZMod 3064176299) ^ 843660 = (2 : ZMod 3064176299) ^ (421830 + 421830) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 421830 * (2 : ZMod 3064176299) ^ 421830 := by rw [pow_add]
          _ = 2977764785 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 3064176299) ^ 1687321 = 2025873999 := by
        calc
          (2 : ZMod 3064176299) ^ 1687321 = (2 : ZMod 3064176299) ^ (843660 + 843660 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 843660 * (2 : ZMod 3064176299) ^ 843660) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2025873999 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 3064176299) ^ 3374643 = 310404444 := by
        calc
          (2 : ZMod 3064176299) ^ 3374643 = (2 : ZMod 3064176299) ^ (1687321 + 1687321 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 1687321 * (2 : ZMod 3064176299) ^ 1687321) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 310404444 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 3064176299) ^ 6749287 = 444023098 := by
        calc
          (2 : ZMod 3064176299) ^ 6749287 = (2 : ZMod 3064176299) ^ (3374643 + 3374643 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 3374643 * (2 : ZMod 3064176299) ^ 3374643) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 444023098 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 3064176299) ^ 13498574 = 2365742921 := by
        calc
          (2 : ZMod 3064176299) ^ 13498574 = (2 : ZMod 3064176299) ^ (6749287 + 6749287) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 6749287 * (2 : ZMod 3064176299) ^ 6749287 := by rw [pow_add]
          _ = 2365742921 := by rw [factor_1_22]; decide
      change (2 : ZMod 3064176299) ^ 13498574 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (2 : ZMod 3064176299) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 3064176299) ^ 3 = 8 := by
        calc
          (2 : ZMod 3064176299) ^ 3 = (2 : ZMod 3064176299) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 1 * (2 : ZMod 3064176299) ^ 1) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 3064176299) ^ 7 = 128 := by
        calc
          (2 : ZMod 3064176299) ^ 7 = (2 : ZMod 3064176299) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 3 * (2 : ZMod 3064176299) ^ 3) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 3064176299) ^ 15 = 32768 := by
        calc
          (2 : ZMod 3064176299) ^ 15 = (2 : ZMod 3064176299) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 7 * (2 : ZMod 3064176299) ^ 7) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 3064176299) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 3064176299) ^ 31 = (2 : ZMod 3064176299) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 15 * (2 : ZMod 3064176299) ^ 15) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 3064176299) ^ 63 = 2262581827 := by
        calc
          (2 : ZMod 3064176299) ^ 63 = (2 : ZMod 3064176299) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 31 * (2 : ZMod 3064176299) ^ 31) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2262581827 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 3064176299) ^ 126 = 2995136454 := by
        calc
          (2 : ZMod 3064176299) ^ 126 = (2 : ZMod 3064176299) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 63 * (2 : ZMod 3064176299) ^ 63 := by rw [pow_add]
          _ = 2995136454 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 3064176299) ^ 253 = 1677137263 := by
        calc
          (2 : ZMod 3064176299) ^ 253 = (2 : ZMod 3064176299) ^ (126 + 126 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 126 * (2 : ZMod 3064176299) ^ 126) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1677137263 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 3064176299) ^ 506 = 1853162456 := by
        calc
          (2 : ZMod 3064176299) ^ 506 = (2 : ZMod 3064176299) ^ (253 + 253) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 253 * (2 : ZMod 3064176299) ^ 253 := by rw [pow_add]
          _ = 1853162456 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 3064176299) ^ 1012 = 2741278021 := by
        calc
          (2 : ZMod 3064176299) ^ 1012 = (2 : ZMod 3064176299) ^ (506 + 506) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 506 * (2 : ZMod 3064176299) ^ 506 := by rw [pow_add]
          _ = 2741278021 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 3064176299) ^ 2024 = 1979623917 := by
        calc
          (2 : ZMod 3064176299) ^ 2024 = (2 : ZMod 3064176299) ^ (1012 + 1012) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 1012 * (2 : ZMod 3064176299) ^ 1012 := by rw [pow_add]
          _ = 1979623917 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 3064176299) ^ 4049 = 2245970604 := by
        calc
          (2 : ZMod 3064176299) ^ 4049 = (2 : ZMod 3064176299) ^ (2024 + 2024 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 2024 * (2 : ZMod 3064176299) ^ 2024) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2245970604 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 3064176299) ^ 8098 = 1772051403 := by
        calc
          (2 : ZMod 3064176299) ^ 8098 = (2 : ZMod 3064176299) ^ (4049 + 4049) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 4049 * (2 : ZMod 3064176299) ^ 4049 := by rw [pow_add]
          _ = 1772051403 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 3064176299) ^ 16196 = 1212738055 := by
        calc
          (2 : ZMod 3064176299) ^ 16196 = (2 : ZMod 3064176299) ^ (8098 + 8098) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 8098 * (2 : ZMod 3064176299) ^ 8098 := by rw [pow_add]
          _ = 1212738055 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 3064176299) ^ 32393 = 520292886 := by
        calc
          (2 : ZMod 3064176299) ^ 32393 = (2 : ZMod 3064176299) ^ (16196 + 16196 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 16196 * (2 : ZMod 3064176299) ^ 16196) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 520292886 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 3064176299) ^ 64787 = 2890582012 := by
        calc
          (2 : ZMod 3064176299) ^ 64787 = (2 : ZMod 3064176299) ^ (32393 + 32393 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 32393 * (2 : ZMod 3064176299) ^ 32393) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2890582012 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 3064176299) ^ 129574 = 671306278 := by
        calc
          (2 : ZMod 3064176299) ^ 129574 = (2 : ZMod 3064176299) ^ (64787 + 64787) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 64787 * (2 : ZMod 3064176299) ^ 64787 := by rw [pow_add]
          _ = 671306278 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 3064176299) ^ 259148 = 2934961494 := by
        calc
          (2 : ZMod 3064176299) ^ 259148 = (2 : ZMod 3064176299) ^ (129574 + 129574) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 129574 * (2 : ZMod 3064176299) ^ 129574 := by rw [pow_add]
          _ = 2934961494 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 3064176299) ^ 518297 = 1046495199 := by
        calc
          (2 : ZMod 3064176299) ^ 518297 = (2 : ZMod 3064176299) ^ (259148 + 259148 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 259148 * (2 : ZMod 3064176299) ^ 259148) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1046495199 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 3064176299) ^ 1036595 = 412704279 := by
        calc
          (2 : ZMod 3064176299) ^ 1036595 = (2 : ZMod 3064176299) ^ (518297 + 518297 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 518297 * (2 : ZMod 3064176299) ^ 518297) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 412704279 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 3064176299) ^ 2073191 = 1512925867 := by
        calc
          (2 : ZMod 3064176299) ^ 2073191 = (2 : ZMod 3064176299) ^ (1036595 + 1036595 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 1036595 * (2 : ZMod 3064176299) ^ 1036595) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1512925867 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 3064176299) ^ 4146382 = 1334039515 := by
        calc
          (2 : ZMod 3064176299) ^ 4146382 = (2 : ZMod 3064176299) ^ (2073191 + 2073191) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 2073191 * (2 : ZMod 3064176299) ^ 2073191 := by rw [pow_add]
          _ = 1334039515 := by rw [factor_2_20]; decide
      change (2 : ZMod 3064176299) ^ 4146382 ≠ 1
      rw [factor_2_21]
      decide
    ·
      have factor_3_0 : (2 : ZMod 3064176299) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 3064176299) ^ 2 = 4 := by
        calc
          (2 : ZMod 3064176299) ^ 2 = (2 : ZMod 3064176299) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 1 * (2 : ZMod 3064176299) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 3064176299) ^ 5 = 32 := by
        calc
          (2 : ZMod 3064176299) ^ 5 = (2 : ZMod 3064176299) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 2 * (2 : ZMod 3064176299) ^ 2) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 3064176299) ^ 10 = 1024 := by
        calc
          (2 : ZMod 3064176299) ^ 10 = (2 : ZMod 3064176299) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 5 * (2 : ZMod 3064176299) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 3064176299) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 3064176299) ^ 20 = (2 : ZMod 3064176299) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 10 * (2 : ZMod 3064176299) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 3064176299) ^ 40 = 2536512734 := by
        calc
          (2 : ZMod 3064176299) ^ 40 = (2 : ZMod 3064176299) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 20 * (2 : ZMod 3064176299) ^ 20 := by rw [pow_add]
          _ = 2536512734 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 3064176299) ^ 81 = 1900964854 := by
        calc
          (2 : ZMod 3064176299) ^ 81 = (2 : ZMod 3064176299) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 40 * (2 : ZMod 3064176299) ^ 40) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1900964854 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 3064176299) ^ 163 = 704461333 := by
        calc
          (2 : ZMod 3064176299) ^ 163 = (2 : ZMod 3064176299) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 81 * (2 : ZMod 3064176299) ^ 81) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 704461333 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 3064176299) ^ 327 = 1110566810 := by
        calc
          (2 : ZMod 3064176299) ^ 327 = (2 : ZMod 3064176299) ^ (163 + 163 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 163 * (2 : ZMod 3064176299) ^ 163) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1110566810 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 3064176299) ^ 655 = 843134466 := by
        calc
          (2 : ZMod 3064176299) ^ 655 = (2 : ZMod 3064176299) ^ (327 + 327 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 327 * (2 : ZMod 3064176299) ^ 327) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 843134466 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 3064176299) ^ 1310 = 2347190856 := by
        calc
          (2 : ZMod 3064176299) ^ 1310 = (2 : ZMod 3064176299) ^ (655 + 655) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 655 * (2 : ZMod 3064176299) ^ 655 := by rw [pow_add]
          _ = 2347190856 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 3064176299) ^ 2621 = 1386256798 := by
        calc
          (2 : ZMod 3064176299) ^ 2621 = (2 : ZMod 3064176299) ^ (1310 + 1310 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 1310 * (2 : ZMod 3064176299) ^ 1310) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 1386256798 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 3064176299) ^ 5242 = 2731984 := by
        calc
          (2 : ZMod 3064176299) ^ 5242 = (2 : ZMod 3064176299) ^ (2621 + 2621) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 2621 * (2 : ZMod 3064176299) ^ 2621 := by rw [pow_add]
          _ = 2731984 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 3064176299) ^ 10484 = 2467288191 := by
        calc
          (2 : ZMod 3064176299) ^ 10484 = (2 : ZMod 3064176299) ^ (5242 + 5242) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 5242 * (2 : ZMod 3064176299) ^ 5242 := by rw [pow_add]
          _ = 2467288191 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 3064176299) ^ 20969 = 2147998100 := by
        calc
          (2 : ZMod 3064176299) ^ 20969 = (2 : ZMod 3064176299) ^ (10484 + 10484 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 10484 * (2 : ZMod 3064176299) ^ 10484) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2147998100 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 3064176299) ^ 41938 = 2240464638 := by
        calc
          (2 : ZMod 3064176299) ^ 41938 = (2 : ZMod 3064176299) ^ (20969 + 20969) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 20969 * (2 : ZMod 3064176299) ^ 20969 := by rw [pow_add]
          _ = 2240464638 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 3064176299) ^ 83876 = 2456239732 := by
        calc
          (2 : ZMod 3064176299) ^ 83876 = (2 : ZMod 3064176299) ^ (41938 + 41938) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 41938 * (2 : ZMod 3064176299) ^ 41938 := by rw [pow_add]
          _ = 2456239732 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 3064176299) ^ 167753 = 2272566190 := by
        calc
          (2 : ZMod 3064176299) ^ 167753 = (2 : ZMod 3064176299) ^ (83876 + 83876 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = ((2 : ZMod 3064176299) ^ 83876 * (2 : ZMod 3064176299) ^ 83876) * (2 : ZMod 3064176299) := by rw [pow_succ, pow_add]
          _ = 2272566190 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 3064176299) ^ 335506 = 2086399427 := by
        calc
          (2 : ZMod 3064176299) ^ 335506 = (2 : ZMod 3064176299) ^ (167753 + 167753) :=
            congrArg (fun n : ℕ => (2 : ZMod 3064176299) ^ n) (by norm_num)
          _ = (2 : ZMod 3064176299) ^ 167753 * (2 : ZMod 3064176299) ^ 167753 := by rw [pow_add]
          _ = 2086399427 := by rw [factor_3_17]; decide
      change (2 : ZMod 3064176299) ^ 335506 ≠ 1
      rw [factor_3_18]
      decide

#print axioms prime_lucas_3064176299

end TotientTailPeriodKiller
end Erdos249257
