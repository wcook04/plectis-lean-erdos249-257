import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1295780383 : Nat.Prime 1295780383 := by
  apply lucas_primality 1295780383 (5 : ZMod 1295780383)
  ·
      have fermat_0 : (5 : ZMod 1295780383) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 1295780383) ^ 2 = 25 := by
        calc
          (5 : ZMod 1295780383) ^ 2 = (5 : ZMod 1295780383) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 1 * (5 : ZMod 1295780383) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 1295780383) ^ 4 = 625 := by
        calc
          (5 : ZMod 1295780383) ^ 4 = (5 : ZMod 1295780383) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 2 * (5 : ZMod 1295780383) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 1295780383) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 1295780383) ^ 9 = (5 : ZMod 1295780383) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 4 * (5 : ZMod 1295780383) ^ 4) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 1295780383) ^ 19 = 894870748 := by
        calc
          (5 : ZMod 1295780383) ^ 19 = (5 : ZMod 1295780383) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 9 * (5 : ZMod 1295780383) ^ 9) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 894870748 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 1295780383) ^ 38 = 221751992 := by
        calc
          (5 : ZMod 1295780383) ^ 38 = (5 : ZMod 1295780383) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 19 * (5 : ZMod 1295780383) ^ 19 := by rw [pow_add]
          _ = 221751992 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 1295780383) ^ 77 = 830169587 := by
        calc
          (5 : ZMod 1295780383) ^ 77 = (5 : ZMod 1295780383) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 38 * (5 : ZMod 1295780383) ^ 38) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 830169587 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 1295780383) ^ 154 = 1037268739 := by
        calc
          (5 : ZMod 1295780383) ^ 154 = (5 : ZMod 1295780383) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 77 * (5 : ZMod 1295780383) ^ 77 := by rw [pow_add]
          _ = 1037268739 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 1295780383) ^ 308 = 1006471890 := by
        calc
          (5 : ZMod 1295780383) ^ 308 = (5 : ZMod 1295780383) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 154 * (5 : ZMod 1295780383) ^ 154 := by rw [pow_add]
          _ = 1006471890 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 1295780383) ^ 617 = 401831094 := by
        calc
          (5 : ZMod 1295780383) ^ 617 = (5 : ZMod 1295780383) ^ (308 + 308 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 308 * (5 : ZMod 1295780383) ^ 308) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 401831094 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 1295780383) ^ 1235 = 142745244 := by
        calc
          (5 : ZMod 1295780383) ^ 1235 = (5 : ZMod 1295780383) ^ (617 + 617 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 617 * (5 : ZMod 1295780383) ^ 617) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 142745244 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 1295780383) ^ 2471 = 554916888 := by
        calc
          (5 : ZMod 1295780383) ^ 2471 = (5 : ZMod 1295780383) ^ (1235 + 1235 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 1235 * (5 : ZMod 1295780383) ^ 1235) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 554916888 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 1295780383) ^ 4943 = 681326858 := by
        calc
          (5 : ZMod 1295780383) ^ 4943 = (5 : ZMod 1295780383) ^ (2471 + 2471 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 2471 * (5 : ZMod 1295780383) ^ 2471) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 681326858 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 1295780383) ^ 9886 = 14101471 := by
        calc
          (5 : ZMod 1295780383) ^ 9886 = (5 : ZMod 1295780383) ^ (4943 + 4943) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 4943 * (5 : ZMod 1295780383) ^ 4943 := by rw [pow_add]
          _ = 14101471 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 1295780383) ^ 19772 = 1026788661 := by
        calc
          (5 : ZMod 1295780383) ^ 19772 = (5 : ZMod 1295780383) ^ (9886 + 9886) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 9886 * (5 : ZMod 1295780383) ^ 9886 := by rw [pow_add]
          _ = 1026788661 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 1295780383) ^ 39544 = 170575111 := by
        calc
          (5 : ZMod 1295780383) ^ 39544 = (5 : ZMod 1295780383) ^ (19772 + 19772) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 19772 * (5 : ZMod 1295780383) ^ 19772 := by rw [pow_add]
          _ = 170575111 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 1295780383) ^ 79088 = 1123057761 := by
        calc
          (5 : ZMod 1295780383) ^ 79088 = (5 : ZMod 1295780383) ^ (39544 + 39544) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 39544 * (5 : ZMod 1295780383) ^ 39544 := by rw [pow_add]
          _ = 1123057761 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 1295780383) ^ 158176 = 1236262091 := by
        calc
          (5 : ZMod 1295780383) ^ 158176 = (5 : ZMod 1295780383) ^ (79088 + 79088) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 79088 * (5 : ZMod 1295780383) ^ 79088 := by rw [pow_add]
          _ = 1236262091 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 1295780383) ^ 316352 = 643285353 := by
        calc
          (5 : ZMod 1295780383) ^ 316352 = (5 : ZMod 1295780383) ^ (158176 + 158176) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 158176 * (5 : ZMod 1295780383) ^ 158176 := by rw [pow_add]
          _ = 643285353 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 1295780383) ^ 632705 = 965283064 := by
        calc
          (5 : ZMod 1295780383) ^ 632705 = (5 : ZMod 1295780383) ^ (316352 + 316352 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 316352 * (5 : ZMod 1295780383) ^ 316352) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 965283064 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 1295780383) ^ 1265410 = 562744750 := by
        calc
          (5 : ZMod 1295780383) ^ 1265410 = (5 : ZMod 1295780383) ^ (632705 + 632705) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 632705 * (5 : ZMod 1295780383) ^ 632705 := by rw [pow_add]
          _ = 562744750 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 1295780383) ^ 2530821 = 787684187 := by
        calc
          (5 : ZMod 1295780383) ^ 2530821 = (5 : ZMod 1295780383) ^ (1265410 + 1265410 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 1265410 * (5 : ZMod 1295780383) ^ 1265410) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 787684187 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 1295780383) ^ 5061642 = 415930062 := by
        calc
          (5 : ZMod 1295780383) ^ 5061642 = (5 : ZMod 1295780383) ^ (2530821 + 2530821) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 2530821 * (5 : ZMod 1295780383) ^ 2530821 := by rw [pow_add]
          _ = 415930062 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 1295780383) ^ 10123284 = 703992725 := by
        calc
          (5 : ZMod 1295780383) ^ 10123284 = (5 : ZMod 1295780383) ^ (5061642 + 5061642) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 5061642 * (5 : ZMod 1295780383) ^ 5061642 := by rw [pow_add]
          _ = 703992725 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 1295780383) ^ 20246568 = 1278004079 := by
        calc
          (5 : ZMod 1295780383) ^ 20246568 = (5 : ZMod 1295780383) ^ (10123284 + 10123284) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 10123284 * (5 : ZMod 1295780383) ^ 10123284 := by rw [pow_add]
          _ = 1278004079 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 1295780383) ^ 40493136 = 205019738 := by
        calc
          (5 : ZMod 1295780383) ^ 40493136 = (5 : ZMod 1295780383) ^ (20246568 + 20246568) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 20246568 * (5 : ZMod 1295780383) ^ 20246568 := by rw [pow_add]
          _ = 205019738 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 1295780383) ^ 80986273 = 291232535 := by
        calc
          (5 : ZMod 1295780383) ^ 80986273 = (5 : ZMod 1295780383) ^ (40493136 + 40493136 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 40493136 * (5 : ZMod 1295780383) ^ 40493136) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 291232535 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 1295780383) ^ 161972547 = 821183653 := by
        calc
          (5 : ZMod 1295780383) ^ 161972547 = (5 : ZMod 1295780383) ^ (80986273 + 80986273 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 80986273 * (5 : ZMod 1295780383) ^ 80986273) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 821183653 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 1295780383) ^ 323945095 = 1107010315 := by
        calc
          (5 : ZMod 1295780383) ^ 323945095 = (5 : ZMod 1295780383) ^ (161972547 + 161972547 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 161972547 * (5 : ZMod 1295780383) ^ 161972547) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1107010315 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 1295780383) ^ 647890191 = 1295780382 := by
        calc
          (5 : ZMod 1295780383) ^ 647890191 = (5 : ZMod 1295780383) ^ (323945095 + 323945095 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 323945095 * (5 : ZMod 1295780383) ^ 323945095) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1295780382 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 1295780383) ^ 1295780382 = 1 := by
        calc
          (5 : ZMod 1295780383) ^ 1295780382 = (5 : ZMod 1295780383) ^ (647890191 + 647890191) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 647890191 * (5 : ZMod 1295780383) ^ 647890191 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (13, 1), (1845841, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (13, 1), (1845841, 1)] : List FactorBlock).map factorBlockValue).prod = 1295780383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 1295780383) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 1295780383) ^ 2 = 25 := by
        calc
          (5 : ZMod 1295780383) ^ 2 = (5 : ZMod 1295780383) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 1 * (5 : ZMod 1295780383) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 1295780383) ^ 4 = 625 := by
        calc
          (5 : ZMod 1295780383) ^ 4 = (5 : ZMod 1295780383) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 2 * (5 : ZMod 1295780383) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 1295780383) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 1295780383) ^ 9 = (5 : ZMod 1295780383) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 4 * (5 : ZMod 1295780383) ^ 4) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 1295780383) ^ 19 = 894870748 := by
        calc
          (5 : ZMod 1295780383) ^ 19 = (5 : ZMod 1295780383) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 9 * (5 : ZMod 1295780383) ^ 9) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 894870748 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 1295780383) ^ 38 = 221751992 := by
        calc
          (5 : ZMod 1295780383) ^ 38 = (5 : ZMod 1295780383) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 19 * (5 : ZMod 1295780383) ^ 19 := by rw [pow_add]
          _ = 221751992 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 1295780383) ^ 77 = 830169587 := by
        calc
          (5 : ZMod 1295780383) ^ 77 = (5 : ZMod 1295780383) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 38 * (5 : ZMod 1295780383) ^ 38) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 830169587 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 1295780383) ^ 154 = 1037268739 := by
        calc
          (5 : ZMod 1295780383) ^ 154 = (5 : ZMod 1295780383) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 77 * (5 : ZMod 1295780383) ^ 77 := by rw [pow_add]
          _ = 1037268739 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 1295780383) ^ 308 = 1006471890 := by
        calc
          (5 : ZMod 1295780383) ^ 308 = (5 : ZMod 1295780383) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 154 * (5 : ZMod 1295780383) ^ 154 := by rw [pow_add]
          _ = 1006471890 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 1295780383) ^ 617 = 401831094 := by
        calc
          (5 : ZMod 1295780383) ^ 617 = (5 : ZMod 1295780383) ^ (308 + 308 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 308 * (5 : ZMod 1295780383) ^ 308) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 401831094 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 1295780383) ^ 1235 = 142745244 := by
        calc
          (5 : ZMod 1295780383) ^ 1235 = (5 : ZMod 1295780383) ^ (617 + 617 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 617 * (5 : ZMod 1295780383) ^ 617) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 142745244 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 1295780383) ^ 2471 = 554916888 := by
        calc
          (5 : ZMod 1295780383) ^ 2471 = (5 : ZMod 1295780383) ^ (1235 + 1235 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 1235 * (5 : ZMod 1295780383) ^ 1235) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 554916888 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 1295780383) ^ 4943 = 681326858 := by
        calc
          (5 : ZMod 1295780383) ^ 4943 = (5 : ZMod 1295780383) ^ (2471 + 2471 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 2471 * (5 : ZMod 1295780383) ^ 2471) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 681326858 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 1295780383) ^ 9886 = 14101471 := by
        calc
          (5 : ZMod 1295780383) ^ 9886 = (5 : ZMod 1295780383) ^ (4943 + 4943) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 4943 * (5 : ZMod 1295780383) ^ 4943 := by rw [pow_add]
          _ = 14101471 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 1295780383) ^ 19772 = 1026788661 := by
        calc
          (5 : ZMod 1295780383) ^ 19772 = (5 : ZMod 1295780383) ^ (9886 + 9886) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 9886 * (5 : ZMod 1295780383) ^ 9886 := by rw [pow_add]
          _ = 1026788661 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 1295780383) ^ 39544 = 170575111 := by
        calc
          (5 : ZMod 1295780383) ^ 39544 = (5 : ZMod 1295780383) ^ (19772 + 19772) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 19772 * (5 : ZMod 1295780383) ^ 19772 := by rw [pow_add]
          _ = 170575111 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 1295780383) ^ 79088 = 1123057761 := by
        calc
          (5 : ZMod 1295780383) ^ 79088 = (5 : ZMod 1295780383) ^ (39544 + 39544) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 39544 * (5 : ZMod 1295780383) ^ 39544 := by rw [pow_add]
          _ = 1123057761 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 1295780383) ^ 158176 = 1236262091 := by
        calc
          (5 : ZMod 1295780383) ^ 158176 = (5 : ZMod 1295780383) ^ (79088 + 79088) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 79088 * (5 : ZMod 1295780383) ^ 79088 := by rw [pow_add]
          _ = 1236262091 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 1295780383) ^ 316352 = 643285353 := by
        calc
          (5 : ZMod 1295780383) ^ 316352 = (5 : ZMod 1295780383) ^ (158176 + 158176) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 158176 * (5 : ZMod 1295780383) ^ 158176 := by rw [pow_add]
          _ = 643285353 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 1295780383) ^ 632705 = 965283064 := by
        calc
          (5 : ZMod 1295780383) ^ 632705 = (5 : ZMod 1295780383) ^ (316352 + 316352 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 316352 * (5 : ZMod 1295780383) ^ 316352) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 965283064 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 1295780383) ^ 1265410 = 562744750 := by
        calc
          (5 : ZMod 1295780383) ^ 1265410 = (5 : ZMod 1295780383) ^ (632705 + 632705) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 632705 * (5 : ZMod 1295780383) ^ 632705 := by rw [pow_add]
          _ = 562744750 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 1295780383) ^ 2530821 = 787684187 := by
        calc
          (5 : ZMod 1295780383) ^ 2530821 = (5 : ZMod 1295780383) ^ (1265410 + 1265410 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 1265410 * (5 : ZMod 1295780383) ^ 1265410) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 787684187 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 1295780383) ^ 5061642 = 415930062 := by
        calc
          (5 : ZMod 1295780383) ^ 5061642 = (5 : ZMod 1295780383) ^ (2530821 + 2530821) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 2530821 * (5 : ZMod 1295780383) ^ 2530821 := by rw [pow_add]
          _ = 415930062 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 1295780383) ^ 10123284 = 703992725 := by
        calc
          (5 : ZMod 1295780383) ^ 10123284 = (5 : ZMod 1295780383) ^ (5061642 + 5061642) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 5061642 * (5 : ZMod 1295780383) ^ 5061642 := by rw [pow_add]
          _ = 703992725 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 1295780383) ^ 20246568 = 1278004079 := by
        calc
          (5 : ZMod 1295780383) ^ 20246568 = (5 : ZMod 1295780383) ^ (10123284 + 10123284) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 10123284 * (5 : ZMod 1295780383) ^ 10123284 := by rw [pow_add]
          _ = 1278004079 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 1295780383) ^ 40493136 = 205019738 := by
        calc
          (5 : ZMod 1295780383) ^ 40493136 = (5 : ZMod 1295780383) ^ (20246568 + 20246568) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 20246568 * (5 : ZMod 1295780383) ^ 20246568 := by rw [pow_add]
          _ = 205019738 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 1295780383) ^ 80986273 = 291232535 := by
        calc
          (5 : ZMod 1295780383) ^ 80986273 = (5 : ZMod 1295780383) ^ (40493136 + 40493136 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 40493136 * (5 : ZMod 1295780383) ^ 40493136) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 291232535 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 1295780383) ^ 161972547 = 821183653 := by
        calc
          (5 : ZMod 1295780383) ^ 161972547 = (5 : ZMod 1295780383) ^ (80986273 + 80986273 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 80986273 * (5 : ZMod 1295780383) ^ 80986273) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 821183653 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 1295780383) ^ 323945095 = 1107010315 := by
        calc
          (5 : ZMod 1295780383) ^ 323945095 = (5 : ZMod 1295780383) ^ (161972547 + 161972547 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 161972547 * (5 : ZMod 1295780383) ^ 161972547) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1107010315 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 1295780383) ^ 647890191 = 1295780382 := by
        calc
          (5 : ZMod 1295780383) ^ 647890191 = (5 : ZMod 1295780383) ^ (323945095 + 323945095 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 323945095 * (5 : ZMod 1295780383) ^ 323945095) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1295780382 := by rw [factor_0_28]; decide
      change (5 : ZMod 1295780383) ^ 647890191 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (5 : ZMod 1295780383) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 1295780383) ^ 3 = 125 := by
        calc
          (5 : ZMod 1295780383) ^ 3 = (5 : ZMod 1295780383) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 1 * (5 : ZMod 1295780383) ^ 1) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 1295780383) ^ 6 = 15625 := by
        calc
          (5 : ZMod 1295780383) ^ 6 = (5 : ZMod 1295780383) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 3 * (5 : ZMod 1295780383) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 1295780383) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 1295780383) ^ 12 = (5 : ZMod 1295780383) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 6 * (5 : ZMod 1295780383) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 1295780383) ^ 25 = 885104930 := by
        calc
          (5 : ZMod 1295780383) ^ 25 = (5 : ZMod 1295780383) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 12 * (5 : ZMod 1295780383) ^ 12) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 885104930 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 1295780383) ^ 51 = 818748325 := by
        calc
          (5 : ZMod 1295780383) ^ 51 = (5 : ZMod 1295780383) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 25 * (5 : ZMod 1295780383) ^ 25) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 818748325 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 1295780383) ^ 102 = 619601750 := by
        calc
          (5 : ZMod 1295780383) ^ 102 = (5 : ZMod 1295780383) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 51 * (5 : ZMod 1295780383) ^ 51 := by rw [pow_add]
          _ = 619601750 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 1295780383) ^ 205 = 593452008 := by
        calc
          (5 : ZMod 1295780383) ^ 205 = (5 : ZMod 1295780383) ^ (102 + 102 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 102 * (5 : ZMod 1295780383) ^ 102) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 593452008 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 1295780383) ^ 411 = 334240792 := by
        calc
          (5 : ZMod 1295780383) ^ 411 = (5 : ZMod 1295780383) ^ (205 + 205 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 205 * (5 : ZMod 1295780383) ^ 205) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 334240792 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 1295780383) ^ 823 = 640136115 := by
        calc
          (5 : ZMod 1295780383) ^ 823 = (5 : ZMod 1295780383) ^ (411 + 411 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 411 * (5 : ZMod 1295780383) ^ 411) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 640136115 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 1295780383) ^ 1647 = 12246059 := by
        calc
          (5 : ZMod 1295780383) ^ 1647 = (5 : ZMod 1295780383) ^ (823 + 823 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 823 * (5 : ZMod 1295780383) ^ 823) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 12246059 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 1295780383) ^ 3295 = 570926795 := by
        calc
          (5 : ZMod 1295780383) ^ 3295 = (5 : ZMod 1295780383) ^ (1647 + 1647 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 1647 * (5 : ZMod 1295780383) ^ 1647) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 570926795 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 1295780383) ^ 6590 = 141804132 := by
        calc
          (5 : ZMod 1295780383) ^ 6590 = (5 : ZMod 1295780383) ^ (3295 + 3295) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 3295 * (5 : ZMod 1295780383) ^ 3295 := by rw [pow_add]
          _ = 141804132 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 1295780383) ^ 13181 = 1249010569 := by
        calc
          (5 : ZMod 1295780383) ^ 13181 = (5 : ZMod 1295780383) ^ (6590 + 6590 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 6590 * (5 : ZMod 1295780383) ^ 6590) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1249010569 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 1295780383) ^ 26362 = 862369998 := by
        calc
          (5 : ZMod 1295780383) ^ 26362 = (5 : ZMod 1295780383) ^ (13181 + 13181) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 13181 * (5 : ZMod 1295780383) ^ 13181 := by rw [pow_add]
          _ = 862369998 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 1295780383) ^ 52725 = 1151367470 := by
        calc
          (5 : ZMod 1295780383) ^ 52725 = (5 : ZMod 1295780383) ^ (26362 + 26362 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 26362 * (5 : ZMod 1295780383) ^ 26362) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1151367470 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 1295780383) ^ 105450 = 460647258 := by
        calc
          (5 : ZMod 1295780383) ^ 105450 = (5 : ZMod 1295780383) ^ (52725 + 52725) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 52725 * (5 : ZMod 1295780383) ^ 52725 := by rw [pow_add]
          _ = 460647258 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 1295780383) ^ 210901 = 614577506 := by
        calc
          (5 : ZMod 1295780383) ^ 210901 = (5 : ZMod 1295780383) ^ (105450 + 105450 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 105450 * (5 : ZMod 1295780383) ^ 105450) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 614577506 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 1295780383) ^ 421803 = 1264206517 := by
        calc
          (5 : ZMod 1295780383) ^ 421803 = (5 : ZMod 1295780383) ^ (210901 + 210901 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 210901 * (5 : ZMod 1295780383) ^ 210901) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1264206517 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 1295780383) ^ 843607 = 586844147 := by
        calc
          (5 : ZMod 1295780383) ^ 843607 = (5 : ZMod 1295780383) ^ (421803 + 421803 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 421803 * (5 : ZMod 1295780383) ^ 421803) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 586844147 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 1295780383) ^ 1687214 = 843846481 := by
        calc
          (5 : ZMod 1295780383) ^ 1687214 = (5 : ZMod 1295780383) ^ (843607 + 843607) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 843607 * (5 : ZMod 1295780383) ^ 843607 := by rw [pow_add]
          _ = 843846481 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 1295780383) ^ 3374428 = 807756315 := by
        calc
          (5 : ZMod 1295780383) ^ 3374428 = (5 : ZMod 1295780383) ^ (1687214 + 1687214) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 1687214 * (5 : ZMod 1295780383) ^ 1687214 := by rw [pow_add]
          _ = 807756315 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 1295780383) ^ 6748856 = 1101725510 := by
        calc
          (5 : ZMod 1295780383) ^ 6748856 = (5 : ZMod 1295780383) ^ (3374428 + 3374428) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 3374428 * (5 : ZMod 1295780383) ^ 3374428 := by rw [pow_add]
          _ = 1101725510 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 1295780383) ^ 13497712 = 641660055 := by
        calc
          (5 : ZMod 1295780383) ^ 13497712 = (5 : ZMod 1295780383) ^ (6748856 + 6748856) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 6748856 * (5 : ZMod 1295780383) ^ 6748856 := by rw [pow_add]
          _ = 641660055 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 1295780383) ^ 26995424 = 1119161346 := by
        calc
          (5 : ZMod 1295780383) ^ 26995424 = (5 : ZMod 1295780383) ^ (13497712 + 13497712) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 13497712 * (5 : ZMod 1295780383) ^ 13497712 := by rw [pow_add]
          _ = 1119161346 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 1295780383) ^ 53990849 = 234338617 := by
        calc
          (5 : ZMod 1295780383) ^ 53990849 = (5 : ZMod 1295780383) ^ (26995424 + 26995424 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 26995424 * (5 : ZMod 1295780383) ^ 26995424) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 234338617 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 1295780383) ^ 107981698 = 478665805 := by
        calc
          (5 : ZMod 1295780383) ^ 107981698 = (5 : ZMod 1295780383) ^ (53990849 + 53990849) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 53990849 * (5 : ZMod 1295780383) ^ 53990849 := by rw [pow_add]
          _ = 478665805 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 1295780383) ^ 215963397 = 818035612 := by
        calc
          (5 : ZMod 1295780383) ^ 215963397 = (5 : ZMod 1295780383) ^ (107981698 + 107981698 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 107981698 * (5 : ZMod 1295780383) ^ 107981698) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 818035612 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 1295780383) ^ 431926794 = 818035611 := by
        calc
          (5 : ZMod 1295780383) ^ 431926794 = (5 : ZMod 1295780383) ^ (215963397 + 215963397) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 215963397 * (5 : ZMod 1295780383) ^ 215963397 := by rw [pow_add]
          _ = 818035611 := by rw [factor_1_27]; decide
      change (5 : ZMod 1295780383) ^ 431926794 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (5 : ZMod 1295780383) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 1295780383) ^ 2 = 25 := by
        calc
          (5 : ZMod 1295780383) ^ 2 = (5 : ZMod 1295780383) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 1 * (5 : ZMod 1295780383) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 1295780383) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1295780383) ^ 5 = (5 : ZMod 1295780383) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 2 * (5 : ZMod 1295780383) ^ 2) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 1295780383) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 1295780383) ^ 11 = (5 : ZMod 1295780383) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 5 * (5 : ZMod 1295780383) ^ 5) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 1295780383) ^ 23 = 812872427 := by
        calc
          (5 : ZMod 1295780383) ^ 23 = (5 : ZMod 1295780383) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 11 * (5 : ZMod 1295780383) ^ 11) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 812872427 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 1295780383) ^ 47 = 1245259165 := by
        calc
          (5 : ZMod 1295780383) ^ 47 = (5 : ZMod 1295780383) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 23 * (5 : ZMod 1295780383) ^ 23) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1245259165 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 1295780383) ^ 95 = 1279202325 := by
        calc
          (5 : ZMod 1295780383) ^ 95 = (5 : ZMod 1295780383) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 47 * (5 : ZMod 1295780383) ^ 47) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1279202325 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 1295780383) ^ 190 = 875158213 := by
        calc
          (5 : ZMod 1295780383) ^ 190 = (5 : ZMod 1295780383) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 95 * (5 : ZMod 1295780383) ^ 95 := by rw [pow_add]
          _ = 875158213 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 1295780383) ^ 380 = 638629585 := by
        calc
          (5 : ZMod 1295780383) ^ 380 = (5 : ZMod 1295780383) ^ (190 + 190) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 190 * (5 : ZMod 1295780383) ^ 190 := by rw [pow_add]
          _ = 638629585 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 1295780383) ^ 760 = 523604849 := by
        calc
          (5 : ZMod 1295780383) ^ 760 = (5 : ZMod 1295780383) ^ (380 + 380) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 380 * (5 : ZMod 1295780383) ^ 380 := by rw [pow_add]
          _ = 523604849 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 1295780383) ^ 1520 = 344849213 := by
        calc
          (5 : ZMod 1295780383) ^ 1520 = (5 : ZMod 1295780383) ^ (760 + 760) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 760 * (5 : ZMod 1295780383) ^ 760 := by rw [pow_add]
          _ = 344849213 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 1295780383) ^ 3041 = 451305657 := by
        calc
          (5 : ZMod 1295780383) ^ 3041 = (5 : ZMod 1295780383) ^ (1520 + 1520 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 1520 * (5 : ZMod 1295780383) ^ 1520) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 451305657 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 1295780383) ^ 6083 = 1067748941 := by
        calc
          (5 : ZMod 1295780383) ^ 6083 = (5 : ZMod 1295780383) ^ (3041 + 3041 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 3041 * (5 : ZMod 1295780383) ^ 3041) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1067748941 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 1295780383) ^ 12167 = 1024290078 := by
        calc
          (5 : ZMod 1295780383) ^ 12167 = (5 : ZMod 1295780383) ^ (6083 + 6083 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 6083 * (5 : ZMod 1295780383) ^ 6083) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1024290078 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 1295780383) ^ 24334 = 383927146 := by
        calc
          (5 : ZMod 1295780383) ^ 24334 = (5 : ZMod 1295780383) ^ (12167 + 12167) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 12167 * (5 : ZMod 1295780383) ^ 12167 := by rw [pow_add]
          _ = 383927146 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 1295780383) ^ 48669 = 1221776039 := by
        calc
          (5 : ZMod 1295780383) ^ 48669 = (5 : ZMod 1295780383) ^ (24334 + 24334 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 24334 * (5 : ZMod 1295780383) ^ 24334) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1221776039 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 1295780383) ^ 97339 = 949444348 := by
        calc
          (5 : ZMod 1295780383) ^ 97339 = (5 : ZMod 1295780383) ^ (48669 + 48669 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 48669 * (5 : ZMod 1295780383) ^ 48669) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 949444348 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 1295780383) ^ 194678 = 614045977 := by
        calc
          (5 : ZMod 1295780383) ^ 194678 = (5 : ZMod 1295780383) ^ (97339 + 97339) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 97339 * (5 : ZMod 1295780383) ^ 97339 := by rw [pow_add]
          _ = 614045977 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 1295780383) ^ 389357 = 969532980 := by
        calc
          (5 : ZMod 1295780383) ^ 389357 = (5 : ZMod 1295780383) ^ (194678 + 194678 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 194678 * (5 : ZMod 1295780383) ^ 194678) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 969532980 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 1295780383) ^ 778714 = 310003015 := by
        calc
          (5 : ZMod 1295780383) ^ 778714 = (5 : ZMod 1295780383) ^ (389357 + 389357) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 389357 * (5 : ZMod 1295780383) ^ 389357 := by rw [pow_add]
          _ = 310003015 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 1295780383) ^ 1557428 = 1033481773 := by
        calc
          (5 : ZMod 1295780383) ^ 1557428 = (5 : ZMod 1295780383) ^ (778714 + 778714) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 778714 * (5 : ZMod 1295780383) ^ 778714 := by rw [pow_add]
          _ = 1033481773 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 1295780383) ^ 3114856 = 1255001933 := by
        calc
          (5 : ZMod 1295780383) ^ 3114856 = (5 : ZMod 1295780383) ^ (1557428 + 1557428) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 1557428 * (5 : ZMod 1295780383) ^ 1557428 := by rw [pow_add]
          _ = 1255001933 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 1295780383) ^ 6229713 = 108422659 := by
        calc
          (5 : ZMod 1295780383) ^ 6229713 = (5 : ZMod 1295780383) ^ (3114856 + 3114856 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 3114856 * (5 : ZMod 1295780383) ^ 3114856) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 108422659 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 1295780383) ^ 12459426 = 447969087 := by
        calc
          (5 : ZMod 1295780383) ^ 12459426 = (5 : ZMod 1295780383) ^ (6229713 + 6229713) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 6229713 * (5 : ZMod 1295780383) ^ 6229713 := by rw [pow_add]
          _ = 447969087 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 1295780383) ^ 24918853 = 340798795 := by
        calc
          (5 : ZMod 1295780383) ^ 24918853 = (5 : ZMod 1295780383) ^ (12459426 + 12459426 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 12459426 * (5 : ZMod 1295780383) ^ 12459426) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 340798795 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 1295780383) ^ 49837707 = 743422813 := by
        calc
          (5 : ZMod 1295780383) ^ 49837707 = (5 : ZMod 1295780383) ^ (24918853 + 24918853 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 24918853 * (5 : ZMod 1295780383) ^ 24918853) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 743422813 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 1295780383) ^ 99675414 = 236089502 := by
        calc
          (5 : ZMod 1295780383) ^ 99675414 = (5 : ZMod 1295780383) ^ (49837707 + 49837707) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 49837707 * (5 : ZMod 1295780383) ^ 49837707 := by rw [pow_add]
          _ = 236089502 := by rw [factor_2_25]; decide
      change (5 : ZMod 1295780383) ^ 99675414 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (5 : ZMod 1295780383) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 1295780383) ^ 2 = 25 := by
        calc
          (5 : ZMod 1295780383) ^ 2 = (5 : ZMod 1295780383) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 1 * (5 : ZMod 1295780383) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 1295780383) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1295780383) ^ 5 = (5 : ZMod 1295780383) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 2 * (5 : ZMod 1295780383) ^ 2) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 1295780383) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 1295780383) ^ 10 = (5 : ZMod 1295780383) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 5 * (5 : ZMod 1295780383) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 1295780383) ^ 21 = 343502189 := by
        calc
          (5 : ZMod 1295780383) ^ 21 = (5 : ZMod 1295780383) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 10 * (5 : ZMod 1295780383) ^ 10) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 343502189 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 1295780383) ^ 43 = 1028250478 := by
        calc
          (5 : ZMod 1295780383) ^ 43 = (5 : ZMod 1295780383) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 21 * (5 : ZMod 1295780383) ^ 21) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1028250478 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 1295780383) ^ 87 = 1047325544 := by
        calc
          (5 : ZMod 1295780383) ^ 87 = (5 : ZMod 1295780383) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 43 * (5 : ZMod 1295780383) ^ 43) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 1047325544 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 1295780383) ^ 175 = 921969616 := by
        calc
          (5 : ZMod 1295780383) ^ 175 = (5 : ZMod 1295780383) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 87 * (5 : ZMod 1295780383) ^ 87) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 921969616 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 1295780383) ^ 351 = 941287605 := by
        calc
          (5 : ZMod 1295780383) ^ 351 = (5 : ZMod 1295780383) ^ (175 + 175 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = ((5 : ZMod 1295780383) ^ 175 * (5 : ZMod 1295780383) ^ 175) * (5 : ZMod 1295780383) := by rw [pow_succ, pow_add]
          _ = 941287605 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 1295780383) ^ 702 = 841674640 := by
        calc
          (5 : ZMod 1295780383) ^ 702 = (5 : ZMod 1295780383) ^ (351 + 351) :=
            congrArg (fun n : ℕ => (5 : ZMod 1295780383) ^ n) (by norm_num)
          _ = (5 : ZMod 1295780383) ^ 351 * (5 : ZMod 1295780383) ^ 351 := by rw [pow_add]
          _ = 841674640 := by rw [factor_3_8]; decide
      change (5 : ZMod 1295780383) ^ 702 ≠ 1
      rw [factor_3_9]
      decide

#print axioms prime_lucas_1295780383

end TotientTailPeriodKiller
end Erdos249257
