import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_50503979 : Nat.Prime 50503979 := by
  apply lucas_primality 50503979 (2 : ZMod 50503979)
  ·
      have fermat_0 : (2 : ZMod 50503979) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 50503979) ^ 3 = 8 := by
        calc
          (2 : ZMod 50503979) ^ 3 = (2 : ZMod 50503979) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 1 * (2 : ZMod 50503979) ^ 1) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 50503979) ^ 6 = 64 := by
        calc
          (2 : ZMod 50503979) ^ 6 = (2 : ZMod 50503979) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 3 * (2 : ZMod 50503979) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 50503979) ^ 12 = 4096 := by
        calc
          (2 : ZMod 50503979) ^ 12 = (2 : ZMod 50503979) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 6 * (2 : ZMod 50503979) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 50503979) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 50503979) ^ 24 = (2 : ZMod 50503979) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 12 * (2 : ZMod 50503979) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 50503979) ^ 48 = 39462418 := by
        calc
          (2 : ZMod 50503979) ^ 48 = (2 : ZMod 50503979) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 24 * (2 : ZMod 50503979) ^ 24 := by rw [pow_add]
          _ = 39462418 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 50503979) ^ 96 = 19554490 := by
        calc
          (2 : ZMod 50503979) ^ 96 = (2 : ZMod 50503979) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 48 * (2 : ZMod 50503979) ^ 48 := by rw [pow_add]
          _ = 19554490 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 50503979) ^ 192 = 30172266 := by
        calc
          (2 : ZMod 50503979) ^ 192 = (2 : ZMod 50503979) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 96 * (2 : ZMod 50503979) ^ 96 := by rw [pow_add]
          _ = 30172266 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 50503979) ^ 385 = 1249636 := by
        calc
          (2 : ZMod 50503979) ^ 385 = (2 : ZMod 50503979) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 192 * (2 : ZMod 50503979) ^ 192) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 1249636 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 50503979) ^ 770 = 7101816 := by
        calc
          (2 : ZMod 50503979) ^ 770 = (2 : ZMod 50503979) ^ (385 + 385) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 385 * (2 : ZMod 50503979) ^ 385 := by rw [pow_add]
          _ = 7101816 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 50503979) ^ 1541 = 34242991 := by
        calc
          (2 : ZMod 50503979) ^ 1541 = (2 : ZMod 50503979) ^ (770 + 770 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 770 * (2 : ZMod 50503979) ^ 770) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 34242991 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 50503979) ^ 3082 = 37700185 := by
        calc
          (2 : ZMod 50503979) ^ 3082 = (2 : ZMod 50503979) ^ (1541 + 1541) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 1541 * (2 : ZMod 50503979) ^ 1541 := by rw [pow_add]
          _ = 37700185 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 50503979) ^ 6165 = 25729880 := by
        calc
          (2 : ZMod 50503979) ^ 6165 = (2 : ZMod 50503979) ^ (3082 + 3082 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 3082 * (2 : ZMod 50503979) ^ 3082) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 25729880 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 50503979) ^ 12330 = 12962947 := by
        calc
          (2 : ZMod 50503979) ^ 12330 = (2 : ZMod 50503979) ^ (6165 + 6165) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 6165 * (2 : ZMod 50503979) ^ 6165 := by rw [pow_add]
          _ = 12962947 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 50503979) ^ 24660 = 44908471 := by
        calc
          (2 : ZMod 50503979) ^ 24660 = (2 : ZMod 50503979) ^ (12330 + 12330) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 12330 * (2 : ZMod 50503979) ^ 12330 := by rw [pow_add]
          _ = 44908471 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 50503979) ^ 49320 = 20516909 := by
        calc
          (2 : ZMod 50503979) ^ 49320 = (2 : ZMod 50503979) ^ (24660 + 24660) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 24660 * (2 : ZMod 50503979) ^ 24660 := by rw [pow_add]
          _ = 20516909 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 50503979) ^ 98640 = 11010320 := by
        calc
          (2 : ZMod 50503979) ^ 98640 = (2 : ZMod 50503979) ^ (49320 + 49320) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 49320 * (2 : ZMod 50503979) ^ 49320 := by rw [pow_add]
          _ = 11010320 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 50503979) ^ 197281 = 43035416 := by
        calc
          (2 : ZMod 50503979) ^ 197281 = (2 : ZMod 50503979) ^ (98640 + 98640 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 98640 * (2 : ZMod 50503979) ^ 98640) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 43035416 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 50503979) ^ 394562 = 10654545 := by
        calc
          (2 : ZMod 50503979) ^ 394562 = (2 : ZMod 50503979) ^ (197281 + 197281) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 197281 * (2 : ZMod 50503979) ^ 197281 := by rw [pow_add]
          _ = 10654545 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 50503979) ^ 789124 = 20439355 := by
        calc
          (2 : ZMod 50503979) ^ 789124 = (2 : ZMod 50503979) ^ (394562 + 394562) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 394562 * (2 : ZMod 50503979) ^ 394562 := by rw [pow_add]
          _ = 20439355 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 50503979) ^ 1578249 = 20822643 := by
        calc
          (2 : ZMod 50503979) ^ 1578249 = (2 : ZMod 50503979) ^ (789124 + 789124 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 789124 * (2 : ZMod 50503979) ^ 789124) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 20822643 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 50503979) ^ 3156498 = 44336843 := by
        calc
          (2 : ZMod 50503979) ^ 3156498 = (2 : ZMod 50503979) ^ (1578249 + 1578249) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 1578249 * (2 : ZMod 50503979) ^ 1578249 := by rw [pow_add]
          _ = 44336843 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 50503979) ^ 6312997 = 9370373 := by
        calc
          (2 : ZMod 50503979) ^ 6312997 = (2 : ZMod 50503979) ^ (3156498 + 3156498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 3156498 * (2 : ZMod 50503979) ^ 3156498) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 9370373 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 50503979) ^ 12625994 = 45956742 := by
        calc
          (2 : ZMod 50503979) ^ 12625994 = (2 : ZMod 50503979) ^ (6312997 + 6312997) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 6312997 * (2 : ZMod 50503979) ^ 6312997 := by rw [pow_add]
          _ = 45956742 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 50503979) ^ 25251989 = 50503978 := by
        calc
          (2 : ZMod 50503979) ^ 25251989 = (2 : ZMod 50503979) ^ (12625994 + 12625994 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 12625994 * (2 : ZMod 50503979) ^ 12625994) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 50503978 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 50503979) ^ 50503978 = 1 := by
        calc
          (2 : ZMod 50503979) ^ 50503978 = (2 : ZMod 50503979) ^ (25251989 + 25251989) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 25251989 * (2 : ZMod 50503979) ^ 25251989 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (631, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (631, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod = 50503979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 50503979) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 50503979) ^ 3 = 8 := by
        calc
          (2 : ZMod 50503979) ^ 3 = (2 : ZMod 50503979) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 1 * (2 : ZMod 50503979) ^ 1) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 50503979) ^ 6 = 64 := by
        calc
          (2 : ZMod 50503979) ^ 6 = (2 : ZMod 50503979) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 3 * (2 : ZMod 50503979) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 50503979) ^ 12 = 4096 := by
        calc
          (2 : ZMod 50503979) ^ 12 = (2 : ZMod 50503979) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 6 * (2 : ZMod 50503979) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 50503979) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 50503979) ^ 24 = (2 : ZMod 50503979) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 12 * (2 : ZMod 50503979) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 50503979) ^ 48 = 39462418 := by
        calc
          (2 : ZMod 50503979) ^ 48 = (2 : ZMod 50503979) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 24 * (2 : ZMod 50503979) ^ 24 := by rw [pow_add]
          _ = 39462418 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 50503979) ^ 96 = 19554490 := by
        calc
          (2 : ZMod 50503979) ^ 96 = (2 : ZMod 50503979) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 48 * (2 : ZMod 50503979) ^ 48 := by rw [pow_add]
          _ = 19554490 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 50503979) ^ 192 = 30172266 := by
        calc
          (2 : ZMod 50503979) ^ 192 = (2 : ZMod 50503979) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 96 * (2 : ZMod 50503979) ^ 96 := by rw [pow_add]
          _ = 30172266 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 50503979) ^ 385 = 1249636 := by
        calc
          (2 : ZMod 50503979) ^ 385 = (2 : ZMod 50503979) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 192 * (2 : ZMod 50503979) ^ 192) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 1249636 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 50503979) ^ 770 = 7101816 := by
        calc
          (2 : ZMod 50503979) ^ 770 = (2 : ZMod 50503979) ^ (385 + 385) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 385 * (2 : ZMod 50503979) ^ 385 := by rw [pow_add]
          _ = 7101816 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 50503979) ^ 1541 = 34242991 := by
        calc
          (2 : ZMod 50503979) ^ 1541 = (2 : ZMod 50503979) ^ (770 + 770 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 770 * (2 : ZMod 50503979) ^ 770) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 34242991 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 50503979) ^ 3082 = 37700185 := by
        calc
          (2 : ZMod 50503979) ^ 3082 = (2 : ZMod 50503979) ^ (1541 + 1541) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 1541 * (2 : ZMod 50503979) ^ 1541 := by rw [pow_add]
          _ = 37700185 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 50503979) ^ 6165 = 25729880 := by
        calc
          (2 : ZMod 50503979) ^ 6165 = (2 : ZMod 50503979) ^ (3082 + 3082 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 3082 * (2 : ZMod 50503979) ^ 3082) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 25729880 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 50503979) ^ 12330 = 12962947 := by
        calc
          (2 : ZMod 50503979) ^ 12330 = (2 : ZMod 50503979) ^ (6165 + 6165) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 6165 * (2 : ZMod 50503979) ^ 6165 := by rw [pow_add]
          _ = 12962947 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 50503979) ^ 24660 = 44908471 := by
        calc
          (2 : ZMod 50503979) ^ 24660 = (2 : ZMod 50503979) ^ (12330 + 12330) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 12330 * (2 : ZMod 50503979) ^ 12330 := by rw [pow_add]
          _ = 44908471 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 50503979) ^ 49320 = 20516909 := by
        calc
          (2 : ZMod 50503979) ^ 49320 = (2 : ZMod 50503979) ^ (24660 + 24660) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 24660 * (2 : ZMod 50503979) ^ 24660 := by rw [pow_add]
          _ = 20516909 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 50503979) ^ 98640 = 11010320 := by
        calc
          (2 : ZMod 50503979) ^ 98640 = (2 : ZMod 50503979) ^ (49320 + 49320) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 49320 * (2 : ZMod 50503979) ^ 49320 := by rw [pow_add]
          _ = 11010320 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 50503979) ^ 197281 = 43035416 := by
        calc
          (2 : ZMod 50503979) ^ 197281 = (2 : ZMod 50503979) ^ (98640 + 98640 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 98640 * (2 : ZMod 50503979) ^ 98640) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 43035416 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 50503979) ^ 394562 = 10654545 := by
        calc
          (2 : ZMod 50503979) ^ 394562 = (2 : ZMod 50503979) ^ (197281 + 197281) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 197281 * (2 : ZMod 50503979) ^ 197281 := by rw [pow_add]
          _ = 10654545 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 50503979) ^ 789124 = 20439355 := by
        calc
          (2 : ZMod 50503979) ^ 789124 = (2 : ZMod 50503979) ^ (394562 + 394562) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 394562 * (2 : ZMod 50503979) ^ 394562 := by rw [pow_add]
          _ = 20439355 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 50503979) ^ 1578249 = 20822643 := by
        calc
          (2 : ZMod 50503979) ^ 1578249 = (2 : ZMod 50503979) ^ (789124 + 789124 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 789124 * (2 : ZMod 50503979) ^ 789124) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 20822643 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 50503979) ^ 3156498 = 44336843 := by
        calc
          (2 : ZMod 50503979) ^ 3156498 = (2 : ZMod 50503979) ^ (1578249 + 1578249) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 1578249 * (2 : ZMod 50503979) ^ 1578249 := by rw [pow_add]
          _ = 44336843 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 50503979) ^ 6312997 = 9370373 := by
        calc
          (2 : ZMod 50503979) ^ 6312997 = (2 : ZMod 50503979) ^ (3156498 + 3156498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 3156498 * (2 : ZMod 50503979) ^ 3156498) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 9370373 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 50503979) ^ 12625994 = 45956742 := by
        calc
          (2 : ZMod 50503979) ^ 12625994 = (2 : ZMod 50503979) ^ (6312997 + 6312997) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 6312997 * (2 : ZMod 50503979) ^ 6312997 := by rw [pow_add]
          _ = 45956742 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 50503979) ^ 25251989 = 50503978 := by
        calc
          (2 : ZMod 50503979) ^ 25251989 = (2 : ZMod 50503979) ^ (12625994 + 12625994 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 12625994 * (2 : ZMod 50503979) ^ 12625994) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 50503978 := by rw [factor_0_23]; decide
      change (2 : ZMod 50503979) ^ 25251989 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 50503979) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 50503979) ^ 3 = 8 := by
        calc
          (2 : ZMod 50503979) ^ 3 = (2 : ZMod 50503979) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 1 * (2 : ZMod 50503979) ^ 1) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 50503979) ^ 6 = 64 := by
        calc
          (2 : ZMod 50503979) ^ 6 = (2 : ZMod 50503979) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 3 * (2 : ZMod 50503979) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 50503979) ^ 13 = 8192 := by
        calc
          (2 : ZMod 50503979) ^ 13 = (2 : ZMod 50503979) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 6 * (2 : ZMod 50503979) ^ 6) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 50503979) ^ 27 = 33209770 := by
        calc
          (2 : ZMod 50503979) ^ 27 = (2 : ZMod 50503979) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 13 * (2 : ZMod 50503979) ^ 13) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 33209770 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 50503979) ^ 55 = 791604 := by
        calc
          (2 : ZMod 50503979) ^ 55 = (2 : ZMod 50503979) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 27 * (2 : ZMod 50503979) ^ 27) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 791604 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 50503979) ^ 110 = 34025363 := by
        calc
          (2 : ZMod 50503979) ^ 110 = (2 : ZMod 50503979) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 55 * (2 : ZMod 50503979) ^ 55 := by rw [pow_add]
          _ = 34025363 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 50503979) ^ 220 = 41386156 := by
        calc
          (2 : ZMod 50503979) ^ 220 = (2 : ZMod 50503979) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 110 * (2 : ZMod 50503979) ^ 110 := by rw [pow_add]
          _ = 41386156 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 50503979) ^ 440 = 45923450 := by
        calc
          (2 : ZMod 50503979) ^ 440 = (2 : ZMod 50503979) ^ (220 + 220) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 220 * (2 : ZMod 50503979) ^ 220 := by rw [pow_add]
          _ = 45923450 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 50503979) ^ 880 = 24396018 := by
        calc
          (2 : ZMod 50503979) ^ 880 = (2 : ZMod 50503979) ^ (440 + 440) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 440 * (2 : ZMod 50503979) ^ 440 := by rw [pow_add]
          _ = 24396018 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 50503979) ^ 1761 = 26718929 := by
        calc
          (2 : ZMod 50503979) ^ 1761 = (2 : ZMod 50503979) ^ (880 + 880 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 880 * (2 : ZMod 50503979) ^ 880) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 26718929 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 50503979) ^ 3522 = 81444 := by
        calc
          (2 : ZMod 50503979) ^ 3522 = (2 : ZMod 50503979) ^ (1761 + 1761) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 1761 * (2 : ZMod 50503979) ^ 1761 := by rw [pow_add]
          _ = 81444 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 50503979) ^ 7045 = 34207774 := by
        calc
          (2 : ZMod 50503979) ^ 7045 = (2 : ZMod 50503979) ^ (3522 + 3522 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 3522 * (2 : ZMod 50503979) ^ 3522) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 34207774 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 50503979) ^ 14091 = 25061658 := by
        calc
          (2 : ZMod 50503979) ^ 14091 = (2 : ZMod 50503979) ^ (7045 + 7045 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 7045 * (2 : ZMod 50503979) ^ 7045) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 25061658 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 50503979) ^ 28183 = 4201909 := by
        calc
          (2 : ZMod 50503979) ^ 28183 = (2 : ZMod 50503979) ^ (14091 + 14091 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 14091 * (2 : ZMod 50503979) ^ 14091) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 4201909 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 50503979) ^ 56366 = 50201797 := by
        calc
          (2 : ZMod 50503979) ^ 56366 = (2 : ZMod 50503979) ^ (28183 + 28183) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 28183 * (2 : ZMod 50503979) ^ 28183 := by rw [pow_add]
          _ = 50201797 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 50503979) ^ 112732 = 2767092 := by
        calc
          (2 : ZMod 50503979) ^ 112732 = (2 : ZMod 50503979) ^ (56366 + 56366) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 56366 * (2 : ZMod 50503979) ^ 56366 := by rw [pow_add]
          _ = 2767092 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 50503979) ^ 225464 = 41392211 := by
        calc
          (2 : ZMod 50503979) ^ 225464 = (2 : ZMod 50503979) ^ (112732 + 112732) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 112732 * (2 : ZMod 50503979) ^ 112732 := by rw [pow_add]
          _ = 41392211 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 50503979) ^ 450928 = 16944060 := by
        calc
          (2 : ZMod 50503979) ^ 450928 = (2 : ZMod 50503979) ^ (225464 + 225464) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 225464 * (2 : ZMod 50503979) ^ 225464 := by rw [pow_add]
          _ = 16944060 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 50503979) ^ 901856 = 38270783 := by
        calc
          (2 : ZMod 50503979) ^ 901856 = (2 : ZMod 50503979) ^ (450928 + 450928) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 450928 * (2 : ZMod 50503979) ^ 450928 := by rw [pow_add]
          _ = 38270783 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 50503979) ^ 1803713 = 33969300 := by
        calc
          (2 : ZMod 50503979) ^ 1803713 = (2 : ZMod 50503979) ^ (901856 + 901856 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 901856 * (2 : ZMod 50503979) ^ 901856) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 33969300 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 50503979) ^ 3607427 = 42346677 := by
        calc
          (2 : ZMod 50503979) ^ 3607427 = (2 : ZMod 50503979) ^ (1803713 + 1803713 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 1803713 * (2 : ZMod 50503979) ^ 1803713) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 42346677 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 50503979) ^ 7214854 = 7883775 := by
        calc
          (2 : ZMod 50503979) ^ 7214854 = (2 : ZMod 50503979) ^ (3607427 + 3607427) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 3607427 * (2 : ZMod 50503979) ^ 3607427 := by rw [pow_add]
          _ = 7883775 := by rw [factor_1_21]; decide
      change (2 : ZMod 50503979) ^ 7214854 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (2 : ZMod 50503979) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 50503979) ^ 2 = 4 := by
        calc
          (2 : ZMod 50503979) ^ 2 = (2 : ZMod 50503979) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 1 * (2 : ZMod 50503979) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 50503979) ^ 4 = 16 := by
        calc
          (2 : ZMod 50503979) ^ 4 = (2 : ZMod 50503979) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 2 * (2 : ZMod 50503979) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 50503979) ^ 9 = 512 := by
        calc
          (2 : ZMod 50503979) ^ 9 = (2 : ZMod 50503979) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 4 * (2 : ZMod 50503979) ^ 4) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 50503979) ^ 19 = 524288 := by
        calc
          (2 : ZMod 50503979) ^ 19 = (2 : ZMod 50503979) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 9 * (2 : ZMod 50503979) ^ 9) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 50503979) ^ 39 = 20002473 := by
        calc
          (2 : ZMod 50503979) ^ 39 = (2 : ZMod 50503979) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 19 * (2 : ZMod 50503979) ^ 19) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 20002473 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 50503979) ^ 78 = 40976375 := by
        calc
          (2 : ZMod 50503979) ^ 78 = (2 : ZMod 50503979) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 39 * (2 : ZMod 50503979) ^ 39 := by rw [pow_add]
          _ = 40976375 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 50503979) ^ 156 = 42677943 := by
        calc
          (2 : ZMod 50503979) ^ 156 = (2 : ZMod 50503979) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 78 * (2 : ZMod 50503979) ^ 78 := by rw [pow_add]
          _ = 42677943 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 50503979) ^ 312 = 7588269 := by
        calc
          (2 : ZMod 50503979) ^ 312 = (2 : ZMod 50503979) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 156 * (2 : ZMod 50503979) ^ 156 := by rw [pow_add]
          _ = 7588269 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 50503979) ^ 625 = 35566770 := by
        calc
          (2 : ZMod 50503979) ^ 625 = (2 : ZMod 50503979) ^ (312 + 312 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 312 * (2 : ZMod 50503979) ^ 312) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 35566770 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 50503979) ^ 1250 = 47493014 := by
        calc
          (2 : ZMod 50503979) ^ 1250 = (2 : ZMod 50503979) ^ (625 + 625) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 625 * (2 : ZMod 50503979) ^ 625 := by rw [pow_add]
          _ = 47493014 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 50503979) ^ 2501 = 33433807 := by
        calc
          (2 : ZMod 50503979) ^ 2501 = (2 : ZMod 50503979) ^ (1250 + 1250 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 1250 * (2 : ZMod 50503979) ^ 1250) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 33433807 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 50503979) ^ 5002 = 35136423 := by
        calc
          (2 : ZMod 50503979) ^ 5002 = (2 : ZMod 50503979) ^ (2501 + 2501) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 2501 * (2 : ZMod 50503979) ^ 2501 := by rw [pow_add]
          _ = 35136423 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 50503979) ^ 10004 = 20203278 := by
        calc
          (2 : ZMod 50503979) ^ 10004 = (2 : ZMod 50503979) ^ (5002 + 5002) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 5002 * (2 : ZMod 50503979) ^ 5002 := by rw [pow_add]
          _ = 20203278 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 50503979) ^ 20009 = 31949959 := by
        calc
          (2 : ZMod 50503979) ^ 20009 = (2 : ZMod 50503979) ^ (10004 + 10004 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 10004 * (2 : ZMod 50503979) ^ 10004) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 31949959 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 50503979) ^ 40019 = 44990534 := by
        calc
          (2 : ZMod 50503979) ^ 40019 = (2 : ZMod 50503979) ^ (20009 + 20009 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 20009 * (2 : ZMod 50503979) ^ 20009) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 44990534 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 50503979) ^ 80038 = 33831799 := by
        calc
          (2 : ZMod 50503979) ^ 80038 = (2 : ZMod 50503979) ^ (40019 + 40019) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 40019 * (2 : ZMod 50503979) ^ 40019 := by rw [pow_add]
          _ = 33831799 := by rw [factor_2_15]; decide
      change (2 : ZMod 50503979) ^ 80038 ≠ 1
      rw [factor_2_16]
      decide
    ·
      have factor_3_0 : (2 : ZMod 50503979) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 50503979) ^ 2 = 4 := by
        calc
          (2 : ZMod 50503979) ^ 2 = (2 : ZMod 50503979) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 1 * (2 : ZMod 50503979) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 50503979) ^ 4 = 16 := by
        calc
          (2 : ZMod 50503979) ^ 4 = (2 : ZMod 50503979) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 2 * (2 : ZMod 50503979) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 50503979) ^ 8 = 256 := by
        calc
          (2 : ZMod 50503979) ^ 8 = (2 : ZMod 50503979) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 4 * (2 : ZMod 50503979) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 50503979) ^ 17 = 131072 := by
        calc
          (2 : ZMod 50503979) ^ 17 = (2 : ZMod 50503979) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 8 * (2 : ZMod 50503979) ^ 8) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 50503979) ^ 34 = 8516324 := by
        calc
          (2 : ZMod 50503979) ^ 34 = (2 : ZMod 50503979) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 17 * (2 : ZMod 50503979) ^ 17 := by rw [pow_add]
          _ = 8516324 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 50503979) ^ 69 = 40621312 := by
        calc
          (2 : ZMod 50503979) ^ 69 = (2 : ZMod 50503979) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 34 * (2 : ZMod 50503979) ^ 34) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 40621312 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 50503979) ^ 138 = 37747718 := by
        calc
          (2 : ZMod 50503979) ^ 138 = (2 : ZMod 50503979) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 69 * (2 : ZMod 50503979) ^ 69 := by rw [pow_add]
          _ = 37747718 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 50503979) ^ 276 = 40993428 := by
        calc
          (2 : ZMod 50503979) ^ 276 = (2 : ZMod 50503979) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 138 * (2 : ZMod 50503979) ^ 138 := by rw [pow_add]
          _ = 40993428 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 50503979) ^ 552 = 24597740 := by
        calc
          (2 : ZMod 50503979) ^ 552 = (2 : ZMod 50503979) ^ (276 + 276) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 276 * (2 : ZMod 50503979) ^ 276 := by rw [pow_add]
          _ = 24597740 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 50503979) ^ 1104 = 33812220 := by
        calc
          (2 : ZMod 50503979) ^ 1104 = (2 : ZMod 50503979) ^ (552 + 552) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 552 * (2 : ZMod 50503979) ^ 552 := by rw [pow_add]
          _ = 33812220 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 50503979) ^ 2208 = 22604571 := by
        calc
          (2 : ZMod 50503979) ^ 2208 = (2 : ZMod 50503979) ^ (1104 + 1104) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 1104 * (2 : ZMod 50503979) ^ 1104 := by rw [pow_add]
          _ = 22604571 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 50503979) ^ 4417 = 42788929 := by
        calc
          (2 : ZMod 50503979) ^ 4417 = (2 : ZMod 50503979) ^ (2208 + 2208 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = ((2 : ZMod 50503979) ^ 2208 * (2 : ZMod 50503979) ^ 2208) * (2 : ZMod 50503979) := by rw [pow_succ, pow_add]
          _ = 42788929 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 50503979) ^ 8834 = 27012260 := by
        calc
          (2 : ZMod 50503979) ^ 8834 = (2 : ZMod 50503979) ^ (4417 + 4417) :=
            congrArg (fun n : ℕ => (2 : ZMod 50503979) ^ n) (by norm_num)
          _ = (2 : ZMod 50503979) ^ 4417 * (2 : ZMod 50503979) ^ 4417 := by rw [pow_add]
          _ = 27012260 := by rw [factor_3_12]; decide
      change (2 : ZMod 50503979) ^ 8834 ≠ 1
      rw [factor_3_13]
      decide

#print axioms prime_lucas_50503979

end TotientTailPeriodKiller
end Erdos249257
