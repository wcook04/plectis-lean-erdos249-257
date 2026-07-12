import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_45293161 : Nat.Prime 45293161 := by
  apply lucas_primality 45293161 (23 : ZMod 45293161)
  ·
      have fermat_0 : (23 : ZMod 45293161) ^ 1 = 23 := by norm_num
      have fermat_1 : (23 : ZMod 45293161) ^ 2 = 529 := by
        calc
          (23 : ZMod 45293161) ^ 2 = (23 : ZMod 45293161) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1 * (23 : ZMod 45293161) ^ 1 := by rw [pow_add]
          _ = 529 := by rw [fermat_0]; decide
      have fermat_2 : (23 : ZMod 45293161) ^ 5 = 6436343 := by
        calc
          (23 : ZMod 45293161) ^ 5 = (23 : ZMod 45293161) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 2 * (23 : ZMod 45293161) ^ 2) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 6436343 := by rw [fermat_1]; decide
      have fermat_3 : (23 : ZMod 45293161) ^ 10 = 27368219 := by
        calc
          (23 : ZMod 45293161) ^ 10 = (23 : ZMod 45293161) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 5 * (23 : ZMod 45293161) ^ 5 := by rw [pow_add]
          _ = 27368219 := by rw [fermat_2]; decide
      have fermat_4 : (23 : ZMod 45293161) ^ 21 = 40171370 := by
        calc
          (23 : ZMod 45293161) ^ 21 = (23 : ZMod 45293161) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 10 * (23 : ZMod 45293161) ^ 10) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 40171370 := by rw [fermat_3]; decide
      have fermat_5 : (23 : ZMod 45293161) ^ 43 = 38946520 := by
        calc
          (23 : ZMod 45293161) ^ 43 = (23 : ZMod 45293161) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 21 * (23 : ZMod 45293161) ^ 21) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 38946520 := by rw [fermat_4]; decide
      have fermat_6 : (23 : ZMod 45293161) ^ 86 = 9801327 := by
        calc
          (23 : ZMod 45293161) ^ 86 = (23 : ZMod 45293161) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 43 * (23 : ZMod 45293161) ^ 43 := by rw [pow_add]
          _ = 9801327 := by rw [fermat_5]; decide
      have fermat_7 : (23 : ZMod 45293161) ^ 172 = 31756827 := by
        calc
          (23 : ZMod 45293161) ^ 172 = (23 : ZMod 45293161) ^ (86 + 86) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 86 * (23 : ZMod 45293161) ^ 86 := by rw [pow_add]
          _ = 31756827 := by rw [fermat_6]; decide
      have fermat_8 : (23 : ZMod 45293161) ^ 345 = 33302990 := by
        calc
          (23 : ZMod 45293161) ^ 345 = (23 : ZMod 45293161) ^ (172 + 172 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 172 * (23 : ZMod 45293161) ^ 172) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 33302990 := by rw [fermat_7]; decide
      have fermat_9 : (23 : ZMod 45293161) ^ 691 = 32961541 := by
        calc
          (23 : ZMod 45293161) ^ 691 = (23 : ZMod 45293161) ^ (345 + 345 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 345 * (23 : ZMod 45293161) ^ 345) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 32961541 := by rw [fermat_8]; decide
      have fermat_10 : (23 : ZMod 45293161) ^ 1382 = 7822365 := by
        calc
          (23 : ZMod 45293161) ^ 1382 = (23 : ZMod 45293161) ^ (691 + 691) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 691 * (23 : ZMod 45293161) ^ 691 := by rw [pow_add]
          _ = 7822365 := by rw [fermat_9]; decide
      have fermat_11 : (23 : ZMod 45293161) ^ 2764 = 9529182 := by
        calc
          (23 : ZMod 45293161) ^ 2764 = (23 : ZMod 45293161) ^ (1382 + 1382) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1382 * (23 : ZMod 45293161) ^ 1382 := by rw [pow_add]
          _ = 9529182 := by rw [fermat_10]; decide
      have fermat_12 : (23 : ZMod 45293161) ^ 5528 = 40448850 := by
        calc
          (23 : ZMod 45293161) ^ 5528 = (23 : ZMod 45293161) ^ (2764 + 2764) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 2764 * (23 : ZMod 45293161) ^ 2764 := by rw [pow_add]
          _ = 40448850 := by rw [fermat_11]; decide
      have fermat_13 : (23 : ZMod 45293161) ^ 11057 = 31001715 := by
        calc
          (23 : ZMod 45293161) ^ 11057 = (23 : ZMod 45293161) ^ (5528 + 5528 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 5528 * (23 : ZMod 45293161) ^ 5528) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 31001715 := by rw [fermat_12]; decide
      have fermat_14 : (23 : ZMod 45293161) ^ 22115 = 35275321 := by
        calc
          (23 : ZMod 45293161) ^ 22115 = (23 : ZMod 45293161) ^ (11057 + 11057 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 11057 * (23 : ZMod 45293161) ^ 11057) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 35275321 := by rw [fermat_13]; decide
      have fermat_15 : (23 : ZMod 45293161) ^ 44231 = 57921 := by
        calc
          (23 : ZMod 45293161) ^ 44231 = (23 : ZMod 45293161) ^ (22115 + 22115 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 22115 * (23 : ZMod 45293161) ^ 22115) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 57921 := by rw [fermat_14]; decide
      have fermat_16 : (23 : ZMod 45293161) ^ 88463 = 27118360 := by
        calc
          (23 : ZMod 45293161) ^ 88463 = (23 : ZMod 45293161) ^ (44231 + 44231 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 44231 * (23 : ZMod 45293161) ^ 44231) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 27118360 := by rw [fermat_15]; decide
      have fermat_17 : (23 : ZMod 45293161) ^ 176926 = 5871313 := by
        calc
          (23 : ZMod 45293161) ^ 176926 = (23 : ZMod 45293161) ^ (88463 + 88463) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 88463 * (23 : ZMod 45293161) ^ 88463 := by rw [pow_add]
          _ = 5871313 := by rw [fermat_16]; decide
      have fermat_18 : (23 : ZMod 45293161) ^ 353852 = 8558996 := by
        calc
          (23 : ZMod 45293161) ^ 353852 = (23 : ZMod 45293161) ^ (176926 + 176926) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 176926 * (23 : ZMod 45293161) ^ 176926 := by rw [pow_add]
          _ = 8558996 := by rw [fermat_17]; decide
      have fermat_19 : (23 : ZMod 45293161) ^ 707705 = 6420187 := by
        calc
          (23 : ZMod 45293161) ^ 707705 = (23 : ZMod 45293161) ^ (353852 + 353852 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 353852 * (23 : ZMod 45293161) ^ 353852) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 6420187 := by rw [fermat_18]; decide
      have fermat_20 : (23 : ZMod 45293161) ^ 1415411 = 4544779 := by
        calc
          (23 : ZMod 45293161) ^ 1415411 = (23 : ZMod 45293161) ^ (707705 + 707705 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 707705 * (23 : ZMod 45293161) ^ 707705) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 4544779 := by rw [fermat_19]; decide
      have fermat_21 : (23 : ZMod 45293161) ^ 2830822 = 21241172 := by
        calc
          (23 : ZMod 45293161) ^ 2830822 = (23 : ZMod 45293161) ^ (1415411 + 1415411) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1415411 * (23 : ZMod 45293161) ^ 1415411 := by rw [pow_add]
          _ = 21241172 := by rw [fermat_20]; decide
      have fermat_22 : (23 : ZMod 45293161) ^ 5661645 = 41619674 := by
        calc
          (23 : ZMod 45293161) ^ 5661645 = (23 : ZMod 45293161) ^ (2830822 + 2830822 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 2830822 * (23 : ZMod 45293161) ^ 2830822) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 41619674 := by rw [fermat_21]; decide
      have fermat_23 : (23 : ZMod 45293161) ^ 11323290 = 43523473 := by
        calc
          (23 : ZMod 45293161) ^ 11323290 = (23 : ZMod 45293161) ^ (5661645 + 5661645) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 5661645 * (23 : ZMod 45293161) ^ 5661645 := by rw [pow_add]
          _ = 43523473 := by rw [fermat_22]; decide
      have fermat_24 : (23 : ZMod 45293161) ^ 22646580 = 45293160 := by
        calc
          (23 : ZMod 45293161) ^ 22646580 = (23 : ZMod 45293161) ^ (11323290 + 11323290) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 11323290 * (23 : ZMod 45293161) ^ 11323290 := by rw [pow_add]
          _ = 45293160 := by rw [fermat_23]; decide
      have fermat_25 : (23 : ZMod 45293161) ^ 45293160 = 1 := by
        calc
          (23 : ZMod 45293161) ^ 45293160 = (23 : ZMod 45293161) ^ (22646580 + 22646580) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 22646580 * (23 : ZMod 45293161) ^ 22646580 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (11, 1), (34313, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (11, 1), (34313, 1)] : List FactorBlock).map factorBlockValue).prod = 45293161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (23 : ZMod 45293161) ^ 1 = 23 := by norm_num
      have factor_0_1 : (23 : ZMod 45293161) ^ 2 = 529 := by
        calc
          (23 : ZMod 45293161) ^ 2 = (23 : ZMod 45293161) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1 * (23 : ZMod 45293161) ^ 1 := by rw [pow_add]
          _ = 529 := by rw [factor_0_0]; decide
      have factor_0_2 : (23 : ZMod 45293161) ^ 5 = 6436343 := by
        calc
          (23 : ZMod 45293161) ^ 5 = (23 : ZMod 45293161) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 2 * (23 : ZMod 45293161) ^ 2) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 6436343 := by rw [factor_0_1]; decide
      have factor_0_3 : (23 : ZMod 45293161) ^ 10 = 27368219 := by
        calc
          (23 : ZMod 45293161) ^ 10 = (23 : ZMod 45293161) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 5 * (23 : ZMod 45293161) ^ 5 := by rw [pow_add]
          _ = 27368219 := by rw [factor_0_2]; decide
      have factor_0_4 : (23 : ZMod 45293161) ^ 21 = 40171370 := by
        calc
          (23 : ZMod 45293161) ^ 21 = (23 : ZMod 45293161) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 10 * (23 : ZMod 45293161) ^ 10) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 40171370 := by rw [factor_0_3]; decide
      have factor_0_5 : (23 : ZMod 45293161) ^ 43 = 38946520 := by
        calc
          (23 : ZMod 45293161) ^ 43 = (23 : ZMod 45293161) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 21 * (23 : ZMod 45293161) ^ 21) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 38946520 := by rw [factor_0_4]; decide
      have factor_0_6 : (23 : ZMod 45293161) ^ 86 = 9801327 := by
        calc
          (23 : ZMod 45293161) ^ 86 = (23 : ZMod 45293161) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 43 * (23 : ZMod 45293161) ^ 43 := by rw [pow_add]
          _ = 9801327 := by rw [factor_0_5]; decide
      have factor_0_7 : (23 : ZMod 45293161) ^ 172 = 31756827 := by
        calc
          (23 : ZMod 45293161) ^ 172 = (23 : ZMod 45293161) ^ (86 + 86) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 86 * (23 : ZMod 45293161) ^ 86 := by rw [pow_add]
          _ = 31756827 := by rw [factor_0_6]; decide
      have factor_0_8 : (23 : ZMod 45293161) ^ 345 = 33302990 := by
        calc
          (23 : ZMod 45293161) ^ 345 = (23 : ZMod 45293161) ^ (172 + 172 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 172 * (23 : ZMod 45293161) ^ 172) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 33302990 := by rw [factor_0_7]; decide
      have factor_0_9 : (23 : ZMod 45293161) ^ 691 = 32961541 := by
        calc
          (23 : ZMod 45293161) ^ 691 = (23 : ZMod 45293161) ^ (345 + 345 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 345 * (23 : ZMod 45293161) ^ 345) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 32961541 := by rw [factor_0_8]; decide
      have factor_0_10 : (23 : ZMod 45293161) ^ 1382 = 7822365 := by
        calc
          (23 : ZMod 45293161) ^ 1382 = (23 : ZMod 45293161) ^ (691 + 691) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 691 * (23 : ZMod 45293161) ^ 691 := by rw [pow_add]
          _ = 7822365 := by rw [factor_0_9]; decide
      have factor_0_11 : (23 : ZMod 45293161) ^ 2764 = 9529182 := by
        calc
          (23 : ZMod 45293161) ^ 2764 = (23 : ZMod 45293161) ^ (1382 + 1382) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1382 * (23 : ZMod 45293161) ^ 1382 := by rw [pow_add]
          _ = 9529182 := by rw [factor_0_10]; decide
      have factor_0_12 : (23 : ZMod 45293161) ^ 5528 = 40448850 := by
        calc
          (23 : ZMod 45293161) ^ 5528 = (23 : ZMod 45293161) ^ (2764 + 2764) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 2764 * (23 : ZMod 45293161) ^ 2764 := by rw [pow_add]
          _ = 40448850 := by rw [factor_0_11]; decide
      have factor_0_13 : (23 : ZMod 45293161) ^ 11057 = 31001715 := by
        calc
          (23 : ZMod 45293161) ^ 11057 = (23 : ZMod 45293161) ^ (5528 + 5528 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 5528 * (23 : ZMod 45293161) ^ 5528) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 31001715 := by rw [factor_0_12]; decide
      have factor_0_14 : (23 : ZMod 45293161) ^ 22115 = 35275321 := by
        calc
          (23 : ZMod 45293161) ^ 22115 = (23 : ZMod 45293161) ^ (11057 + 11057 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 11057 * (23 : ZMod 45293161) ^ 11057) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 35275321 := by rw [factor_0_13]; decide
      have factor_0_15 : (23 : ZMod 45293161) ^ 44231 = 57921 := by
        calc
          (23 : ZMod 45293161) ^ 44231 = (23 : ZMod 45293161) ^ (22115 + 22115 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 22115 * (23 : ZMod 45293161) ^ 22115) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 57921 := by rw [factor_0_14]; decide
      have factor_0_16 : (23 : ZMod 45293161) ^ 88463 = 27118360 := by
        calc
          (23 : ZMod 45293161) ^ 88463 = (23 : ZMod 45293161) ^ (44231 + 44231 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 44231 * (23 : ZMod 45293161) ^ 44231) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 27118360 := by rw [factor_0_15]; decide
      have factor_0_17 : (23 : ZMod 45293161) ^ 176926 = 5871313 := by
        calc
          (23 : ZMod 45293161) ^ 176926 = (23 : ZMod 45293161) ^ (88463 + 88463) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 88463 * (23 : ZMod 45293161) ^ 88463 := by rw [pow_add]
          _ = 5871313 := by rw [factor_0_16]; decide
      have factor_0_18 : (23 : ZMod 45293161) ^ 353852 = 8558996 := by
        calc
          (23 : ZMod 45293161) ^ 353852 = (23 : ZMod 45293161) ^ (176926 + 176926) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 176926 * (23 : ZMod 45293161) ^ 176926 := by rw [pow_add]
          _ = 8558996 := by rw [factor_0_17]; decide
      have factor_0_19 : (23 : ZMod 45293161) ^ 707705 = 6420187 := by
        calc
          (23 : ZMod 45293161) ^ 707705 = (23 : ZMod 45293161) ^ (353852 + 353852 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 353852 * (23 : ZMod 45293161) ^ 353852) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 6420187 := by rw [factor_0_18]; decide
      have factor_0_20 : (23 : ZMod 45293161) ^ 1415411 = 4544779 := by
        calc
          (23 : ZMod 45293161) ^ 1415411 = (23 : ZMod 45293161) ^ (707705 + 707705 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 707705 * (23 : ZMod 45293161) ^ 707705) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 4544779 := by rw [factor_0_19]; decide
      have factor_0_21 : (23 : ZMod 45293161) ^ 2830822 = 21241172 := by
        calc
          (23 : ZMod 45293161) ^ 2830822 = (23 : ZMod 45293161) ^ (1415411 + 1415411) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1415411 * (23 : ZMod 45293161) ^ 1415411 := by rw [pow_add]
          _ = 21241172 := by rw [factor_0_20]; decide
      have factor_0_22 : (23 : ZMod 45293161) ^ 5661645 = 41619674 := by
        calc
          (23 : ZMod 45293161) ^ 5661645 = (23 : ZMod 45293161) ^ (2830822 + 2830822 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 2830822 * (23 : ZMod 45293161) ^ 2830822) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 41619674 := by rw [factor_0_21]; decide
      have factor_0_23 : (23 : ZMod 45293161) ^ 11323290 = 43523473 := by
        calc
          (23 : ZMod 45293161) ^ 11323290 = (23 : ZMod 45293161) ^ (5661645 + 5661645) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 5661645 * (23 : ZMod 45293161) ^ 5661645 := by rw [pow_add]
          _ = 43523473 := by rw [factor_0_22]; decide
      have factor_0_24 : (23 : ZMod 45293161) ^ 22646580 = 45293160 := by
        calc
          (23 : ZMod 45293161) ^ 22646580 = (23 : ZMod 45293161) ^ (11323290 + 11323290) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 11323290 * (23 : ZMod 45293161) ^ 11323290 := by rw [pow_add]
          _ = 45293160 := by rw [factor_0_23]; decide
      change (23 : ZMod 45293161) ^ 22646580 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (23 : ZMod 45293161) ^ 1 = 23 := by norm_num
      have factor_1_1 : (23 : ZMod 45293161) ^ 3 = 12167 := by
        calc
          (23 : ZMod 45293161) ^ 3 = (23 : ZMod 45293161) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 1 * (23 : ZMod 45293161) ^ 1) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 12167 := by rw [factor_1_0]; decide
      have factor_1_2 : (23 : ZMod 45293161) ^ 7 = 7838372 := by
        calc
          (23 : ZMod 45293161) ^ 7 = (23 : ZMod 45293161) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 3 * (23 : ZMod 45293161) ^ 3) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 7838372 := by rw [factor_1_1]; decide
      have factor_1_3 : (23 : ZMod 45293161) ^ 14 = 38593367 := by
        calc
          (23 : ZMod 45293161) ^ 14 = (23 : ZMod 45293161) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 7 * (23 : ZMod 45293161) ^ 7 := by rw [pow_add]
          _ = 38593367 := by rw [factor_1_2]; decide
      have factor_1_4 : (23 : ZMod 45293161) ^ 28 = 41244479 := by
        calc
          (23 : ZMod 45293161) ^ 28 = (23 : ZMod 45293161) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 14 * (23 : ZMod 45293161) ^ 14 := by rw [pow_add]
          _ = 41244479 := by rw [factor_1_3]; decide
      have factor_1_5 : (23 : ZMod 45293161) ^ 57 = 13038315 := by
        calc
          (23 : ZMod 45293161) ^ 57 = (23 : ZMod 45293161) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 28 * (23 : ZMod 45293161) ^ 28) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 13038315 := by rw [factor_1_4]; decide
      have factor_1_6 : (23 : ZMod 45293161) ^ 115 = 15990426 := by
        calc
          (23 : ZMod 45293161) ^ 115 = (23 : ZMod 45293161) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 57 * (23 : ZMod 45293161) ^ 57) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 15990426 := by rw [factor_1_5]; decide
      have factor_1_7 : (23 : ZMod 45293161) ^ 230 = 15402371 := by
        calc
          (23 : ZMod 45293161) ^ 230 = (23 : ZMod 45293161) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 115 * (23 : ZMod 45293161) ^ 115 := by rw [pow_add]
          _ = 15402371 := by rw [factor_1_6]; decide
      have factor_1_8 : (23 : ZMod 45293161) ^ 460 = 1309238 := by
        calc
          (23 : ZMod 45293161) ^ 460 = (23 : ZMod 45293161) ^ (230 + 230) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 230 * (23 : ZMod 45293161) ^ 230 := by rw [pow_add]
          _ = 1309238 := by rw [factor_1_7]; decide
      have factor_1_9 : (23 : ZMod 45293161) ^ 921 = 4985065 := by
        calc
          (23 : ZMod 45293161) ^ 921 = (23 : ZMod 45293161) ^ (460 + 460 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 460 * (23 : ZMod 45293161) ^ 460) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 4985065 := by rw [factor_1_8]; decide
      have factor_1_10 : (23 : ZMod 45293161) ^ 1842 = 10287838 := by
        calc
          (23 : ZMod 45293161) ^ 1842 = (23 : ZMod 45293161) ^ (921 + 921) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 921 * (23 : ZMod 45293161) ^ 921 := by rw [pow_add]
          _ = 10287838 := by rw [factor_1_9]; decide
      have factor_1_11 : (23 : ZMod 45293161) ^ 3685 = 33823708 := by
        calc
          (23 : ZMod 45293161) ^ 3685 = (23 : ZMod 45293161) ^ (1842 + 1842 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 1842 * (23 : ZMod 45293161) ^ 1842) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 33823708 := by rw [factor_1_10]; decide
      have factor_1_12 : (23 : ZMod 45293161) ^ 7371 = 1611928 := by
        calc
          (23 : ZMod 45293161) ^ 7371 = (23 : ZMod 45293161) ^ (3685 + 3685 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 3685 * (23 : ZMod 45293161) ^ 3685) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 1611928 := by rw [factor_1_11]; decide
      have factor_1_13 : (23 : ZMod 45293161) ^ 14743 = 17757002 := by
        calc
          (23 : ZMod 45293161) ^ 14743 = (23 : ZMod 45293161) ^ (7371 + 7371 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 7371 * (23 : ZMod 45293161) ^ 7371) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 17757002 := by rw [factor_1_12]; decide
      have factor_1_14 : (23 : ZMod 45293161) ^ 29487 = 25059421 := by
        calc
          (23 : ZMod 45293161) ^ 29487 = (23 : ZMod 45293161) ^ (14743 + 14743 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 14743 * (23 : ZMod 45293161) ^ 14743) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 25059421 := by rw [factor_1_13]; decide
      have factor_1_15 : (23 : ZMod 45293161) ^ 58975 = 45240930 := by
        calc
          (23 : ZMod 45293161) ^ 58975 = (23 : ZMod 45293161) ^ (29487 + 29487 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 29487 * (23 : ZMod 45293161) ^ 29487) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 45240930 := by rw [factor_1_14]; decide
      have factor_1_16 : (23 : ZMod 45293161) ^ 117950 = 10487701 := by
        calc
          (23 : ZMod 45293161) ^ 117950 = (23 : ZMod 45293161) ^ (58975 + 58975) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 58975 * (23 : ZMod 45293161) ^ 58975 := by rw [pow_add]
          _ = 10487701 := by rw [factor_1_15]; decide
      have factor_1_17 : (23 : ZMod 45293161) ^ 235901 = 15443828 := by
        calc
          (23 : ZMod 45293161) ^ 235901 = (23 : ZMod 45293161) ^ (117950 + 117950 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 117950 * (23 : ZMod 45293161) ^ 117950) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 15443828 := by rw [factor_1_16]; decide
      have factor_1_18 : (23 : ZMod 45293161) ^ 471803 = 19035949 := by
        calc
          (23 : ZMod 45293161) ^ 471803 = (23 : ZMod 45293161) ^ (235901 + 235901 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 235901 * (23 : ZMod 45293161) ^ 235901) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 19035949 := by rw [factor_1_17]; decide
      have factor_1_19 : (23 : ZMod 45293161) ^ 943607 = 15734818 := by
        calc
          (23 : ZMod 45293161) ^ 943607 = (23 : ZMod 45293161) ^ (471803 + 471803 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 471803 * (23 : ZMod 45293161) ^ 471803) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 15734818 := by rw [factor_1_18]; decide
      have factor_1_20 : (23 : ZMod 45293161) ^ 1887215 = 44787439 := by
        calc
          (23 : ZMod 45293161) ^ 1887215 = (23 : ZMod 45293161) ^ (943607 + 943607 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 943607 * (23 : ZMod 45293161) ^ 943607) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 44787439 := by rw [factor_1_19]; decide
      have factor_1_21 : (23 : ZMod 45293161) ^ 3774430 = 29554278 := by
        calc
          (23 : ZMod 45293161) ^ 3774430 = (23 : ZMod 45293161) ^ (1887215 + 1887215) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1887215 * (23 : ZMod 45293161) ^ 1887215 := by rw [pow_add]
          _ = 29554278 := by rw [factor_1_20]; decide
      have factor_1_22 : (23 : ZMod 45293161) ^ 7548860 = 18901038 := by
        calc
          (23 : ZMod 45293161) ^ 7548860 = (23 : ZMod 45293161) ^ (3774430 + 3774430) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 3774430 * (23 : ZMod 45293161) ^ 3774430 := by rw [pow_add]
          _ = 18901038 := by rw [factor_1_21]; decide
      have factor_1_23 : (23 : ZMod 45293161) ^ 15097720 = 18901037 := by
        calc
          (23 : ZMod 45293161) ^ 15097720 = (23 : ZMod 45293161) ^ (7548860 + 7548860) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 7548860 * (23 : ZMod 45293161) ^ 7548860 := by rw [pow_add]
          _ = 18901037 := by rw [factor_1_22]; decide
      change (23 : ZMod 45293161) ^ 15097720 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (23 : ZMod 45293161) ^ 1 = 23 := by norm_num
      have factor_2_1 : (23 : ZMod 45293161) ^ 2 = 529 := by
        calc
          (23 : ZMod 45293161) ^ 2 = (23 : ZMod 45293161) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1 * (23 : ZMod 45293161) ^ 1 := by rw [pow_add]
          _ = 529 := by rw [factor_2_0]; decide
      have factor_2_2 : (23 : ZMod 45293161) ^ 4 = 279841 := by
        calc
          (23 : ZMod 45293161) ^ 4 = (23 : ZMod 45293161) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 2 * (23 : ZMod 45293161) ^ 2 := by rw [pow_add]
          _ = 279841 := by rw [factor_2_1]; decide
      have factor_2_3 : (23 : ZMod 45293161) ^ 8 = 44403073 := by
        calc
          (23 : ZMod 45293161) ^ 8 = (23 : ZMod 45293161) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 4 * (23 : ZMod 45293161) ^ 4 := by rw [pow_add]
          _ = 44403073 := by rw [factor_2_2]; decide
      have factor_2_4 : (23 : ZMod 45293161) ^ 17 = 11296202 := by
        calc
          (23 : ZMod 45293161) ^ 17 = (23 : ZMod 45293161) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 8 * (23 : ZMod 45293161) ^ 8) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 11296202 := by rw [factor_2_3]; decide
      have factor_2_5 : (23 : ZMod 45293161) ^ 34 = 28898470 := by
        calc
          (23 : ZMod 45293161) ^ 34 = (23 : ZMod 45293161) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 17 * (23 : ZMod 45293161) ^ 17 := by rw [pow_add]
          _ = 28898470 := by rw [factor_2_4]; decide
      have factor_2_6 : (23 : ZMod 45293161) ^ 69 = 36381559 := by
        calc
          (23 : ZMod 45293161) ^ 69 = (23 : ZMod 45293161) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 34 * (23 : ZMod 45293161) ^ 34) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 36381559 := by rw [factor_2_5]; decide
      have factor_2_7 : (23 : ZMod 45293161) ^ 138 = 29347453 := by
        calc
          (23 : ZMod 45293161) ^ 138 = (23 : ZMod 45293161) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 69 * (23 : ZMod 45293161) ^ 69 := by rw [pow_add]
          _ = 29347453 := by rw [factor_2_6]; decide
      have factor_2_8 : (23 : ZMod 45293161) ^ 276 = 34021650 := by
        calc
          (23 : ZMod 45293161) ^ 276 = (23 : ZMod 45293161) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 138 * (23 : ZMod 45293161) ^ 138 := by rw [pow_add]
          _ = 34021650 := by rw [factor_2_7]; decide
      have factor_2_9 : (23 : ZMod 45293161) ^ 552 = 5963409 := by
        calc
          (23 : ZMod 45293161) ^ 552 = (23 : ZMod 45293161) ^ (276 + 276) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 276 * (23 : ZMod 45293161) ^ 276 := by rw [pow_add]
          _ = 5963409 := by rw [factor_2_8]; decide
      have factor_2_10 : (23 : ZMod 45293161) ^ 1105 = 12683770 := by
        calc
          (23 : ZMod 45293161) ^ 1105 = (23 : ZMod 45293161) ^ (552 + 552 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 552 * (23 : ZMod 45293161) ^ 552) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 12683770 := by rw [factor_2_9]; decide
      have factor_2_11 : (23 : ZMod 45293161) ^ 2211 = 5726409 := by
        calc
          (23 : ZMod 45293161) ^ 2211 = (23 : ZMod 45293161) ^ (1105 + 1105 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 1105 * (23 : ZMod 45293161) ^ 1105) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 5726409 := by rw [factor_2_10]; decide
      have factor_2_12 : (23 : ZMod 45293161) ^ 4423 = 41836552 := by
        calc
          (23 : ZMod 45293161) ^ 4423 = (23 : ZMod 45293161) ^ (2211 + 2211 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 2211 * (23 : ZMod 45293161) ^ 2211) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 41836552 := by rw [factor_2_11]; decide
      have factor_2_13 : (23 : ZMod 45293161) ^ 8846 = 36372886 := by
        calc
          (23 : ZMod 45293161) ^ 8846 = (23 : ZMod 45293161) ^ (4423 + 4423) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 4423 * (23 : ZMod 45293161) ^ 4423 := by rw [pow_add]
          _ = 36372886 := by rw [factor_2_12]; decide
      have factor_2_14 : (23 : ZMod 45293161) ^ 17692 = 9071859 := by
        calc
          (23 : ZMod 45293161) ^ 17692 = (23 : ZMod 45293161) ^ (8846 + 8846) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 8846 * (23 : ZMod 45293161) ^ 8846 := by rw [pow_add]
          _ = 9071859 := by rw [factor_2_13]; decide
      have factor_2_15 : (23 : ZMod 45293161) ^ 35385 = 23517500 := by
        calc
          (23 : ZMod 45293161) ^ 35385 = (23 : ZMod 45293161) ^ (17692 + 17692 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 17692 * (23 : ZMod 45293161) ^ 17692) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 23517500 := by rw [factor_2_14]; decide
      have factor_2_16 : (23 : ZMod 45293161) ^ 70770 = 10178084 := by
        calc
          (23 : ZMod 45293161) ^ 70770 = (23 : ZMod 45293161) ^ (35385 + 35385) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 35385 * (23 : ZMod 45293161) ^ 35385 := by rw [pow_add]
          _ = 10178084 := by rw [factor_2_15]; decide
      have factor_2_17 : (23 : ZMod 45293161) ^ 141541 = 12047619 := by
        calc
          (23 : ZMod 45293161) ^ 141541 = (23 : ZMod 45293161) ^ (70770 + 70770 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 70770 * (23 : ZMod 45293161) ^ 70770) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 12047619 := by rw [factor_2_16]; decide
      have factor_2_18 : (23 : ZMod 45293161) ^ 283082 = 18623391 := by
        calc
          (23 : ZMod 45293161) ^ 283082 = (23 : ZMod 45293161) ^ (141541 + 141541) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 141541 * (23 : ZMod 45293161) ^ 141541 := by rw [pow_add]
          _ = 18623391 := by rw [factor_2_17]; decide
      have factor_2_19 : (23 : ZMod 45293161) ^ 566164 = 33121499 := by
        calc
          (23 : ZMod 45293161) ^ 566164 = (23 : ZMod 45293161) ^ (283082 + 283082) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 283082 * (23 : ZMod 45293161) ^ 283082 := by rw [pow_add]
          _ = 33121499 := by rw [factor_2_18]; decide
      have factor_2_20 : (23 : ZMod 45293161) ^ 1132329 = 18871615 := by
        calc
          (23 : ZMod 45293161) ^ 1132329 = (23 : ZMod 45293161) ^ (566164 + 566164 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 566164 * (23 : ZMod 45293161) ^ 566164) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 18871615 := by rw [factor_2_19]; decide
      have factor_2_21 : (23 : ZMod 45293161) ^ 2264658 = 37716436 := by
        calc
          (23 : ZMod 45293161) ^ 2264658 = (23 : ZMod 45293161) ^ (1132329 + 1132329) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1132329 * (23 : ZMod 45293161) ^ 1132329 := by rw [pow_add]
          _ = 37716436 := by rw [factor_2_20]; decide
      have factor_2_22 : (23 : ZMod 45293161) ^ 4529316 = 35402497 := by
        calc
          (23 : ZMod 45293161) ^ 4529316 = (23 : ZMod 45293161) ^ (2264658 + 2264658) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 2264658 * (23 : ZMod 45293161) ^ 2264658 := by rw [pow_add]
          _ = 35402497 := by rw [factor_2_21]; decide
      have factor_2_23 : (23 : ZMod 45293161) ^ 9058632 = 23490393 := by
        calc
          (23 : ZMod 45293161) ^ 9058632 = (23 : ZMod 45293161) ^ (4529316 + 4529316) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 4529316 * (23 : ZMod 45293161) ^ 4529316 := by rw [pow_add]
          _ = 23490393 := by rw [factor_2_22]; decide
      change (23 : ZMod 45293161) ^ 9058632 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (23 : ZMod 45293161) ^ 1 = 23 := by norm_num
      have factor_3_1 : (23 : ZMod 45293161) ^ 3 = 12167 := by
        calc
          (23 : ZMod 45293161) ^ 3 = (23 : ZMod 45293161) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 1 * (23 : ZMod 45293161) ^ 1) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 12167 := by rw [factor_3_0]; decide
      have factor_3_2 : (23 : ZMod 45293161) ^ 7 = 7838372 := by
        calc
          (23 : ZMod 45293161) ^ 7 = (23 : ZMod 45293161) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 3 * (23 : ZMod 45293161) ^ 3) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 7838372 := by rw [factor_3_1]; decide
      have factor_3_3 : (23 : ZMod 45293161) ^ 15 = 27077382 := by
        calc
          (23 : ZMod 45293161) ^ 15 = (23 : ZMod 45293161) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 7 * (23 : ZMod 45293161) ^ 7) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 27077382 := by rw [factor_3_2]; decide
      have factor_3_4 : (23 : ZMod 45293161) ^ 31 = 18645274 := by
        calc
          (23 : ZMod 45293161) ^ 31 = (23 : ZMod 45293161) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 15 * (23 : ZMod 45293161) ^ 15) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 18645274 := by rw [factor_3_3]; decide
      have factor_3_5 : (23 : ZMod 45293161) ^ 62 = 34660728 := by
        calc
          (23 : ZMod 45293161) ^ 62 = (23 : ZMod 45293161) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 31 * (23 : ZMod 45293161) ^ 31 := by rw [pow_add]
          _ = 34660728 := by rw [factor_3_4]; decide
      have factor_3_6 : (23 : ZMod 45293161) ^ 125 = 29235661 := by
        calc
          (23 : ZMod 45293161) ^ 125 = (23 : ZMod 45293161) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 62 * (23 : ZMod 45293161) ^ 62) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 29235661 := by rw [factor_3_5]; decide
      have factor_3_7 : (23 : ZMod 45293161) ^ 251 = 7451493 := by
        calc
          (23 : ZMod 45293161) ^ 251 = (23 : ZMod 45293161) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 125 * (23 : ZMod 45293161) ^ 125) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 7451493 := by rw [factor_3_6]; decide
      have factor_3_8 : (23 : ZMod 45293161) ^ 502 = 43031793 := by
        calc
          (23 : ZMod 45293161) ^ 502 = (23 : ZMod 45293161) ^ (251 + 251) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 251 * (23 : ZMod 45293161) ^ 251 := by rw [pow_add]
          _ = 43031793 := by rw [factor_3_7]; decide
      have factor_3_9 : (23 : ZMod 45293161) ^ 1005 = 6303757 := by
        calc
          (23 : ZMod 45293161) ^ 1005 = (23 : ZMod 45293161) ^ (502 + 502 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 502 * (23 : ZMod 45293161) ^ 502) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 6303757 := by rw [factor_3_8]; decide
      have factor_3_10 : (23 : ZMod 45293161) ^ 2010 = 31615953 := by
        calc
          (23 : ZMod 45293161) ^ 2010 = (23 : ZMod 45293161) ^ (1005 + 1005) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1005 * (23 : ZMod 45293161) ^ 1005 := by rw [pow_add]
          _ = 31615953 := by rw [factor_3_9]; decide
      have factor_3_11 : (23 : ZMod 45293161) ^ 4021 = 42814880 := by
        calc
          (23 : ZMod 45293161) ^ 4021 = (23 : ZMod 45293161) ^ (2010 + 2010 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 2010 * (23 : ZMod 45293161) ^ 2010) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 42814880 := by rw [factor_3_10]; decide
      have factor_3_12 : (23 : ZMod 45293161) ^ 8042 = 33497039 := by
        calc
          (23 : ZMod 45293161) ^ 8042 = (23 : ZMod 45293161) ^ (4021 + 4021) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 4021 * (23 : ZMod 45293161) ^ 4021 := by rw [pow_add]
          _ = 33497039 := by rw [factor_3_11]; decide
      have factor_3_13 : (23 : ZMod 45293161) ^ 16084 = 22636870 := by
        calc
          (23 : ZMod 45293161) ^ 16084 = (23 : ZMod 45293161) ^ (8042 + 8042) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 8042 * (23 : ZMod 45293161) ^ 8042 := by rw [pow_add]
          _ = 22636870 := by rw [factor_3_12]; decide
      have factor_3_14 : (23 : ZMod 45293161) ^ 32168 = 37677359 := by
        calc
          (23 : ZMod 45293161) ^ 32168 = (23 : ZMod 45293161) ^ (16084 + 16084) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 16084 * (23 : ZMod 45293161) ^ 16084 := by rw [pow_add]
          _ = 37677359 := by rw [factor_3_13]; decide
      have factor_3_15 : (23 : ZMod 45293161) ^ 64336 = 11025688 := by
        calc
          (23 : ZMod 45293161) ^ 64336 = (23 : ZMod 45293161) ^ (32168 + 32168) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 32168 * (23 : ZMod 45293161) ^ 32168 := by rw [pow_add]
          _ = 11025688 := by rw [factor_3_14]; decide
      have factor_3_16 : (23 : ZMod 45293161) ^ 128673 = 31489725 := by
        calc
          (23 : ZMod 45293161) ^ 128673 = (23 : ZMod 45293161) ^ (64336 + 64336 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 64336 * (23 : ZMod 45293161) ^ 64336) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 31489725 := by rw [factor_3_15]; decide
      have factor_3_17 : (23 : ZMod 45293161) ^ 257347 = 15092575 := by
        calc
          (23 : ZMod 45293161) ^ 257347 = (23 : ZMod 45293161) ^ (128673 + 128673 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 128673 * (23 : ZMod 45293161) ^ 128673) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 15092575 := by rw [factor_3_16]; decide
      have factor_3_18 : (23 : ZMod 45293161) ^ 514695 = 25133948 := by
        calc
          (23 : ZMod 45293161) ^ 514695 = (23 : ZMod 45293161) ^ (257347 + 257347 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 257347 * (23 : ZMod 45293161) ^ 257347) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 25133948 := by rw [factor_3_17]; decide
      have factor_3_19 : (23 : ZMod 45293161) ^ 1029390 = 30550488 := by
        calc
          (23 : ZMod 45293161) ^ 1029390 = (23 : ZMod 45293161) ^ (514695 + 514695) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 514695 * (23 : ZMod 45293161) ^ 514695 := by rw [pow_add]
          _ = 30550488 := by rw [factor_3_18]; decide
      have factor_3_20 : (23 : ZMod 45293161) ^ 2058780 = 17806991 := by
        calc
          (23 : ZMod 45293161) ^ 2058780 = (23 : ZMod 45293161) ^ (1029390 + 1029390) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1029390 * (23 : ZMod 45293161) ^ 1029390 := by rw [pow_add]
          _ = 17806991 := by rw [factor_3_19]; decide
      have factor_3_21 : (23 : ZMod 45293161) ^ 4117560 = 23427349 := by
        calc
          (23 : ZMod 45293161) ^ 4117560 = (23 : ZMod 45293161) ^ (2058780 + 2058780) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 2058780 * (23 : ZMod 45293161) ^ 2058780 := by rw [pow_add]
          _ = 23427349 := by rw [factor_3_20]; decide
      change (23 : ZMod 45293161) ^ 4117560 ≠ 1
      rw [factor_3_21]
      decide
    ·
      have factor_4_0 : (23 : ZMod 45293161) ^ 1 = 23 := by norm_num
      have factor_4_1 : (23 : ZMod 45293161) ^ 2 = 529 := by
        calc
          (23 : ZMod 45293161) ^ 2 = (23 : ZMod 45293161) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 1 * (23 : ZMod 45293161) ^ 1 := by rw [pow_add]
          _ = 529 := by rw [factor_4_0]; decide
      have factor_4_2 : (23 : ZMod 45293161) ^ 5 = 6436343 := by
        calc
          (23 : ZMod 45293161) ^ 5 = (23 : ZMod 45293161) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 2 * (23 : ZMod 45293161) ^ 2) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 6436343 := by rw [factor_4_1]; decide
      have factor_4_3 : (23 : ZMod 45293161) ^ 10 = 27368219 := by
        calc
          (23 : ZMod 45293161) ^ 10 = (23 : ZMod 45293161) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 5 * (23 : ZMod 45293161) ^ 5 := by rw [pow_add]
          _ = 27368219 := by rw [factor_4_2]; decide
      have factor_4_4 : (23 : ZMod 45293161) ^ 20 = 21439260 := by
        calc
          (23 : ZMod 45293161) ^ 20 = (23 : ZMod 45293161) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 10 * (23 : ZMod 45293161) ^ 10 := by rw [pow_add]
          _ = 21439260 := by rw [factor_4_3]; decide
      have factor_4_5 : (23 : ZMod 45293161) ^ 41 = 17112071 := by
        calc
          (23 : ZMod 45293161) ^ 41 = (23 : ZMod 45293161) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 20 * (23 : ZMod 45293161) ^ 20) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 17112071 := by rw [factor_4_4]; decide
      have factor_4_6 : (23 : ZMod 45293161) ^ 82 = 15747542 := by
        calc
          (23 : ZMod 45293161) ^ 82 = (23 : ZMod 45293161) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 41 * (23 : ZMod 45293161) ^ 41 := by rw [pow_add]
          _ = 15747542 := by rw [factor_4_5]; decide
      have factor_4_7 : (23 : ZMod 45293161) ^ 165 = 21475022 := by
        calc
          (23 : ZMod 45293161) ^ 165 = (23 : ZMod 45293161) ^ (82 + 82 + 1) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = ((23 : ZMod 45293161) ^ 82 * (23 : ZMod 45293161) ^ 82) * (23 : ZMod 45293161) := by rw [pow_succ, pow_add]
          _ = 21475022 := by rw [factor_4_6]; decide
      have factor_4_8 : (23 : ZMod 45293161) ^ 330 = 19337849 := by
        calc
          (23 : ZMod 45293161) ^ 330 = (23 : ZMod 45293161) ^ (165 + 165) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 165 * (23 : ZMod 45293161) ^ 165 := by rw [pow_add]
          _ = 19337849 := by rw [factor_4_7]; decide
      have factor_4_9 : (23 : ZMod 45293161) ^ 660 = 18749975 := by
        calc
          (23 : ZMod 45293161) ^ 660 = (23 : ZMod 45293161) ^ (330 + 330) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 330 * (23 : ZMod 45293161) ^ 330 := by rw [pow_add]
          _ = 18749975 := by rw [factor_4_8]; decide
      have factor_4_10 : (23 : ZMod 45293161) ^ 1320 = 32616793 := by
        calc
          (23 : ZMod 45293161) ^ 1320 = (23 : ZMod 45293161) ^ (660 + 660) :=
            congrArg (fun n : ℕ => (23 : ZMod 45293161) ^ n) (by norm_num)
          _ = (23 : ZMod 45293161) ^ 660 * (23 : ZMod 45293161) ^ 660 := by rw [pow_add]
          _ = 32616793 := by rw [factor_4_9]; decide
      change (23 : ZMod 45293161) ^ 1320 ≠ 1
      rw [factor_4_10]
      decide

#print axioms prime_lucas_45293161

end TotientTailPeriodKiller
end Erdos249257
