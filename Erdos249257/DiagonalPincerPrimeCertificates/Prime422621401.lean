import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_422621401 : Nat.Prime 422621401 := by
  apply lucas_primality 422621401 (7 : ZMod 422621401)
  ·
      have fermat_0 : (7 : ZMod 422621401) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 422621401) ^ 3 = 343 := by
        calc
          (7 : ZMod 422621401) ^ 3 = (7 : ZMod 422621401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 1 * (7 : ZMod 422621401) ^ 1) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 422621401) ^ 6 = 117649 := by
        calc
          (7 : ZMod 422621401) ^ 6 = (7 : ZMod 422621401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 3 * (7 : ZMod 422621401) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 422621401) ^ 12 = 317402369 := by
        calc
          (7 : ZMod 422621401) ^ 12 = (7 : ZMod 422621401) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 6 * (7 : ZMod 422621401) ^ 6 := by rw [pow_add]
          _ = 317402369 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 422621401) ^ 25 = 116443466 := by
        calc
          (7 : ZMod 422621401) ^ 25 = (7 : ZMod 422621401) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 12 * (7 : ZMod 422621401) ^ 12) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 116443466 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 422621401) ^ 50 = 31817876 := by
        calc
          (7 : ZMod 422621401) ^ 50 = (7 : ZMod 422621401) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 25 * (7 : ZMod 422621401) ^ 25 := by rw [pow_add]
          _ = 31817876 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 422621401) ^ 100 = 345697906 := by
        calc
          (7 : ZMod 422621401) ^ 100 = (7 : ZMod 422621401) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 50 * (7 : ZMod 422621401) ^ 50 := by rw [pow_add]
          _ = 345697906 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 422621401) ^ 201 = 393616089 := by
        calc
          (7 : ZMod 422621401) ^ 201 = (7 : ZMod 422621401) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 100 * (7 : ZMod 422621401) ^ 100) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 393616089 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 422621401) ^ 403 = 337467380 := by
        calc
          (7 : ZMod 422621401) ^ 403 = (7 : ZMod 422621401) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 201 * (7 : ZMod 422621401) ^ 201) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 337467380 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 422621401) ^ 806 = 306744751 := by
        calc
          (7 : ZMod 422621401) ^ 806 = (7 : ZMod 422621401) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 403 * (7 : ZMod 422621401) ^ 403 := by rw [pow_add]
          _ = 306744751 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 422621401) ^ 1612 = 184799206 := by
        calc
          (7 : ZMod 422621401) ^ 1612 = (7 : ZMod 422621401) ^ (806 + 806) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 806 * (7 : ZMod 422621401) ^ 806 := by rw [pow_add]
          _ = 184799206 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 422621401) ^ 3224 = 118693486 := by
        calc
          (7 : ZMod 422621401) ^ 3224 = (7 : ZMod 422621401) ^ (1612 + 1612) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 1612 * (7 : ZMod 422621401) ^ 1612 := by rw [pow_add]
          _ = 118693486 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 422621401) ^ 6448 = 49501056 := by
        calc
          (7 : ZMod 422621401) ^ 6448 = (7 : ZMod 422621401) ^ (3224 + 3224) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 3224 * (7 : ZMod 422621401) ^ 3224 := by rw [pow_add]
          _ = 49501056 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 422621401) ^ 12897 = 63560824 := by
        calc
          (7 : ZMod 422621401) ^ 12897 = (7 : ZMod 422621401) ^ (6448 + 6448 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 6448 * (7 : ZMod 422621401) ^ 6448) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 63560824 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 422621401) ^ 25794 = 65094844 := by
        calc
          (7 : ZMod 422621401) ^ 25794 = (7 : ZMod 422621401) ^ (12897 + 12897) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 12897 * (7 : ZMod 422621401) ^ 12897 := by rw [pow_add]
          _ = 65094844 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 422621401) ^ 51589 = 295720691 := by
        calc
          (7 : ZMod 422621401) ^ 51589 = (7 : ZMod 422621401) ^ (25794 + 25794 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 25794 * (7 : ZMod 422621401) ^ 25794) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 295720691 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 422621401) ^ 103179 = 305095985 := by
        calc
          (7 : ZMod 422621401) ^ 103179 = (7 : ZMod 422621401) ^ (51589 + 51589 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 51589 * (7 : ZMod 422621401) ^ 51589) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 305095985 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 422621401) ^ 206358 = 51683994 := by
        calc
          (7 : ZMod 422621401) ^ 206358 = (7 : ZMod 422621401) ^ (103179 + 103179) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 103179 * (7 : ZMod 422621401) ^ 103179 := by rw [pow_add]
          _ = 51683994 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 422621401) ^ 412716 = 39503802 := by
        calc
          (7 : ZMod 422621401) ^ 412716 = (7 : ZMod 422621401) ^ (206358 + 206358) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 206358 * (7 : ZMod 422621401) ^ 206358 := by rw [pow_add]
          _ = 39503802 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 422621401) ^ 825432 = 140814055 := by
        calc
          (7 : ZMod 422621401) ^ 825432 = (7 : ZMod 422621401) ^ (412716 + 412716) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 412716 * (7 : ZMod 422621401) ^ 412716 := by rw [pow_add]
          _ = 140814055 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 422621401) ^ 1650864 = 282449514 := by
        calc
          (7 : ZMod 422621401) ^ 1650864 = (7 : ZMod 422621401) ^ (825432 + 825432) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 825432 * (7 : ZMod 422621401) ^ 825432 := by rw [pow_add]
          _ = 282449514 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 422621401) ^ 3301729 = 420450085 := by
        calc
          (7 : ZMod 422621401) ^ 3301729 = (7 : ZMod 422621401) ^ (1650864 + 1650864 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 1650864 * (7 : ZMod 422621401) ^ 1650864) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 420450085 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 422621401) ^ 6603459 = 209620303 := by
        calc
          (7 : ZMod 422621401) ^ 6603459 = (7 : ZMod 422621401) ^ (3301729 + 3301729 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 3301729 * (7 : ZMod 422621401) ^ 3301729) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 209620303 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 422621401) ^ 13206918 = 417381896 := by
        calc
          (7 : ZMod 422621401) ^ 13206918 = (7 : ZMod 422621401) ^ (6603459 + 6603459) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 6603459 * (7 : ZMod 422621401) ^ 6603459 := by rw [pow_add]
          _ = 417381896 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 422621401) ^ 26413837 = 92237673 := by
        calc
          (7 : ZMod 422621401) ^ 26413837 = (7 : ZMod 422621401) ^ (13206918 + 13206918 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 13206918 * (7 : ZMod 422621401) ^ 13206918) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 92237673 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 422621401) ^ 52827675 = 254780355 := by
        calc
          (7 : ZMod 422621401) ^ 52827675 = (7 : ZMod 422621401) ^ (26413837 + 26413837 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 26413837 * (7 : ZMod 422621401) ^ 26413837) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 254780355 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 422621401) ^ 105655350 = 317670454 := by
        calc
          (7 : ZMod 422621401) ^ 105655350 = (7 : ZMod 422621401) ^ (52827675 + 52827675) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 52827675 * (7 : ZMod 422621401) ^ 52827675 := by rw [pow_add]
          _ = 317670454 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 422621401) ^ 211310700 = 422621400 := by
        calc
          (7 : ZMod 422621401) ^ 211310700 = (7 : ZMod 422621401) ^ (105655350 + 105655350) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 105655350 * (7 : ZMod 422621401) ^ 105655350 := by rw [pow_add]
          _ = 422621400 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 422621401) ^ 422621400 = 1 := by
        calc
          (7 : ZMod 422621401) ^ 422621400 = (7 : ZMod 422621401) ^ (211310700 + 211310700) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 211310700 * (7 : ZMod 422621401) ^ 211310700 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (37, 1), (19037, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (37, 1), (19037, 1)] : List FactorBlock).map factorBlockValue).prod = 422621401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 422621401) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 422621401) ^ 3 = 343 := by
        calc
          (7 : ZMod 422621401) ^ 3 = (7 : ZMod 422621401) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 1 * (7 : ZMod 422621401) ^ 1) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 422621401) ^ 6 = 117649 := by
        calc
          (7 : ZMod 422621401) ^ 6 = (7 : ZMod 422621401) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 3 * (7 : ZMod 422621401) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 422621401) ^ 12 = 317402369 := by
        calc
          (7 : ZMod 422621401) ^ 12 = (7 : ZMod 422621401) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 6 * (7 : ZMod 422621401) ^ 6 := by rw [pow_add]
          _ = 317402369 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 422621401) ^ 25 = 116443466 := by
        calc
          (7 : ZMod 422621401) ^ 25 = (7 : ZMod 422621401) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 12 * (7 : ZMod 422621401) ^ 12) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 116443466 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 422621401) ^ 50 = 31817876 := by
        calc
          (7 : ZMod 422621401) ^ 50 = (7 : ZMod 422621401) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 25 * (7 : ZMod 422621401) ^ 25 := by rw [pow_add]
          _ = 31817876 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 422621401) ^ 100 = 345697906 := by
        calc
          (7 : ZMod 422621401) ^ 100 = (7 : ZMod 422621401) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 50 * (7 : ZMod 422621401) ^ 50 := by rw [pow_add]
          _ = 345697906 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 422621401) ^ 201 = 393616089 := by
        calc
          (7 : ZMod 422621401) ^ 201 = (7 : ZMod 422621401) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 100 * (7 : ZMod 422621401) ^ 100) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 393616089 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 422621401) ^ 403 = 337467380 := by
        calc
          (7 : ZMod 422621401) ^ 403 = (7 : ZMod 422621401) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 201 * (7 : ZMod 422621401) ^ 201) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 337467380 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 422621401) ^ 806 = 306744751 := by
        calc
          (7 : ZMod 422621401) ^ 806 = (7 : ZMod 422621401) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 403 * (7 : ZMod 422621401) ^ 403 := by rw [pow_add]
          _ = 306744751 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 422621401) ^ 1612 = 184799206 := by
        calc
          (7 : ZMod 422621401) ^ 1612 = (7 : ZMod 422621401) ^ (806 + 806) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 806 * (7 : ZMod 422621401) ^ 806 := by rw [pow_add]
          _ = 184799206 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 422621401) ^ 3224 = 118693486 := by
        calc
          (7 : ZMod 422621401) ^ 3224 = (7 : ZMod 422621401) ^ (1612 + 1612) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 1612 * (7 : ZMod 422621401) ^ 1612 := by rw [pow_add]
          _ = 118693486 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 422621401) ^ 6448 = 49501056 := by
        calc
          (7 : ZMod 422621401) ^ 6448 = (7 : ZMod 422621401) ^ (3224 + 3224) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 3224 * (7 : ZMod 422621401) ^ 3224 := by rw [pow_add]
          _ = 49501056 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 422621401) ^ 12897 = 63560824 := by
        calc
          (7 : ZMod 422621401) ^ 12897 = (7 : ZMod 422621401) ^ (6448 + 6448 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 6448 * (7 : ZMod 422621401) ^ 6448) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 63560824 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 422621401) ^ 25794 = 65094844 := by
        calc
          (7 : ZMod 422621401) ^ 25794 = (7 : ZMod 422621401) ^ (12897 + 12897) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 12897 * (7 : ZMod 422621401) ^ 12897 := by rw [pow_add]
          _ = 65094844 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 422621401) ^ 51589 = 295720691 := by
        calc
          (7 : ZMod 422621401) ^ 51589 = (7 : ZMod 422621401) ^ (25794 + 25794 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 25794 * (7 : ZMod 422621401) ^ 25794) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 295720691 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 422621401) ^ 103179 = 305095985 := by
        calc
          (7 : ZMod 422621401) ^ 103179 = (7 : ZMod 422621401) ^ (51589 + 51589 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 51589 * (7 : ZMod 422621401) ^ 51589) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 305095985 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 422621401) ^ 206358 = 51683994 := by
        calc
          (7 : ZMod 422621401) ^ 206358 = (7 : ZMod 422621401) ^ (103179 + 103179) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 103179 * (7 : ZMod 422621401) ^ 103179 := by rw [pow_add]
          _ = 51683994 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 422621401) ^ 412716 = 39503802 := by
        calc
          (7 : ZMod 422621401) ^ 412716 = (7 : ZMod 422621401) ^ (206358 + 206358) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 206358 * (7 : ZMod 422621401) ^ 206358 := by rw [pow_add]
          _ = 39503802 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 422621401) ^ 825432 = 140814055 := by
        calc
          (7 : ZMod 422621401) ^ 825432 = (7 : ZMod 422621401) ^ (412716 + 412716) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 412716 * (7 : ZMod 422621401) ^ 412716 := by rw [pow_add]
          _ = 140814055 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 422621401) ^ 1650864 = 282449514 := by
        calc
          (7 : ZMod 422621401) ^ 1650864 = (7 : ZMod 422621401) ^ (825432 + 825432) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 825432 * (7 : ZMod 422621401) ^ 825432 := by rw [pow_add]
          _ = 282449514 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 422621401) ^ 3301729 = 420450085 := by
        calc
          (7 : ZMod 422621401) ^ 3301729 = (7 : ZMod 422621401) ^ (1650864 + 1650864 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 1650864 * (7 : ZMod 422621401) ^ 1650864) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 420450085 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 422621401) ^ 6603459 = 209620303 := by
        calc
          (7 : ZMod 422621401) ^ 6603459 = (7 : ZMod 422621401) ^ (3301729 + 3301729 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 3301729 * (7 : ZMod 422621401) ^ 3301729) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 209620303 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 422621401) ^ 13206918 = 417381896 := by
        calc
          (7 : ZMod 422621401) ^ 13206918 = (7 : ZMod 422621401) ^ (6603459 + 6603459) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 6603459 * (7 : ZMod 422621401) ^ 6603459 := by rw [pow_add]
          _ = 417381896 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 422621401) ^ 26413837 = 92237673 := by
        calc
          (7 : ZMod 422621401) ^ 26413837 = (7 : ZMod 422621401) ^ (13206918 + 13206918 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 13206918 * (7 : ZMod 422621401) ^ 13206918) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 92237673 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 422621401) ^ 52827675 = 254780355 := by
        calc
          (7 : ZMod 422621401) ^ 52827675 = (7 : ZMod 422621401) ^ (26413837 + 26413837 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 26413837 * (7 : ZMod 422621401) ^ 26413837) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 254780355 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 422621401) ^ 105655350 = 317670454 := by
        calc
          (7 : ZMod 422621401) ^ 105655350 = (7 : ZMod 422621401) ^ (52827675 + 52827675) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 52827675 * (7 : ZMod 422621401) ^ 52827675 := by rw [pow_add]
          _ = 317670454 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 422621401) ^ 211310700 = 422621400 := by
        calc
          (7 : ZMod 422621401) ^ 211310700 = (7 : ZMod 422621401) ^ (105655350 + 105655350) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 105655350 * (7 : ZMod 422621401) ^ 105655350 := by rw [pow_add]
          _ = 422621400 := by rw [factor_0_26]; decide
      change (7 : ZMod 422621401) ^ 211310700 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (7 : ZMod 422621401) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 422621401) ^ 2 = 49 := by
        calc
          (7 : ZMod 422621401) ^ 2 = (7 : ZMod 422621401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 1 * (7 : ZMod 422621401) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 422621401) ^ 4 = 2401 := by
        calc
          (7 : ZMod 422621401) ^ 4 = (7 : ZMod 422621401) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 2 * (7 : ZMod 422621401) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 422621401) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 422621401) ^ 8 = (7 : ZMod 422621401) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 4 * (7 : ZMod 422621401) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 422621401) ^ 16 = 96701966 := by
        calc
          (7 : ZMod 422621401) ^ 16 = (7 : ZMod 422621401) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 8 * (7 : ZMod 422621401) ^ 8 := by rw [pow_add]
          _ = 96701966 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 422621401) ^ 33 = 171233510 := by
        calc
          (7 : ZMod 422621401) ^ 33 = (7 : ZMod 422621401) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 16 * (7 : ZMod 422621401) ^ 16) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 171233510 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 422621401) ^ 67 = 40525940 := by
        calc
          (7 : ZMod 422621401) ^ 67 = (7 : ZMod 422621401) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 33 * (7 : ZMod 422621401) ^ 33) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 40525940 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 422621401) ^ 134 = 250729094 := by
        calc
          (7 : ZMod 422621401) ^ 134 = (7 : ZMod 422621401) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 67 * (7 : ZMod 422621401) ^ 67 := by rw [pow_add]
          _ = 250729094 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 422621401) ^ 268 = 220170293 := by
        calc
          (7 : ZMod 422621401) ^ 268 = (7 : ZMod 422621401) ^ (134 + 134) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 134 * (7 : ZMod 422621401) ^ 134 := by rw [pow_add]
          _ = 220170293 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 422621401) ^ 537 = 58048852 := by
        calc
          (7 : ZMod 422621401) ^ 537 = (7 : ZMod 422621401) ^ (268 + 268 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 268 * (7 : ZMod 422621401) ^ 268) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 58048852 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 422621401) ^ 1074 = 174644847 := by
        calc
          (7 : ZMod 422621401) ^ 1074 = (7 : ZMod 422621401) ^ (537 + 537) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 537 * (7 : ZMod 422621401) ^ 537 := by rw [pow_add]
          _ = 174644847 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 422621401) ^ 2149 = 64705953 := by
        calc
          (7 : ZMod 422621401) ^ 2149 = (7 : ZMod 422621401) ^ (1074 + 1074 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 1074 * (7 : ZMod 422621401) ^ 1074) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 64705953 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 422621401) ^ 4299 = 22795689 := by
        calc
          (7 : ZMod 422621401) ^ 4299 = (7 : ZMod 422621401) ^ (2149 + 2149 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 2149 * (7 : ZMod 422621401) ^ 2149) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 22795689 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 422621401) ^ 8598 = 418335750 := by
        calc
          (7 : ZMod 422621401) ^ 8598 = (7 : ZMod 422621401) ^ (4299 + 4299) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 4299 * (7 : ZMod 422621401) ^ 4299 := by rw [pow_add]
          _ = 418335750 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 422621401) ^ 17196 = 101027742 := by
        calc
          (7 : ZMod 422621401) ^ 17196 = (7 : ZMod 422621401) ^ (8598 + 8598) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 8598 * (7 : ZMod 422621401) ^ 8598 := by rw [pow_add]
          _ = 101027742 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 422621401) ^ 34393 = 367530216 := by
        calc
          (7 : ZMod 422621401) ^ 34393 = (7 : ZMod 422621401) ^ (17196 + 17196 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 17196 * (7 : ZMod 422621401) ^ 17196) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 367530216 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 422621401) ^ 68786 = 400900166 := by
        calc
          (7 : ZMod 422621401) ^ 68786 = (7 : ZMod 422621401) ^ (34393 + 34393) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 34393 * (7 : ZMod 422621401) ^ 34393 := by rw [pow_add]
          _ = 400900166 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 422621401) ^ 137572 = 53577231 := by
        calc
          (7 : ZMod 422621401) ^ 137572 = (7 : ZMod 422621401) ^ (68786 + 68786) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 68786 * (7 : ZMod 422621401) ^ 68786 := by rw [pow_add]
          _ = 53577231 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 422621401) ^ 275144 = 322047384 := by
        calc
          (7 : ZMod 422621401) ^ 275144 = (7 : ZMod 422621401) ^ (137572 + 137572) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 137572 * (7 : ZMod 422621401) ^ 137572 := by rw [pow_add]
          _ = 322047384 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 422621401) ^ 550288 = 289311024 := by
        calc
          (7 : ZMod 422621401) ^ 550288 = (7 : ZMod 422621401) ^ (275144 + 275144) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 275144 * (7 : ZMod 422621401) ^ 275144 := by rw [pow_add]
          _ = 289311024 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 422621401) ^ 1100576 = 278838520 := by
        calc
          (7 : ZMod 422621401) ^ 1100576 = (7 : ZMod 422621401) ^ (550288 + 550288) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 550288 * (7 : ZMod 422621401) ^ 550288 := by rw [pow_add]
          _ = 278838520 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 422621401) ^ 2201153 = 363540113 := by
        calc
          (7 : ZMod 422621401) ^ 2201153 = (7 : ZMod 422621401) ^ (1100576 + 1100576 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 1100576 * (7 : ZMod 422621401) ^ 1100576) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 363540113 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 422621401) ^ 4402306 = 237562346 := by
        calc
          (7 : ZMod 422621401) ^ 4402306 = (7 : ZMod 422621401) ^ (2201153 + 2201153) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 2201153 * (7 : ZMod 422621401) ^ 2201153 := by rw [pow_add]
          _ = 237562346 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 422621401) ^ 8804612 = 353018868 := by
        calc
          (7 : ZMod 422621401) ^ 8804612 = (7 : ZMod 422621401) ^ (4402306 + 4402306) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 4402306 * (7 : ZMod 422621401) ^ 4402306 := by rw [pow_add]
          _ = 353018868 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 422621401) ^ 17609225 = 273051766 := by
        calc
          (7 : ZMod 422621401) ^ 17609225 = (7 : ZMod 422621401) ^ (8804612 + 8804612 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 8804612 * (7 : ZMod 422621401) ^ 8804612) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 273051766 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 422621401) ^ 35218450 = 241165744 := by
        calc
          (7 : ZMod 422621401) ^ 35218450 = (7 : ZMod 422621401) ^ (17609225 + 17609225) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 17609225 * (7 : ZMod 422621401) ^ 17609225 := by rw [pow_add]
          _ = 241165744 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 422621401) ^ 70436900 = 190273507 := by
        calc
          (7 : ZMod 422621401) ^ 70436900 = (7 : ZMod 422621401) ^ (35218450 + 35218450) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 35218450 * (7 : ZMod 422621401) ^ 35218450 := by rw [pow_add]
          _ = 190273507 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 422621401) ^ 140873800 = 190273506 := by
        calc
          (7 : ZMod 422621401) ^ 140873800 = (7 : ZMod 422621401) ^ (70436900 + 70436900) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 70436900 * (7 : ZMod 422621401) ^ 70436900 := by rw [pow_add]
          _ = 190273506 := by rw [factor_1_26]; decide
      change (7 : ZMod 422621401) ^ 140873800 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (7 : ZMod 422621401) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 422621401) ^ 2 = 49 := by
        calc
          (7 : ZMod 422621401) ^ 2 = (7 : ZMod 422621401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 1 * (7 : ZMod 422621401) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 422621401) ^ 5 = 16807 := by
        calc
          (7 : ZMod 422621401) ^ 5 = (7 : ZMod 422621401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 2 * (7 : ZMod 422621401) ^ 2) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 422621401) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 422621401) ^ 10 = (7 : ZMod 422621401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 5 * (7 : ZMod 422621401) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 422621401) ^ 20 = 162271217 := by
        calc
          (7 : ZMod 422621401) ^ 20 = (7 : ZMod 422621401) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 10 * (7 : ZMod 422621401) ^ 10 := by rw [pow_add]
          _ = 162271217 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 422621401) ^ 40 = 385168656 := by
        calc
          (7 : ZMod 422621401) ^ 40 = (7 : ZMod 422621401) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 20 * (7 : ZMod 422621401) ^ 20 := by rw [pow_add]
          _ = 385168656 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 422621401) ^ 80 = 207724960 := by
        calc
          (7 : ZMod 422621401) ^ 80 = (7 : ZMod 422621401) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 40 * (7 : ZMod 422621401) ^ 40 := by rw [pow_add]
          _ = 207724960 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 422621401) ^ 161 = 128767569 := by
        calc
          (7 : ZMod 422621401) ^ 161 = (7 : ZMod 422621401) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 80 * (7 : ZMod 422621401) ^ 80) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 128767569 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 422621401) ^ 322 = 196233059 := by
        calc
          (7 : ZMod 422621401) ^ 322 = (7 : ZMod 422621401) ^ (161 + 161) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 161 * (7 : ZMod 422621401) ^ 161 := by rw [pow_add]
          _ = 196233059 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 422621401) ^ 644 = 354006856 := by
        calc
          (7 : ZMod 422621401) ^ 644 = (7 : ZMod 422621401) ^ (322 + 322) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 322 * (7 : ZMod 422621401) ^ 322 := by rw [pow_add]
          _ = 354006856 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 422621401) ^ 1289 = 335262148 := by
        calc
          (7 : ZMod 422621401) ^ 1289 = (7 : ZMod 422621401) ^ (644 + 644 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 644 * (7 : ZMod 422621401) ^ 644) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 335262148 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 422621401) ^ 2579 = 185250627 := by
        calc
          (7 : ZMod 422621401) ^ 2579 = (7 : ZMod 422621401) ^ (1289 + 1289 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 1289 * (7 : ZMod 422621401) ^ 1289) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 185250627 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 422621401) ^ 5158 = 91047112 := by
        calc
          (7 : ZMod 422621401) ^ 5158 = (7 : ZMod 422621401) ^ (2579 + 2579) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 2579 * (7 : ZMod 422621401) ^ 2579 := by rw [pow_add]
          _ = 91047112 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 422621401) ^ 10317 = 33878163 := by
        calc
          (7 : ZMod 422621401) ^ 10317 = (7 : ZMod 422621401) ^ (5158 + 5158 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 5158 * (7 : ZMod 422621401) ^ 5158) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 33878163 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 422621401) ^ 20635 = 170298402 := by
        calc
          (7 : ZMod 422621401) ^ 20635 = (7 : ZMod 422621401) ^ (10317 + 10317 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 10317 * (7 : ZMod 422621401) ^ 10317) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 170298402 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 422621401) ^ 41271 = 278477273 := by
        calc
          (7 : ZMod 422621401) ^ 41271 = (7 : ZMod 422621401) ^ (20635 + 20635 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 20635 * (7 : ZMod 422621401) ^ 20635) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 278477273 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 422621401) ^ 82543 = 127167280 := by
        calc
          (7 : ZMod 422621401) ^ 82543 = (7 : ZMod 422621401) ^ (41271 + 41271 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 41271 * (7 : ZMod 422621401) ^ 41271) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 127167280 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 422621401) ^ 165086 = 56934615 := by
        calc
          (7 : ZMod 422621401) ^ 165086 = (7 : ZMod 422621401) ^ (82543 + 82543) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 82543 * (7 : ZMod 422621401) ^ 82543 := by rw [pow_add]
          _ = 56934615 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 422621401) ^ 330172 = 286902521 := by
        calc
          (7 : ZMod 422621401) ^ 330172 = (7 : ZMod 422621401) ^ (165086 + 165086) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 165086 * (7 : ZMod 422621401) ^ 165086 := by rw [pow_add]
          _ = 286902521 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 422621401) ^ 660345 = 358602222 := by
        calc
          (7 : ZMod 422621401) ^ 660345 = (7 : ZMod 422621401) ^ (330172 + 330172 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 330172 * (7 : ZMod 422621401) ^ 330172) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 358602222 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 422621401) ^ 1320691 = 148601392 := by
        calc
          (7 : ZMod 422621401) ^ 1320691 = (7 : ZMod 422621401) ^ (660345 + 660345 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 660345 * (7 : ZMod 422621401) ^ 660345) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 148601392 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 422621401) ^ 2641383 = 189284532 := by
        calc
          (7 : ZMod 422621401) ^ 2641383 = (7 : ZMod 422621401) ^ (1320691 + 1320691 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 1320691 * (7 : ZMod 422621401) ^ 1320691) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 189284532 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 422621401) ^ 5282767 = 88472782 := by
        calc
          (7 : ZMod 422621401) ^ 5282767 = (7 : ZMod 422621401) ^ (2641383 + 2641383 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 2641383 * (7 : ZMod 422621401) ^ 2641383) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 88472782 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 422621401) ^ 10565535 = 8246638 := by
        calc
          (7 : ZMod 422621401) ^ 10565535 = (7 : ZMod 422621401) ^ (5282767 + 5282767 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 5282767 * (7 : ZMod 422621401) ^ 5282767) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 8246638 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 422621401) ^ 21131070 = 70318327 := by
        calc
          (7 : ZMod 422621401) ^ 21131070 = (7 : ZMod 422621401) ^ (10565535 + 10565535) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 10565535 * (7 : ZMod 422621401) ^ 10565535 := by rw [pow_add]
          _ = 70318327 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 422621401) ^ 42262140 = 101350137 := by
        calc
          (7 : ZMod 422621401) ^ 42262140 = (7 : ZMod 422621401) ^ (21131070 + 21131070) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 21131070 * (7 : ZMod 422621401) ^ 21131070 := by rw [pow_add]
          _ = 101350137 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 422621401) ^ 84524280 = 350551882 := by
        calc
          (7 : ZMod 422621401) ^ 84524280 = (7 : ZMod 422621401) ^ (42262140 + 42262140) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 42262140 * (7 : ZMod 422621401) ^ 42262140 := by rw [pow_add]
          _ = 350551882 := by rw [factor_2_25]; decide
      change (7 : ZMod 422621401) ^ 84524280 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (7 : ZMod 422621401) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 422621401) ^ 2 = 49 := by
        calc
          (7 : ZMod 422621401) ^ 2 = (7 : ZMod 422621401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 1 * (7 : ZMod 422621401) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 422621401) ^ 5 = 16807 := by
        calc
          (7 : ZMod 422621401) ^ 5 = (7 : ZMod 422621401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 2 * (7 : ZMod 422621401) ^ 2) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 422621401) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 422621401) ^ 10 = (7 : ZMod 422621401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 5 * (7 : ZMod 422621401) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 422621401) ^ 21 = 290655717 := by
        calc
          (7 : ZMod 422621401) ^ 21 = (7 : ZMod 422621401) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 10 * (7 : ZMod 422621401) ^ 10) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 290655717 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 422621401) ^ 43 = 254971896 := by
        calc
          (7 : ZMod 422621401) ^ 43 = (7 : ZMod 422621401) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 21 * (7 : ZMod 422621401) ^ 21) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 254971896 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 422621401) ^ 87 = 55550896 := by
        calc
          (7 : ZMod 422621401) ^ 87 = (7 : ZMod 422621401) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 43 * (7 : ZMod 422621401) ^ 43) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 55550896 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 422621401) ^ 174 = 29124204 := by
        calc
          (7 : ZMod 422621401) ^ 174 = (7 : ZMod 422621401) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 87 * (7 : ZMod 422621401) ^ 87 := by rw [pow_add]
          _ = 29124204 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 422621401) ^ 348 = 356727774 := by
        calc
          (7 : ZMod 422621401) ^ 348 = (7 : ZMod 422621401) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 174 * (7 : ZMod 422621401) ^ 174 := by rw [pow_add]
          _ = 356727774 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 422621401) ^ 697 = 49747202 := by
        calc
          (7 : ZMod 422621401) ^ 697 = (7 : ZMod 422621401) ^ (348 + 348 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 348 * (7 : ZMod 422621401) ^ 348) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 49747202 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 422621401) ^ 1394 = 242581410 := by
        calc
          (7 : ZMod 422621401) ^ 1394 = (7 : ZMod 422621401) ^ (697 + 697) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 697 * (7 : ZMod 422621401) ^ 697 := by rw [pow_add]
          _ = 242581410 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 422621401) ^ 2788 = 418179651 := by
        calc
          (7 : ZMod 422621401) ^ 2788 = (7 : ZMod 422621401) ^ (1394 + 1394) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 1394 * (7 : ZMod 422621401) ^ 1394 := by rw [pow_add]
          _ = 418179651 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 422621401) ^ 5577 = 202640121 := by
        calc
          (7 : ZMod 422621401) ^ 5577 = (7 : ZMod 422621401) ^ (2788 + 2788 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 2788 * (7 : ZMod 422621401) ^ 2788) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 202640121 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 422621401) ^ 11154 = 412672184 := by
        calc
          (7 : ZMod 422621401) ^ 11154 = (7 : ZMod 422621401) ^ (5577 + 5577) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 5577 * (7 : ZMod 422621401) ^ 5577 := by rw [pow_add]
          _ = 412672184 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 422621401) ^ 22308 = 111749468 := by
        calc
          (7 : ZMod 422621401) ^ 22308 = (7 : ZMod 422621401) ^ (11154 + 11154) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 11154 * (7 : ZMod 422621401) ^ 11154 := by rw [pow_add]
          _ = 111749468 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 422621401) ^ 44617 = 399451362 := by
        calc
          (7 : ZMod 422621401) ^ 44617 = (7 : ZMod 422621401) ^ (22308 + 22308 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 22308 * (7 : ZMod 422621401) ^ 22308) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 399451362 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 422621401) ^ 89235 = 381681835 := by
        calc
          (7 : ZMod 422621401) ^ 89235 = (7 : ZMod 422621401) ^ (44617 + 44617 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 44617 * (7 : ZMod 422621401) ^ 44617) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 381681835 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 422621401) ^ 178471 = 367985226 := by
        calc
          (7 : ZMod 422621401) ^ 178471 = (7 : ZMod 422621401) ^ (89235 + 89235 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 89235 * (7 : ZMod 422621401) ^ 89235) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 367985226 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 422621401) ^ 356943 = 251342912 := by
        calc
          (7 : ZMod 422621401) ^ 356943 = (7 : ZMod 422621401) ^ (178471 + 178471 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 178471 * (7 : ZMod 422621401) ^ 178471) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 251342912 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 422621401) ^ 713887 = 245432516 := by
        calc
          (7 : ZMod 422621401) ^ 713887 = (7 : ZMod 422621401) ^ (356943 + 356943 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 356943 * (7 : ZMod 422621401) ^ 356943) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 245432516 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 422621401) ^ 1427775 = 106071824 := by
        calc
          (7 : ZMod 422621401) ^ 1427775 = (7 : ZMod 422621401) ^ (713887 + 713887 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 713887 * (7 : ZMod 422621401) ^ 713887) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 106071824 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 422621401) ^ 2855550 = 360506892 := by
        calc
          (7 : ZMod 422621401) ^ 2855550 = (7 : ZMod 422621401) ^ (1427775 + 1427775) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 1427775 * (7 : ZMod 422621401) ^ 1427775 := by rw [pow_add]
          _ = 360506892 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 422621401) ^ 5711100 = 29445841 := by
        calc
          (7 : ZMod 422621401) ^ 5711100 = (7 : ZMod 422621401) ^ (2855550 + 2855550) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 2855550 * (7 : ZMod 422621401) ^ 2855550 := by rw [pow_add]
          _ = 29445841 := by rw [factor_3_21]; decide
      have factor_3_23 : (7 : ZMod 422621401) ^ 11422200 = 301341864 := by
        calc
          (7 : ZMod 422621401) ^ 11422200 = (7 : ZMod 422621401) ^ (5711100 + 5711100) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 5711100 * (7 : ZMod 422621401) ^ 5711100 := by rw [pow_add]
          _ = 301341864 := by rw [factor_3_22]; decide
      change (7 : ZMod 422621401) ^ 11422200 ≠ 1
      rw [factor_3_23]
      decide
    ·
      have factor_4_0 : (7 : ZMod 422621401) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 422621401) ^ 2 = 49 := by
        calc
          (7 : ZMod 422621401) ^ 2 = (7 : ZMod 422621401) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 1 * (7 : ZMod 422621401) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 422621401) ^ 5 = 16807 := by
        calc
          (7 : ZMod 422621401) ^ 5 = (7 : ZMod 422621401) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 2 * (7 : ZMod 422621401) ^ 2) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 422621401) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 422621401) ^ 10 = (7 : ZMod 422621401) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 5 * (7 : ZMod 422621401) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 422621401) ^ 21 = 290655717 := by
        calc
          (7 : ZMod 422621401) ^ 21 = (7 : ZMod 422621401) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 10 * (7 : ZMod 422621401) ^ 10) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 290655717 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 422621401) ^ 43 = 254971896 := by
        calc
          (7 : ZMod 422621401) ^ 43 = (7 : ZMod 422621401) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 21 * (7 : ZMod 422621401) ^ 21) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 254971896 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 422621401) ^ 86 = 128684814 := by
        calc
          (7 : ZMod 422621401) ^ 86 = (7 : ZMod 422621401) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 43 * (7 : ZMod 422621401) ^ 43 := by rw [pow_add]
          _ = 128684814 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 422621401) ^ 173 = 245658544 := by
        calc
          (7 : ZMod 422621401) ^ 173 = (7 : ZMod 422621401) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 86 * (7 : ZMod 422621401) ^ 86) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 245658544 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 422621401) ^ 346 = 404026780 := by
        calc
          (7 : ZMod 422621401) ^ 346 = (7 : ZMod 422621401) ^ (173 + 173) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 173 * (7 : ZMod 422621401) ^ 173 := by rw [pow_add]
          _ = 404026780 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 422621401) ^ 693 = 134499166 := by
        calc
          (7 : ZMod 422621401) ^ 693 = (7 : ZMod 422621401) ^ (346 + 346 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 346 * (7 : ZMod 422621401) ^ 346) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 134499166 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 422621401) ^ 1387 = 301711587 := by
        calc
          (7 : ZMod 422621401) ^ 1387 = (7 : ZMod 422621401) ^ (693 + 693 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 693 * (7 : ZMod 422621401) ^ 693) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 301711587 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 422621401) ^ 2775 = 28603031 := by
        calc
          (7 : ZMod 422621401) ^ 2775 = (7 : ZMod 422621401) ^ (1387 + 1387 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = ((7 : ZMod 422621401) ^ 1387 * (7 : ZMod 422621401) ^ 1387) * (7 : ZMod 422621401) := by rw [pow_succ, pow_add]
          _ = 28603031 := by rw [factor_4_10]; decide
      have factor_4_12 : (7 : ZMod 422621401) ^ 5550 = 52775507 := by
        calc
          (7 : ZMod 422621401) ^ 5550 = (7 : ZMod 422621401) ^ (2775 + 2775) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 2775 * (7 : ZMod 422621401) ^ 2775 := by rw [pow_add]
          _ = 52775507 := by rw [factor_4_11]; decide
      have factor_4_13 : (7 : ZMod 422621401) ^ 11100 = 337664426 := by
        calc
          (7 : ZMod 422621401) ^ 11100 = (7 : ZMod 422621401) ^ (5550 + 5550) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 5550 * (7 : ZMod 422621401) ^ 5550 := by rw [pow_add]
          _ = 337664426 := by rw [factor_4_12]; decide
      have factor_4_14 : (7 : ZMod 422621401) ^ 22200 = 409225849 := by
        calc
          (7 : ZMod 422621401) ^ 22200 = (7 : ZMod 422621401) ^ (11100 + 11100) :=
            congrArg (fun n : ℕ => (7 : ZMod 422621401) ^ n) (by norm_num)
          _ = (7 : ZMod 422621401) ^ 11100 * (7 : ZMod 422621401) ^ 11100 := by rw [pow_add]
          _ = 409225849 := by rw [factor_4_13]; decide
      change (7 : ZMod 422621401) ^ 22200 ≠ 1
      rw [factor_4_14]
      decide

#print axioms prime_lucas_422621401

end TotientTailPeriodKiller
end Erdos249257
