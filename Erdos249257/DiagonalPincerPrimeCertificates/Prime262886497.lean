import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_262886497 : Nat.Prime 262886497 := by
  apply lucas_primality 262886497 (5 : ZMod 262886497)
  ·
      have fermat_0 : (5 : ZMod 262886497) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 262886497) ^ 3 = 125 := by
        calc
          (5 : ZMod 262886497) ^ 3 = (5 : ZMod 262886497) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 1 * (5 : ZMod 262886497) ^ 1) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 262886497) ^ 7 = 78125 := by
        calc
          (5 : ZMod 262886497) ^ 7 = (5 : ZMod 262886497) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 3 * (5 : ZMod 262886497) ^ 3) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 262886497) ^ 15 = 22744473 := by
        calc
          (5 : ZMod 262886497) ^ 15 = (5 : ZMod 262886497) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 7 * (5 : ZMod 262886497) ^ 7) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 22744473 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 262886497) ^ 31 = 31725316 := by
        calc
          (5 : ZMod 262886497) ^ 31 = (5 : ZMod 262886497) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 15 * (5 : ZMod 262886497) ^ 15) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 31725316 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 262886497) ^ 62 = 20517752 := by
        calc
          (5 : ZMod 262886497) ^ 62 = (5 : ZMod 262886497) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 31 * (5 : ZMod 262886497) ^ 31 := by rw [pow_add]
          _ = 20517752 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 262886497) ^ 125 = 90255046 := by
        calc
          (5 : ZMod 262886497) ^ 125 = (5 : ZMod 262886497) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 62 * (5 : ZMod 262886497) ^ 62) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 90255046 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 262886497) ^ 250 = 141764581 := by
        calc
          (5 : ZMod 262886497) ^ 250 = (5 : ZMod 262886497) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 125 * (5 : ZMod 262886497) ^ 125 := by rw [pow_add]
          _ = 141764581 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 262886497) ^ 501 = 141054128 := by
        calc
          (5 : ZMod 262886497) ^ 501 = (5 : ZMod 262886497) ^ (250 + 250 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 250 * (5 : ZMod 262886497) ^ 250) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 141054128 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 262886497) ^ 1002 = 87909988 := by
        calc
          (5 : ZMod 262886497) ^ 1002 = (5 : ZMod 262886497) ^ (501 + 501) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 501 * (5 : ZMod 262886497) ^ 501 := by rw [pow_add]
          _ = 87909988 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 262886497) ^ 2005 = 240977946 := by
        calc
          (5 : ZMod 262886497) ^ 2005 = (5 : ZMod 262886497) ^ (1002 + 1002 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 1002 * (5 : ZMod 262886497) ^ 1002) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 240977946 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 262886497) ^ 4011 = 131332371 := by
        calc
          (5 : ZMod 262886497) ^ 4011 = (5 : ZMod 262886497) ^ (2005 + 2005 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 2005 * (5 : ZMod 262886497) ^ 2005) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 131332371 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 262886497) ^ 8022 = 135319520 := by
        calc
          (5 : ZMod 262886497) ^ 8022 = (5 : ZMod 262886497) ^ (4011 + 4011) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 4011 * (5 : ZMod 262886497) ^ 4011 := by rw [pow_add]
          _ = 135319520 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 262886497) ^ 16045 = 160647271 := by
        calc
          (5 : ZMod 262886497) ^ 16045 = (5 : ZMod 262886497) ^ (8022 + 8022 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 8022 * (5 : ZMod 262886497) ^ 8022) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 160647271 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 262886497) ^ 32090 = 88836692 := by
        calc
          (5 : ZMod 262886497) ^ 32090 = (5 : ZMod 262886497) ^ (16045 + 16045) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 16045 * (5 : ZMod 262886497) ^ 16045 := by rw [pow_add]
          _ = 88836692 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 262886497) ^ 64181 = 254820320 := by
        calc
          (5 : ZMod 262886497) ^ 64181 = (5 : ZMod 262886497) ^ (32090 + 32090 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 32090 * (5 : ZMod 262886497) ^ 32090) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 254820320 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 262886497) ^ 128362 = 117820314 := by
        calc
          (5 : ZMod 262886497) ^ 128362 = (5 : ZMod 262886497) ^ (64181 + 64181) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 64181 * (5 : ZMod 262886497) ^ 64181 := by rw [pow_add]
          _ = 117820314 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 262886497) ^ 256725 = 146541053 := by
        calc
          (5 : ZMod 262886497) ^ 256725 = (5 : ZMod 262886497) ^ (128362 + 128362 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 128362 * (5 : ZMod 262886497) ^ 128362) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 146541053 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 262886497) ^ 513450 = 11179836 := by
        calc
          (5 : ZMod 262886497) ^ 513450 = (5 : ZMod 262886497) ^ (256725 + 256725) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 256725 * (5 : ZMod 262886497) ^ 256725 := by rw [pow_add]
          _ = 11179836 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 262886497) ^ 1026900 = 136647737 := by
        calc
          (5 : ZMod 262886497) ^ 1026900 = (5 : ZMod 262886497) ^ (513450 + 513450) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 513450 * (5 : ZMod 262886497) ^ 513450 := by rw [pow_add]
          _ = 136647737 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 262886497) ^ 2053800 = 124606613 := by
        calc
          (5 : ZMod 262886497) ^ 2053800 = (5 : ZMod 262886497) ^ (1026900 + 1026900) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 1026900 * (5 : ZMod 262886497) ^ 1026900 := by rw [pow_add]
          _ = 124606613 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 262886497) ^ 4107601 = 175612581 := by
        calc
          (5 : ZMod 262886497) ^ 4107601 = (5 : ZMod 262886497) ^ (2053800 + 2053800 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 2053800 * (5 : ZMod 262886497) ^ 2053800) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 175612581 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 262886497) ^ 8215203 = 68809965 := by
        calc
          (5 : ZMod 262886497) ^ 8215203 = (5 : ZMod 262886497) ^ (4107601 + 4107601 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 4107601 * (5 : ZMod 262886497) ^ 4107601) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 68809965 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 262886497) ^ 16430406 = 178603296 := by
        calc
          (5 : ZMod 262886497) ^ 16430406 = (5 : ZMod 262886497) ^ (8215203 + 8215203) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 8215203 * (5 : ZMod 262886497) ^ 8215203 := by rw [pow_add]
          _ = 178603296 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 262886497) ^ 32860812 = 38539705 := by
        calc
          (5 : ZMod 262886497) ^ 32860812 = (5 : ZMod 262886497) ^ (16430406 + 16430406) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 16430406 * (5 : ZMod 262886497) ^ 16430406 := by rw [pow_add]
          _ = 38539705 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 262886497) ^ 65721624 = 153437025 := by
        calc
          (5 : ZMod 262886497) ^ 65721624 = (5 : ZMod 262886497) ^ (32860812 + 32860812) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 32860812 * (5 : ZMod 262886497) ^ 32860812 := by rw [pow_add]
          _ = 153437025 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 262886497) ^ 131443248 = 262886496 := by
        calc
          (5 : ZMod 262886497) ^ 131443248 = (5 : ZMod 262886497) ^ (65721624 + 65721624) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 65721624 * (5 : ZMod 262886497) ^ 65721624 := by rw [pow_add]
          _ = 262886496 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 262886497) ^ 262886496 = 1 := by
        calc
          (5 : ZMod 262886497) ^ 262886496 = (5 : ZMod 262886497) ^ (131443248 + 131443248) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 131443248 * (5 : ZMod 262886497) ^ 131443248 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (487, 1), (5623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (487, 1), (5623, 1)] : List FactorBlock).map factorBlockValue).prod = 262886497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 262886497) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 262886497) ^ 3 = 125 := by
        calc
          (5 : ZMod 262886497) ^ 3 = (5 : ZMod 262886497) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 1 * (5 : ZMod 262886497) ^ 1) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 262886497) ^ 7 = 78125 := by
        calc
          (5 : ZMod 262886497) ^ 7 = (5 : ZMod 262886497) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 3 * (5 : ZMod 262886497) ^ 3) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 262886497) ^ 15 = 22744473 := by
        calc
          (5 : ZMod 262886497) ^ 15 = (5 : ZMod 262886497) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 7 * (5 : ZMod 262886497) ^ 7) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 22744473 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 262886497) ^ 31 = 31725316 := by
        calc
          (5 : ZMod 262886497) ^ 31 = (5 : ZMod 262886497) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 15 * (5 : ZMod 262886497) ^ 15) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 31725316 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 262886497) ^ 62 = 20517752 := by
        calc
          (5 : ZMod 262886497) ^ 62 = (5 : ZMod 262886497) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 31 * (5 : ZMod 262886497) ^ 31 := by rw [pow_add]
          _ = 20517752 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 262886497) ^ 125 = 90255046 := by
        calc
          (5 : ZMod 262886497) ^ 125 = (5 : ZMod 262886497) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 62 * (5 : ZMod 262886497) ^ 62) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 90255046 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 262886497) ^ 250 = 141764581 := by
        calc
          (5 : ZMod 262886497) ^ 250 = (5 : ZMod 262886497) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 125 * (5 : ZMod 262886497) ^ 125 := by rw [pow_add]
          _ = 141764581 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 262886497) ^ 501 = 141054128 := by
        calc
          (5 : ZMod 262886497) ^ 501 = (5 : ZMod 262886497) ^ (250 + 250 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 250 * (5 : ZMod 262886497) ^ 250) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 141054128 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 262886497) ^ 1002 = 87909988 := by
        calc
          (5 : ZMod 262886497) ^ 1002 = (5 : ZMod 262886497) ^ (501 + 501) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 501 * (5 : ZMod 262886497) ^ 501 := by rw [pow_add]
          _ = 87909988 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 262886497) ^ 2005 = 240977946 := by
        calc
          (5 : ZMod 262886497) ^ 2005 = (5 : ZMod 262886497) ^ (1002 + 1002 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 1002 * (5 : ZMod 262886497) ^ 1002) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 240977946 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 262886497) ^ 4011 = 131332371 := by
        calc
          (5 : ZMod 262886497) ^ 4011 = (5 : ZMod 262886497) ^ (2005 + 2005 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 2005 * (5 : ZMod 262886497) ^ 2005) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 131332371 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 262886497) ^ 8022 = 135319520 := by
        calc
          (5 : ZMod 262886497) ^ 8022 = (5 : ZMod 262886497) ^ (4011 + 4011) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 4011 * (5 : ZMod 262886497) ^ 4011 := by rw [pow_add]
          _ = 135319520 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 262886497) ^ 16045 = 160647271 := by
        calc
          (5 : ZMod 262886497) ^ 16045 = (5 : ZMod 262886497) ^ (8022 + 8022 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 8022 * (5 : ZMod 262886497) ^ 8022) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 160647271 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 262886497) ^ 32090 = 88836692 := by
        calc
          (5 : ZMod 262886497) ^ 32090 = (5 : ZMod 262886497) ^ (16045 + 16045) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 16045 * (5 : ZMod 262886497) ^ 16045 := by rw [pow_add]
          _ = 88836692 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 262886497) ^ 64181 = 254820320 := by
        calc
          (5 : ZMod 262886497) ^ 64181 = (5 : ZMod 262886497) ^ (32090 + 32090 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 32090 * (5 : ZMod 262886497) ^ 32090) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 254820320 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 262886497) ^ 128362 = 117820314 := by
        calc
          (5 : ZMod 262886497) ^ 128362 = (5 : ZMod 262886497) ^ (64181 + 64181) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 64181 * (5 : ZMod 262886497) ^ 64181 := by rw [pow_add]
          _ = 117820314 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 262886497) ^ 256725 = 146541053 := by
        calc
          (5 : ZMod 262886497) ^ 256725 = (5 : ZMod 262886497) ^ (128362 + 128362 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 128362 * (5 : ZMod 262886497) ^ 128362) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 146541053 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 262886497) ^ 513450 = 11179836 := by
        calc
          (5 : ZMod 262886497) ^ 513450 = (5 : ZMod 262886497) ^ (256725 + 256725) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 256725 * (5 : ZMod 262886497) ^ 256725 := by rw [pow_add]
          _ = 11179836 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 262886497) ^ 1026900 = 136647737 := by
        calc
          (5 : ZMod 262886497) ^ 1026900 = (5 : ZMod 262886497) ^ (513450 + 513450) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 513450 * (5 : ZMod 262886497) ^ 513450 := by rw [pow_add]
          _ = 136647737 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 262886497) ^ 2053800 = 124606613 := by
        calc
          (5 : ZMod 262886497) ^ 2053800 = (5 : ZMod 262886497) ^ (1026900 + 1026900) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 1026900 * (5 : ZMod 262886497) ^ 1026900 := by rw [pow_add]
          _ = 124606613 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 262886497) ^ 4107601 = 175612581 := by
        calc
          (5 : ZMod 262886497) ^ 4107601 = (5 : ZMod 262886497) ^ (2053800 + 2053800 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 2053800 * (5 : ZMod 262886497) ^ 2053800) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 175612581 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 262886497) ^ 8215203 = 68809965 := by
        calc
          (5 : ZMod 262886497) ^ 8215203 = (5 : ZMod 262886497) ^ (4107601 + 4107601 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 4107601 * (5 : ZMod 262886497) ^ 4107601) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 68809965 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 262886497) ^ 16430406 = 178603296 := by
        calc
          (5 : ZMod 262886497) ^ 16430406 = (5 : ZMod 262886497) ^ (8215203 + 8215203) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 8215203 * (5 : ZMod 262886497) ^ 8215203 := by rw [pow_add]
          _ = 178603296 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 262886497) ^ 32860812 = 38539705 := by
        calc
          (5 : ZMod 262886497) ^ 32860812 = (5 : ZMod 262886497) ^ (16430406 + 16430406) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 16430406 * (5 : ZMod 262886497) ^ 16430406 := by rw [pow_add]
          _ = 38539705 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 262886497) ^ 65721624 = 153437025 := by
        calc
          (5 : ZMod 262886497) ^ 65721624 = (5 : ZMod 262886497) ^ (32860812 + 32860812) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 32860812 * (5 : ZMod 262886497) ^ 32860812 := by rw [pow_add]
          _ = 153437025 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 262886497) ^ 131443248 = 262886496 := by
        calc
          (5 : ZMod 262886497) ^ 131443248 = (5 : ZMod 262886497) ^ (65721624 + 65721624) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 65721624 * (5 : ZMod 262886497) ^ 65721624 := by rw [pow_add]
          _ = 262886496 := by rw [factor_0_25]; decide
      change (5 : ZMod 262886497) ^ 131443248 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (5 : ZMod 262886497) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 262886497) ^ 2 = 25 := by
        calc
          (5 : ZMod 262886497) ^ 2 = (5 : ZMod 262886497) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 1 * (5 : ZMod 262886497) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 262886497) ^ 5 = 3125 := by
        calc
          (5 : ZMod 262886497) ^ 5 = (5 : ZMod 262886497) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 2 * (5 : ZMod 262886497) ^ 2) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 262886497) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 262886497) ^ 10 = (5 : ZMod 262886497) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 5 * (5 : ZMod 262886497) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 262886497) ^ 20 = 97123935 := by
        calc
          (5 : ZMod 262886497) ^ 20 = (5 : ZMod 262886497) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 10 * (5 : ZMod 262886497) ^ 10 := by rw [pow_add]
          _ = 97123935 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 262886497) ^ 41 = 18845066 := by
        calc
          (5 : ZMod 262886497) ^ 41 = (5 : ZMod 262886497) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 20 * (5 : ZMod 262886497) ^ 20) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 18845066 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 262886497) ^ 83 = 208431957 := by
        calc
          (5 : ZMod 262886497) ^ 83 = (5 : ZMod 262886497) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 41 * (5 : ZMod 262886497) ^ 41) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 208431957 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 262886497) ^ 167 = 88735418 := by
        calc
          (5 : ZMod 262886497) ^ 167 = (5 : ZMod 262886497) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 83 * (5 : ZMod 262886497) ^ 83) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 88735418 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 262886497) ^ 334 = 152582700 := by
        calc
          (5 : ZMod 262886497) ^ 334 = (5 : ZMod 262886497) ^ (167 + 167) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 167 * (5 : ZMod 262886497) ^ 167 := by rw [pow_add]
          _ = 152582700 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 262886497) ^ 668 = 56819377 := by
        calc
          (5 : ZMod 262886497) ^ 668 = (5 : ZMod 262886497) ^ (334 + 334) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 334 * (5 : ZMod 262886497) ^ 334 := by rw [pow_add]
          _ = 56819377 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 262886497) ^ 1337 = 211317793 := by
        calc
          (5 : ZMod 262886497) ^ 1337 = (5 : ZMod 262886497) ^ (668 + 668 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 668 * (5 : ZMod 262886497) ^ 668) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 211317793 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 262886497) ^ 2674 = 83215789 := by
        calc
          (5 : ZMod 262886497) ^ 2674 = (5 : ZMod 262886497) ^ (1337 + 1337) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 1337 * (5 : ZMod 262886497) ^ 1337 := by rw [pow_add]
          _ = 83215789 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 262886497) ^ 5348 = 27668010 := by
        calc
          (5 : ZMod 262886497) ^ 5348 = (5 : ZMod 262886497) ^ (2674 + 2674) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 2674 * (5 : ZMod 262886497) ^ 2674 := by rw [pow_add]
          _ = 27668010 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 262886497) ^ 10696 = 133145022 := by
        calc
          (5 : ZMod 262886497) ^ 10696 = (5 : ZMod 262886497) ^ (5348 + 5348) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 5348 * (5 : ZMod 262886497) ^ 5348 := by rw [pow_add]
          _ = 133145022 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 262886497) ^ 21393 = 48363630 := by
        calc
          (5 : ZMod 262886497) ^ 21393 = (5 : ZMod 262886497) ^ (10696 + 10696 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 10696 * (5 : ZMod 262886497) ^ 10696) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 48363630 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 262886497) ^ 42787 = 14076462 := by
        calc
          (5 : ZMod 262886497) ^ 42787 = (5 : ZMod 262886497) ^ (21393 + 21393 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 21393 * (5 : ZMod 262886497) ^ 21393) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 14076462 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 262886497) ^ 85575 = 143105745 := by
        calc
          (5 : ZMod 262886497) ^ 85575 = (5 : ZMod 262886497) ^ (42787 + 42787 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 42787 * (5 : ZMod 262886497) ^ 42787) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 143105745 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 262886497) ^ 171150 = 228640543 := by
        calc
          (5 : ZMod 262886497) ^ 171150 = (5 : ZMod 262886497) ^ (85575 + 85575) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 85575 * (5 : ZMod 262886497) ^ 85575 := by rw [pow_add]
          _ = 228640543 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 262886497) ^ 342300 = 68251171 := by
        calc
          (5 : ZMod 262886497) ^ 342300 = (5 : ZMod 262886497) ^ (171150 + 171150) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 171150 * (5 : ZMod 262886497) ^ 171150 := by rw [pow_add]
          _ = 68251171 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 262886497) ^ 684600 = 64436298 := by
        calc
          (5 : ZMod 262886497) ^ 684600 = (5 : ZMod 262886497) ^ (342300 + 342300) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 342300 * (5 : ZMod 262886497) ^ 342300 := by rw [pow_add]
          _ = 64436298 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 262886497) ^ 1369200 = 68391385 := by
        calc
          (5 : ZMod 262886497) ^ 1369200 = (5 : ZMod 262886497) ^ (684600 + 684600) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 684600 * (5 : ZMod 262886497) ^ 684600 := by rw [pow_add]
          _ = 68391385 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 262886497) ^ 2738401 = 216523113 := by
        calc
          (5 : ZMod 262886497) ^ 2738401 = (5 : ZMod 262886497) ^ (1369200 + 1369200 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 1369200 * (5 : ZMod 262886497) ^ 1369200) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 216523113 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 262886497) ^ 5476802 = 165197275 := by
        calc
          (5 : ZMod 262886497) ^ 5476802 = (5 : ZMod 262886497) ^ (2738401 + 2738401) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 2738401 * (5 : ZMod 262886497) ^ 2738401 := by rw [pow_add]
          _ = 165197275 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 262886497) ^ 10953604 = 197319395 := by
        calc
          (5 : ZMod 262886497) ^ 10953604 = (5 : ZMod 262886497) ^ (5476802 + 5476802) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 5476802 * (5 : ZMod 262886497) ^ 5476802 := by rw [pow_add]
          _ = 197319395 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 262886497) ^ 21907208 = 200910609 := by
        calc
          (5 : ZMod 262886497) ^ 21907208 = (5 : ZMod 262886497) ^ (10953604 + 10953604) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 10953604 * (5 : ZMod 262886497) ^ 10953604 := by rw [pow_add]
          _ = 200910609 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 262886497) ^ 43814416 = 8392771 := by
        calc
          (5 : ZMod 262886497) ^ 43814416 = (5 : ZMod 262886497) ^ (21907208 + 21907208) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 21907208 * (5 : ZMod 262886497) ^ 21907208 := by rw [pow_add]
          _ = 8392771 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 262886497) ^ 87628832 = 8392770 := by
        calc
          (5 : ZMod 262886497) ^ 87628832 = (5 : ZMod 262886497) ^ (43814416 + 43814416) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 43814416 * (5 : ZMod 262886497) ^ 43814416 := by rw [pow_add]
          _ = 8392770 := by rw [factor_1_25]; decide
      change (5 : ZMod 262886497) ^ 87628832 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (5 : ZMod 262886497) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 262886497) ^ 2 = 25 := by
        calc
          (5 : ZMod 262886497) ^ 2 = (5 : ZMod 262886497) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 1 * (5 : ZMod 262886497) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 262886497) ^ 4 = 625 := by
        calc
          (5 : ZMod 262886497) ^ 4 = (5 : ZMod 262886497) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 2 * (5 : ZMod 262886497) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 262886497) ^ 8 = 390625 := by
        calc
          (5 : ZMod 262886497) ^ 8 = (5 : ZMod 262886497) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 4 * (5 : ZMod 262886497) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 262886497) ^ 16 = 113722365 := by
        calc
          (5 : ZMod 262886497) ^ 16 = (5 : ZMod 262886497) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 8 * (5 : ZMod 262886497) ^ 8 := by rw [pow_add]
          _ = 113722365 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 262886497) ^ 32 = 158626580 := by
        calc
          (5 : ZMod 262886497) ^ 32 = (5 : ZMod 262886497) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 16 * (5 : ZMod 262886497) ^ 16 := by rw [pow_add]
          _ = 158626580 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 262886497) ^ 65 = 198740527 := by
        calc
          (5 : ZMod 262886497) ^ 65 = (5 : ZMod 262886497) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 32 * (5 : ZMod 262886497) ^ 32) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 198740527 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 262886497) ^ 131 = 111923842 := by
        calc
          (5 : ZMod 262886497) ^ 131 = (5 : ZMod 262886497) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 65 * (5 : ZMod 262886497) ^ 65) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 111923842 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 262886497) ^ 263 = 166814417 := by
        calc
          (5 : ZMod 262886497) ^ 263 = (5 : ZMod 262886497) ^ (131 + 131 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 131 * (5 : ZMod 262886497) ^ 131) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 166814417 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 262886497) ^ 527 = 79604773 := by
        calc
          (5 : ZMod 262886497) ^ 527 = (5 : ZMod 262886497) ^ (263 + 263 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 263 * (5 : ZMod 262886497) ^ 263) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 79604773 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 262886497) ^ 1054 = 126789494 := by
        calc
          (5 : ZMod 262886497) ^ 1054 = (5 : ZMod 262886497) ^ (527 + 527) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 527 * (5 : ZMod 262886497) ^ 527 := by rw [pow_add]
          _ = 126789494 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 262886497) ^ 2108 = 249828792 := by
        calc
          (5 : ZMod 262886497) ^ 2108 = (5 : ZMod 262886497) ^ (1054 + 1054) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 1054 * (5 : ZMod 262886497) ^ 1054 := by rw [pow_add]
          _ = 249828792 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 262886497) ^ 4217 = 260689364 := by
        calc
          (5 : ZMod 262886497) ^ 4217 = (5 : ZMod 262886497) ^ (2108 + 2108 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 2108 * (5 : ZMod 262886497) ^ 2108) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 260689364 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 262886497) ^ 8434 = 8675278 := by
        calc
          (5 : ZMod 262886497) ^ 8434 = (5 : ZMod 262886497) ^ (4217 + 4217) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 4217 * (5 : ZMod 262886497) ^ 4217 := by rw [pow_add]
          _ = 8675278 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 262886497) ^ 16869 = 200804692 := by
        calc
          (5 : ZMod 262886497) ^ 16869 = (5 : ZMod 262886497) ^ (8434 + 8434 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 8434 * (5 : ZMod 262886497) ^ 8434) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 200804692 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 262886497) ^ 33738 = 234169198 := by
        calc
          (5 : ZMod 262886497) ^ 33738 = (5 : ZMod 262886497) ^ (16869 + 16869) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 16869 * (5 : ZMod 262886497) ^ 16869 := by rw [pow_add]
          _ = 234169198 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 262886497) ^ 67476 = 171284994 := by
        calc
          (5 : ZMod 262886497) ^ 67476 = (5 : ZMod 262886497) ^ (33738 + 33738) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 33738 * (5 : ZMod 262886497) ^ 33738 := by rw [pow_add]
          _ = 171284994 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 262886497) ^ 134952 = 217941782 := by
        calc
          (5 : ZMod 262886497) ^ 134952 = (5 : ZMod 262886497) ^ (67476 + 67476) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 67476 * (5 : ZMod 262886497) ^ 67476 := by rw [pow_add]
          _ = 217941782 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 262886497) ^ 269904 = 202661309 := by
        calc
          (5 : ZMod 262886497) ^ 269904 = (5 : ZMod 262886497) ^ (134952 + 134952) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 134952 * (5 : ZMod 262886497) ^ 134952 := by rw [pow_add]
          _ = 202661309 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 262886497) ^ 539808 = 141671165 := by
        calc
          (5 : ZMod 262886497) ^ 539808 = (5 : ZMod 262886497) ^ (269904 + 269904) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 269904 * (5 : ZMod 262886497) ^ 269904 := by rw [pow_add]
          _ = 141671165 := by rw [factor_2_18]; decide
      change (5 : ZMod 262886497) ^ 539808 ≠ 1
      rw [factor_2_19]
      decide
    ·
      have factor_3_0 : (5 : ZMod 262886497) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 262886497) ^ 2 = 25 := by
        calc
          (5 : ZMod 262886497) ^ 2 = (5 : ZMod 262886497) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 1 * (5 : ZMod 262886497) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 262886497) ^ 5 = 3125 := by
        calc
          (5 : ZMod 262886497) ^ 5 = (5 : ZMod 262886497) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 2 * (5 : ZMod 262886497) ^ 2) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 262886497) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 262886497) ^ 11 = (5 : ZMod 262886497) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 5 * (5 : ZMod 262886497) ^ 5) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 262886497) ^ 22 = 62119902 := by
        calc
          (5 : ZMod 262886497) ^ 22 = (5 : ZMod 262886497) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 11 * (5 : ZMod 262886497) ^ 11 := by rw [pow_add]
          _ = 62119902 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 262886497) ^ 45 = 211160382 := by
        calc
          (5 : ZMod 262886497) ^ 45 = (5 : ZMod 262886497) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 22 * (5 : ZMod 262886497) ^ 22) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 211160382 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 262886497) ^ 91 = 156217255 := by
        calc
          (5 : ZMod 262886497) ^ 91 = (5 : ZMod 262886497) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 45 * (5 : ZMod 262886497) ^ 45) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 156217255 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 262886497) ^ 182 = 217481404 := by
        calc
          (5 : ZMod 262886497) ^ 182 = (5 : ZMod 262886497) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 91 * (5 : ZMod 262886497) ^ 91 := by rw [pow_add]
          _ = 217481404 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 262886497) ^ 365 = 252904540 := by
        calc
          (5 : ZMod 262886497) ^ 365 = (5 : ZMod 262886497) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 182 * (5 : ZMod 262886497) ^ 182) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 252904540 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 262886497) ^ 730 = 225456909 := by
        calc
          (5 : ZMod 262886497) ^ 730 = (5 : ZMod 262886497) ^ (365 + 365) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 365 * (5 : ZMod 262886497) ^ 365 := by rw [pow_add]
          _ = 225456909 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 262886497) ^ 1461 = 107711181 := by
        calc
          (5 : ZMod 262886497) ^ 1461 = (5 : ZMod 262886497) ^ (730 + 730 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = ((5 : ZMod 262886497) ^ 730 * (5 : ZMod 262886497) ^ 730) * (5 : ZMod 262886497) := by rw [pow_succ, pow_add]
          _ = 107711181 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 262886497) ^ 2922 = 39178665 := by
        calc
          (5 : ZMod 262886497) ^ 2922 = (5 : ZMod 262886497) ^ (1461 + 1461) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 1461 * (5 : ZMod 262886497) ^ 1461 := by rw [pow_add]
          _ = 39178665 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 262886497) ^ 5844 = 86735422 := by
        calc
          (5 : ZMod 262886497) ^ 5844 = (5 : ZMod 262886497) ^ (2922 + 2922) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 2922 * (5 : ZMod 262886497) ^ 2922 := by rw [pow_add]
          _ = 86735422 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 262886497) ^ 11688 = 29409204 := by
        calc
          (5 : ZMod 262886497) ^ 11688 = (5 : ZMod 262886497) ^ (5844 + 5844) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 5844 * (5 : ZMod 262886497) ^ 5844 := by rw [pow_add]
          _ = 29409204 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 262886497) ^ 23376 = 235713167 := by
        calc
          (5 : ZMod 262886497) ^ 23376 = (5 : ZMod 262886497) ^ (11688 + 11688) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 11688 * (5 : ZMod 262886497) ^ 11688 := by rw [pow_add]
          _ = 235713167 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 262886497) ^ 46752 = 54018234 := by
        calc
          (5 : ZMod 262886497) ^ 46752 = (5 : ZMod 262886497) ^ (23376 + 23376) :=
            congrArg (fun n : ℕ => (5 : ZMod 262886497) ^ n) (by norm_num)
          _ = (5 : ZMod 262886497) ^ 23376 * (5 : ZMod 262886497) ^ 23376 := by rw [pow_add]
          _ = 54018234 := by rw [factor_3_14]; decide
      change (5 : ZMod 262886497) ^ 46752 ≠ 1
      rw [factor_3_15]
      decide

#print axioms prime_lucas_262886497

end TotientTailPeriodKiller
end Erdos249257
