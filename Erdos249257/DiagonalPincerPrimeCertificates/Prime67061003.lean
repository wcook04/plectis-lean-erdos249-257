import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_67061003 : Nat.Prime 67061003 := by
  apply lucas_primality 67061003 (2 : ZMod 67061003)
  ·
      have fermat_0 : (2 : ZMod 67061003) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 67061003) ^ 3 = 8 := by
        calc
          (2 : ZMod 67061003) ^ 3 = (2 : ZMod 67061003) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 1 * (2 : ZMod 67061003) ^ 1) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 67061003) ^ 7 = 128 := by
        calc
          (2 : ZMod 67061003) ^ 7 = (2 : ZMod 67061003) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 3 * (2 : ZMod 67061003) ^ 3) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 67061003) ^ 15 = 32768 := by
        calc
          (2 : ZMod 67061003) ^ 15 = (2 : ZMod 67061003) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 7 * (2 : ZMod 67061003) ^ 7) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 67061003) ^ 31 = 1531552 := by
        calc
          (2 : ZMod 67061003) ^ 31 = (2 : ZMod 67061003) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 15 * (2 : ZMod 67061003) ^ 15) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 1531552 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 67061003) ^ 63 = 50592543 := by
        calc
          (2 : ZMod 67061003) ^ 63 = (2 : ZMod 67061003) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 31 * (2 : ZMod 67061003) ^ 31) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 50592543 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 67061003) ^ 127 = 42156817 := by
        calc
          (2 : ZMod 67061003) ^ 127 = (2 : ZMod 67061003) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 63 * (2 : ZMod 67061003) ^ 63) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 42156817 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 67061003) ^ 255 = 65491766 := by
        calc
          (2 : ZMod 67061003) ^ 255 = (2 : ZMod 67061003) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 127 * (2 : ZMod 67061003) ^ 127) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 65491766 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 67061003) ^ 511 = 49464018 := by
        calc
          (2 : ZMod 67061003) ^ 511 = (2 : ZMod 67061003) ^ (255 + 255 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 255 * (2 : ZMod 67061003) ^ 255) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 49464018 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 67061003) ^ 1023 = 3024477 := by
        calc
          (2 : ZMod 67061003) ^ 1023 = (2 : ZMod 67061003) ^ (511 + 511 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 511 * (2 : ZMod 67061003) ^ 511) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 3024477 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 67061003) ^ 2046 = 5009314 := by
        calc
          (2 : ZMod 67061003) ^ 2046 = (2 : ZMod 67061003) ^ (1023 + 1023) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 1023 * (2 : ZMod 67061003) ^ 1023 := by rw [pow_add]
          _ = 5009314 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 67061003) ^ 4093 = 10686082 := by
        calc
          (2 : ZMod 67061003) ^ 4093 = (2 : ZMod 67061003) ^ (2046 + 2046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 2046 * (2 : ZMod 67061003) ^ 2046) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 10686082 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 67061003) ^ 8186 = 809285 := by
        calc
          (2 : ZMod 67061003) ^ 8186 = (2 : ZMod 67061003) ^ (4093 + 4093) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 4093 * (2 : ZMod 67061003) ^ 4093 := by rw [pow_add]
          _ = 809285 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 67061003) ^ 16372 = 24455927 := by
        calc
          (2 : ZMod 67061003) ^ 16372 = (2 : ZMod 67061003) ^ (8186 + 8186) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 8186 * (2 : ZMod 67061003) ^ 8186 := by rw [pow_add]
          _ = 24455927 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 67061003) ^ 32744 = 25182436 := by
        calc
          (2 : ZMod 67061003) ^ 32744 = (2 : ZMod 67061003) ^ (16372 + 16372) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 16372 * (2 : ZMod 67061003) ^ 16372 := by rw [pow_add]
          _ = 25182436 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 67061003) ^ 65489 = 35347846 := by
        calc
          (2 : ZMod 67061003) ^ 65489 = (2 : ZMod 67061003) ^ (32744 + 32744 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 32744 * (2 : ZMod 67061003) ^ 32744) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 35347846 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 67061003) ^ 130978 = 3399181 := by
        calc
          (2 : ZMod 67061003) ^ 130978 = (2 : ZMod 67061003) ^ (65489 + 65489) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 65489 * (2 : ZMod 67061003) ^ 65489 := by rw [pow_add]
          _ = 3399181 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 67061003) ^ 261957 = 43673740 := by
        calc
          (2 : ZMod 67061003) ^ 261957 = (2 : ZMod 67061003) ^ (130978 + 130978 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 130978 * (2 : ZMod 67061003) ^ 130978) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 43673740 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 67061003) ^ 523914 = 44986521 := by
        calc
          (2 : ZMod 67061003) ^ 523914 = (2 : ZMod 67061003) ^ (261957 + 261957) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 261957 * (2 : ZMod 67061003) ^ 261957 := by rw [pow_add]
          _ = 44986521 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 67061003) ^ 1047828 = 4848541 := by
        calc
          (2 : ZMod 67061003) ^ 1047828 = (2 : ZMod 67061003) ^ (523914 + 523914) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 523914 * (2 : ZMod 67061003) ^ 523914 := by rw [pow_add]
          _ = 4848541 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 67061003) ^ 2095656 = 48166028 := by
        calc
          (2 : ZMod 67061003) ^ 2095656 = (2 : ZMod 67061003) ^ (1047828 + 1047828) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 1047828 * (2 : ZMod 67061003) ^ 1047828 := by rw [pow_add]
          _ = 48166028 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 67061003) ^ 4191312 = 41869195 := by
        calc
          (2 : ZMod 67061003) ^ 4191312 = (2 : ZMod 67061003) ^ (2095656 + 2095656) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 2095656 * (2 : ZMod 67061003) ^ 2095656 := by rw [pow_add]
          _ = 41869195 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 67061003) ^ 8382625 = 31255142 := by
        calc
          (2 : ZMod 67061003) ^ 8382625 = (2 : ZMod 67061003) ^ (4191312 + 4191312 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 4191312 * (2 : ZMod 67061003) ^ 4191312) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 31255142 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 67061003) ^ 16765250 = 34065885 := by
        calc
          (2 : ZMod 67061003) ^ 16765250 = (2 : ZMod 67061003) ^ (8382625 + 8382625) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 8382625 * (2 : ZMod 67061003) ^ 8382625 := by rw [pow_add]
          _ = 34065885 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 67061003) ^ 33530501 = 67061002 := by
        calc
          (2 : ZMod 67061003) ^ 33530501 = (2 : ZMod 67061003) ^ (16765250 + 16765250 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 16765250 * (2 : ZMod 67061003) ^ 16765250) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 67061002 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 67061003) ^ 67061002 = 1 := by
        calc
          (2 : ZMod 67061003) ^ 67061002 = (2 : ZMod 67061003) ^ (33530501 + 33530501) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 33530501 * (2 : ZMod 67061003) ^ 33530501 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (383, 1), (87547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (383, 1), (87547, 1)] : List FactorBlock).map factorBlockValue).prod = 67061003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 67061003) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 67061003) ^ 3 = 8 := by
        calc
          (2 : ZMod 67061003) ^ 3 = (2 : ZMod 67061003) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 1 * (2 : ZMod 67061003) ^ 1) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 67061003) ^ 7 = 128 := by
        calc
          (2 : ZMod 67061003) ^ 7 = (2 : ZMod 67061003) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 3 * (2 : ZMod 67061003) ^ 3) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 67061003) ^ 15 = 32768 := by
        calc
          (2 : ZMod 67061003) ^ 15 = (2 : ZMod 67061003) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 7 * (2 : ZMod 67061003) ^ 7) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 67061003) ^ 31 = 1531552 := by
        calc
          (2 : ZMod 67061003) ^ 31 = (2 : ZMod 67061003) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 15 * (2 : ZMod 67061003) ^ 15) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 1531552 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 67061003) ^ 63 = 50592543 := by
        calc
          (2 : ZMod 67061003) ^ 63 = (2 : ZMod 67061003) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 31 * (2 : ZMod 67061003) ^ 31) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 50592543 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 67061003) ^ 127 = 42156817 := by
        calc
          (2 : ZMod 67061003) ^ 127 = (2 : ZMod 67061003) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 63 * (2 : ZMod 67061003) ^ 63) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 42156817 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 67061003) ^ 255 = 65491766 := by
        calc
          (2 : ZMod 67061003) ^ 255 = (2 : ZMod 67061003) ^ (127 + 127 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 127 * (2 : ZMod 67061003) ^ 127) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 65491766 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 67061003) ^ 511 = 49464018 := by
        calc
          (2 : ZMod 67061003) ^ 511 = (2 : ZMod 67061003) ^ (255 + 255 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 255 * (2 : ZMod 67061003) ^ 255) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 49464018 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 67061003) ^ 1023 = 3024477 := by
        calc
          (2 : ZMod 67061003) ^ 1023 = (2 : ZMod 67061003) ^ (511 + 511 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 511 * (2 : ZMod 67061003) ^ 511) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 3024477 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 67061003) ^ 2046 = 5009314 := by
        calc
          (2 : ZMod 67061003) ^ 2046 = (2 : ZMod 67061003) ^ (1023 + 1023) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 1023 * (2 : ZMod 67061003) ^ 1023 := by rw [pow_add]
          _ = 5009314 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 67061003) ^ 4093 = 10686082 := by
        calc
          (2 : ZMod 67061003) ^ 4093 = (2 : ZMod 67061003) ^ (2046 + 2046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 2046 * (2 : ZMod 67061003) ^ 2046) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 10686082 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 67061003) ^ 8186 = 809285 := by
        calc
          (2 : ZMod 67061003) ^ 8186 = (2 : ZMod 67061003) ^ (4093 + 4093) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 4093 * (2 : ZMod 67061003) ^ 4093 := by rw [pow_add]
          _ = 809285 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 67061003) ^ 16372 = 24455927 := by
        calc
          (2 : ZMod 67061003) ^ 16372 = (2 : ZMod 67061003) ^ (8186 + 8186) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 8186 * (2 : ZMod 67061003) ^ 8186 := by rw [pow_add]
          _ = 24455927 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 67061003) ^ 32744 = 25182436 := by
        calc
          (2 : ZMod 67061003) ^ 32744 = (2 : ZMod 67061003) ^ (16372 + 16372) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 16372 * (2 : ZMod 67061003) ^ 16372 := by rw [pow_add]
          _ = 25182436 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 67061003) ^ 65489 = 35347846 := by
        calc
          (2 : ZMod 67061003) ^ 65489 = (2 : ZMod 67061003) ^ (32744 + 32744 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 32744 * (2 : ZMod 67061003) ^ 32744) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 35347846 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 67061003) ^ 130978 = 3399181 := by
        calc
          (2 : ZMod 67061003) ^ 130978 = (2 : ZMod 67061003) ^ (65489 + 65489) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 65489 * (2 : ZMod 67061003) ^ 65489 := by rw [pow_add]
          _ = 3399181 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 67061003) ^ 261957 = 43673740 := by
        calc
          (2 : ZMod 67061003) ^ 261957 = (2 : ZMod 67061003) ^ (130978 + 130978 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 130978 * (2 : ZMod 67061003) ^ 130978) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 43673740 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 67061003) ^ 523914 = 44986521 := by
        calc
          (2 : ZMod 67061003) ^ 523914 = (2 : ZMod 67061003) ^ (261957 + 261957) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 261957 * (2 : ZMod 67061003) ^ 261957 := by rw [pow_add]
          _ = 44986521 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 67061003) ^ 1047828 = 4848541 := by
        calc
          (2 : ZMod 67061003) ^ 1047828 = (2 : ZMod 67061003) ^ (523914 + 523914) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 523914 * (2 : ZMod 67061003) ^ 523914 := by rw [pow_add]
          _ = 4848541 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 67061003) ^ 2095656 = 48166028 := by
        calc
          (2 : ZMod 67061003) ^ 2095656 = (2 : ZMod 67061003) ^ (1047828 + 1047828) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 1047828 * (2 : ZMod 67061003) ^ 1047828 := by rw [pow_add]
          _ = 48166028 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 67061003) ^ 4191312 = 41869195 := by
        calc
          (2 : ZMod 67061003) ^ 4191312 = (2 : ZMod 67061003) ^ (2095656 + 2095656) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 2095656 * (2 : ZMod 67061003) ^ 2095656 := by rw [pow_add]
          _ = 41869195 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 67061003) ^ 8382625 = 31255142 := by
        calc
          (2 : ZMod 67061003) ^ 8382625 = (2 : ZMod 67061003) ^ (4191312 + 4191312 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 4191312 * (2 : ZMod 67061003) ^ 4191312) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 31255142 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 67061003) ^ 16765250 = 34065885 := by
        calc
          (2 : ZMod 67061003) ^ 16765250 = (2 : ZMod 67061003) ^ (8382625 + 8382625) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 8382625 * (2 : ZMod 67061003) ^ 8382625 := by rw [pow_add]
          _ = 34065885 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 67061003) ^ 33530501 = 67061002 := by
        calc
          (2 : ZMod 67061003) ^ 33530501 = (2 : ZMod 67061003) ^ (16765250 + 16765250 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 16765250 * (2 : ZMod 67061003) ^ 16765250) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 67061002 := by rw [factor_0_23]; decide
      change (2 : ZMod 67061003) ^ 33530501 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 67061003) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 67061003) ^ 2 = 4 := by
        calc
          (2 : ZMod 67061003) ^ 2 = (2 : ZMod 67061003) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 1 * (2 : ZMod 67061003) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 67061003) ^ 5 = 32 := by
        calc
          (2 : ZMod 67061003) ^ 5 = (2 : ZMod 67061003) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 2 * (2 : ZMod 67061003) ^ 2) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 67061003) ^ 10 = 1024 := by
        calc
          (2 : ZMod 67061003) ^ 10 = (2 : ZMod 67061003) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 5 * (2 : ZMod 67061003) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 67061003) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 67061003) ^ 21 = (2 : ZMod 67061003) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 10 * (2 : ZMod 67061003) ^ 10) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 67061003) ^ 42 = 51812358 := by
        calc
          (2 : ZMod 67061003) ^ 42 = (2 : ZMod 67061003) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 21 * (2 : ZMod 67061003) ^ 21 := by rw [pow_add]
          _ = 51812358 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 67061003) ^ 85 = 44292202 := by
        calc
          (2 : ZMod 67061003) ^ 85 = (2 : ZMod 67061003) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 42 * (2 : ZMod 67061003) ^ 42) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 44292202 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 67061003) ^ 170 = 63418960 := by
        calc
          (2 : ZMod 67061003) ^ 170 = (2 : ZMod 67061003) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 85 * (2 : ZMod 67061003) ^ 85 := by rw [pow_add]
          _ = 63418960 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 67061003) ^ 341 = 24006916 := by
        calc
          (2 : ZMod 67061003) ^ 341 = (2 : ZMod 67061003) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 170 * (2 : ZMod 67061003) ^ 170) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 24006916 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 67061003) ^ 683 = 64407242 := by
        calc
          (2 : ZMod 67061003) ^ 683 = (2 : ZMod 67061003) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 341 * (2 : ZMod 67061003) ^ 341) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 64407242 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 67061003) ^ 1367 = 5369149 := by
        calc
          (2 : ZMod 67061003) ^ 1367 = (2 : ZMod 67061003) ^ (683 + 683 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 683 * (2 : ZMod 67061003) ^ 683) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 5369149 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 67061003) ^ 2735 = 25822161 := by
        calc
          (2 : ZMod 67061003) ^ 2735 = (2 : ZMod 67061003) ^ (1367 + 1367 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 1367 * (2 : ZMod 67061003) ^ 1367) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 25822161 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 67061003) ^ 5471 = 228160 := by
        calc
          (2 : ZMod 67061003) ^ 5471 = (2 : ZMod 67061003) ^ (2735 + 2735 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 2735 * (2 : ZMod 67061003) ^ 2735) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 228160 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 67061003) ^ 10943 = 35294544 := by
        calc
          (2 : ZMod 67061003) ^ 10943 = (2 : ZMod 67061003) ^ (5471 + 5471 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 5471 * (2 : ZMod 67061003) ^ 5471) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 35294544 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 67061003) ^ 21886 = 30984848 := by
        calc
          (2 : ZMod 67061003) ^ 21886 = (2 : ZMod 67061003) ^ (10943 + 10943) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 10943 * (2 : ZMod 67061003) ^ 10943 := by rw [pow_add]
          _ = 30984848 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 67061003) ^ 43773 = 58147825 := by
        calc
          (2 : ZMod 67061003) ^ 43773 = (2 : ZMod 67061003) ^ (21886 + 21886 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 21886 * (2 : ZMod 67061003) ^ 21886) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 58147825 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 67061003) ^ 87547 = 39064387 := by
        calc
          (2 : ZMod 67061003) ^ 87547 = (2 : ZMod 67061003) ^ (43773 + 43773 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 43773 * (2 : ZMod 67061003) ^ 43773) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 39064387 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 67061003) ^ 175094 = 29045390 := by
        calc
          (2 : ZMod 67061003) ^ 175094 = (2 : ZMod 67061003) ^ (87547 + 87547) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 87547 * (2 : ZMod 67061003) ^ 87547 := by rw [pow_add]
          _ = 29045390 := by rw [factor_1_16]; decide
      change (2 : ZMod 67061003) ^ 175094 ≠ 1
      rw [factor_1_17]
      decide
    ·
      have factor_2_0 : (2 : ZMod 67061003) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 67061003) ^ 2 = 4 := by
        calc
          (2 : ZMod 67061003) ^ 2 = (2 : ZMod 67061003) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 1 * (2 : ZMod 67061003) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 67061003) ^ 5 = 32 := by
        calc
          (2 : ZMod 67061003) ^ 5 = (2 : ZMod 67061003) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 2 * (2 : ZMod 67061003) ^ 2) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 67061003) ^ 11 = 2048 := by
        calc
          (2 : ZMod 67061003) ^ 11 = (2 : ZMod 67061003) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 5 * (2 : ZMod 67061003) ^ 5) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 67061003) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 67061003) ^ 23 = (2 : ZMod 67061003) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 11 * (2 : ZMod 67061003) ^ 11) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 67061003) ^ 47 = 48531384 := by
        calc
          (2 : ZMod 67061003) ^ 47 = (2 : ZMod 67061003) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 23 * (2 : ZMod 67061003) ^ 23) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 48531384 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 67061003) ^ 95 = 21976820 := by
        calc
          (2 : ZMod 67061003) ^ 95 = (2 : ZMod 67061003) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 47 * (2 : ZMod 67061003) ^ 47) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 21976820 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 67061003) ^ 191 = 62236152 := by
        calc
          (2 : ZMod 67061003) ^ 191 = (2 : ZMod 67061003) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 95 * (2 : ZMod 67061003) ^ 95) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 62236152 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 67061003) ^ 383 = 65913598 := by
        calc
          (2 : ZMod 67061003) ^ 383 = (2 : ZMod 67061003) ^ (191 + 191 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = ((2 : ZMod 67061003) ^ 191 * (2 : ZMod 67061003) ^ 191) * (2 : ZMod 67061003) := by rw [pow_succ, pow_add]
          _ = 65913598 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 67061003) ^ 766 = 63684132 := by
        calc
          (2 : ZMod 67061003) ^ 766 = (2 : ZMod 67061003) ^ (383 + 383) :=
            congrArg (fun n : ℕ => (2 : ZMod 67061003) ^ n) (by norm_num)
          _ = (2 : ZMod 67061003) ^ 383 * (2 : ZMod 67061003) ^ 383 := by rw [pow_add]
          _ = 63684132 := by rw [factor_2_8]; decide
      change (2 : ZMod 67061003) ^ 766 ≠ 1
      rw [factor_2_9]
      decide

#print axioms prime_lucas_67061003

end TotientTailPeriodKiller
end Erdos249257
