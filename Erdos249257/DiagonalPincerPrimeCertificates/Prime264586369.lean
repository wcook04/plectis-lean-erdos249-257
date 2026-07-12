import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_264586369 : Nat.Prime 264586369 := by
  apply lucas_primality 264586369 (7 : ZMod 264586369)
  ·
      have fermat_0 : (7 : ZMod 264586369) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 264586369) ^ 3 = 343 := by
        calc
          (7 : ZMod 264586369) ^ 3 = (7 : ZMod 264586369) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 1 * (7 : ZMod 264586369) ^ 1) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 264586369) ^ 7 = 823543 := by
        calc
          (7 : ZMod 264586369) ^ 7 = (7 : ZMod 264586369) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 3 * (7 : ZMod 264586369) ^ 3) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 264586369) ^ 15 = 88290976 := by
        calc
          (7 : ZMod 264586369) ^ 15 = (7 : ZMod 264586369) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 7 * (7 : ZMod 264586369) ^ 7) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 88290976 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 264586369) ^ 31 = 249724539 := by
        calc
          (7 : ZMod 264586369) ^ 31 = (7 : ZMod 264586369) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 15 * (7 : ZMod 264586369) ^ 15) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 249724539 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 264586369) ^ 63 = 80972468 := by
        calc
          (7 : ZMod 264586369) ^ 63 = (7 : ZMod 264586369) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 31 * (7 : ZMod 264586369) ^ 31) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 80972468 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 264586369) ^ 126 = 126239195 := by
        calc
          (7 : ZMod 264586369) ^ 126 = (7 : ZMod 264586369) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 63 * (7 : ZMod 264586369) ^ 63 := by rw [pow_add]
          _ = 126239195 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 264586369) ^ 252 = 218885638 := by
        calc
          (7 : ZMod 264586369) ^ 252 = (7 : ZMod 264586369) ^ (126 + 126) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 126 * (7 : ZMod 264586369) ^ 126 := by rw [pow_add]
          _ = 218885638 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 264586369) ^ 504 = 124309238 := by
        calc
          (7 : ZMod 264586369) ^ 504 = (7 : ZMod 264586369) ^ (252 + 252) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 252 * (7 : ZMod 264586369) ^ 252 := by rw [pow_add]
          _ = 124309238 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 264586369) ^ 1009 = 133741648 := by
        calc
          (7 : ZMod 264586369) ^ 1009 = (7 : ZMod 264586369) ^ (504 + 504 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 504 * (7 : ZMod 264586369) ^ 504) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 133741648 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 264586369) ^ 2018 = 75044439 := by
        calc
          (7 : ZMod 264586369) ^ 2018 = (7 : ZMod 264586369) ^ (1009 + 1009) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 1009 * (7 : ZMod 264586369) ^ 1009 := by rw [pow_add]
          _ = 75044439 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 264586369) ^ 4037 = 203880123 := by
        calc
          (7 : ZMod 264586369) ^ 4037 = (7 : ZMod 264586369) ^ (2018 + 2018 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 2018 * (7 : ZMod 264586369) ^ 2018) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 203880123 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 264586369) ^ 8074 = 190374163 := by
        calc
          (7 : ZMod 264586369) ^ 8074 = (7 : ZMod 264586369) ^ (4037 + 4037) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 4037 * (7 : ZMod 264586369) ^ 4037 := by rw [pow_add]
          _ = 190374163 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 264586369) ^ 16149 = 219052363 := by
        calc
          (7 : ZMod 264586369) ^ 16149 = (7 : ZMod 264586369) ^ (8074 + 8074 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 8074 * (7 : ZMod 264586369) ^ 8074) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 219052363 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 264586369) ^ 32298 = 83136723 := by
        calc
          (7 : ZMod 264586369) ^ 32298 = (7 : ZMod 264586369) ^ (16149 + 16149) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 16149 * (7 : ZMod 264586369) ^ 16149 := by rw [pow_add]
          _ = 83136723 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 264586369) ^ 64596 = 136320525 := by
        calc
          (7 : ZMod 264586369) ^ 64596 = (7 : ZMod 264586369) ^ (32298 + 32298) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 32298 * (7 : ZMod 264586369) ^ 32298 := by rw [pow_add]
          _ = 136320525 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 264586369) ^ 129192 = 260936648 := by
        calc
          (7 : ZMod 264586369) ^ 129192 = (7 : ZMod 264586369) ^ (64596 + 64596) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 64596 * (7 : ZMod 264586369) ^ 64596 := by rw [pow_add]
          _ = 260936648 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 264586369) ^ 258385 = 96759228 := by
        calc
          (7 : ZMod 264586369) ^ 258385 = (7 : ZMod 264586369) ^ (129192 + 129192 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 129192 * (7 : ZMod 264586369) ^ 129192) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 96759228 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 264586369) ^ 516770 = 17805441 := by
        calc
          (7 : ZMod 264586369) ^ 516770 = (7 : ZMod 264586369) ^ (258385 + 258385) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 258385 * (7 : ZMod 264586369) ^ 258385 := by rw [pow_add]
          _ = 17805441 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 264586369) ^ 1033540 = 256382194 := by
        calc
          (7 : ZMod 264586369) ^ 1033540 = (7 : ZMod 264586369) ^ (516770 + 516770) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 516770 * (7 : ZMod 264586369) ^ 516770 := by rw [pow_add]
          _ = 256382194 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 264586369) ^ 2067081 = 145867684 := by
        calc
          (7 : ZMod 264586369) ^ 2067081 = (7 : ZMod 264586369) ^ (1033540 + 1033540 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 1033540 * (7 : ZMod 264586369) ^ 1033540) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 145867684 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 264586369) ^ 4134162 = 27220762 := by
        calc
          (7 : ZMod 264586369) ^ 4134162 = (7 : ZMod 264586369) ^ (2067081 + 2067081) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 2067081 * (7 : ZMod 264586369) ^ 2067081 := by rw [pow_add]
          _ = 27220762 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 264586369) ^ 8268324 = 255444417 := by
        calc
          (7 : ZMod 264586369) ^ 8268324 = (7 : ZMod 264586369) ^ (4134162 + 4134162) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 4134162 * (7 : ZMod 264586369) ^ 4134162 := by rw [pow_add]
          _ = 255444417 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 264586369) ^ 16536648 = 125407905 := by
        calc
          (7 : ZMod 264586369) ^ 16536648 = (7 : ZMod 264586369) ^ (8268324 + 8268324) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 8268324 * (7 : ZMod 264586369) ^ 8268324 := by rw [pow_add]
          _ = 125407905 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 264586369) ^ 33073296 = 9567322 := by
        calc
          (7 : ZMod 264586369) ^ 33073296 = (7 : ZMod 264586369) ^ (16536648 + 16536648) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 16536648 * (7 : ZMod 264586369) ^ 16536648 := by rw [pow_add]
          _ = 9567322 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 264586369) ^ 66146592 = 260482503 := by
        calc
          (7 : ZMod 264586369) ^ 66146592 = (7 : ZMod 264586369) ^ (33073296 + 33073296) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 33073296 * (7 : ZMod 264586369) ^ 33073296 := by rw [pow_add]
          _ = 260482503 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 264586369) ^ 132293184 = 264586368 := by
        calc
          (7 : ZMod 264586369) ^ 132293184 = (7 : ZMod 264586369) ^ (66146592 + 66146592) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 66146592 * (7 : ZMod 264586369) ^ 66146592 := by rw [pow_add]
          _ = 264586368 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 264586369) ^ 264586368 = 1 := by
        calc
          (7 : ZMod 264586369) ^ 264586368 = (7 : ZMod 264586369) ^ (132293184 + 132293184) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 132293184 * (7 : ZMod 264586369) ^ 132293184 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (17, 1), (40531, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (17, 1), (40531, 1)] : List FactorBlock).map factorBlockValue).prod = 264586369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 264586369) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 264586369) ^ 3 = 343 := by
        calc
          (7 : ZMod 264586369) ^ 3 = (7 : ZMod 264586369) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 1 * (7 : ZMod 264586369) ^ 1) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 264586369) ^ 7 = 823543 := by
        calc
          (7 : ZMod 264586369) ^ 7 = (7 : ZMod 264586369) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 3 * (7 : ZMod 264586369) ^ 3) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 264586369) ^ 15 = 88290976 := by
        calc
          (7 : ZMod 264586369) ^ 15 = (7 : ZMod 264586369) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 7 * (7 : ZMod 264586369) ^ 7) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 88290976 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 264586369) ^ 31 = 249724539 := by
        calc
          (7 : ZMod 264586369) ^ 31 = (7 : ZMod 264586369) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 15 * (7 : ZMod 264586369) ^ 15) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 249724539 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 264586369) ^ 63 = 80972468 := by
        calc
          (7 : ZMod 264586369) ^ 63 = (7 : ZMod 264586369) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 31 * (7 : ZMod 264586369) ^ 31) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 80972468 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 264586369) ^ 126 = 126239195 := by
        calc
          (7 : ZMod 264586369) ^ 126 = (7 : ZMod 264586369) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 63 * (7 : ZMod 264586369) ^ 63 := by rw [pow_add]
          _ = 126239195 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 264586369) ^ 252 = 218885638 := by
        calc
          (7 : ZMod 264586369) ^ 252 = (7 : ZMod 264586369) ^ (126 + 126) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 126 * (7 : ZMod 264586369) ^ 126 := by rw [pow_add]
          _ = 218885638 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 264586369) ^ 504 = 124309238 := by
        calc
          (7 : ZMod 264586369) ^ 504 = (7 : ZMod 264586369) ^ (252 + 252) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 252 * (7 : ZMod 264586369) ^ 252 := by rw [pow_add]
          _ = 124309238 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 264586369) ^ 1009 = 133741648 := by
        calc
          (7 : ZMod 264586369) ^ 1009 = (7 : ZMod 264586369) ^ (504 + 504 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 504 * (7 : ZMod 264586369) ^ 504) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 133741648 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 264586369) ^ 2018 = 75044439 := by
        calc
          (7 : ZMod 264586369) ^ 2018 = (7 : ZMod 264586369) ^ (1009 + 1009) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 1009 * (7 : ZMod 264586369) ^ 1009 := by rw [pow_add]
          _ = 75044439 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 264586369) ^ 4037 = 203880123 := by
        calc
          (7 : ZMod 264586369) ^ 4037 = (7 : ZMod 264586369) ^ (2018 + 2018 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 2018 * (7 : ZMod 264586369) ^ 2018) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 203880123 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 264586369) ^ 8074 = 190374163 := by
        calc
          (7 : ZMod 264586369) ^ 8074 = (7 : ZMod 264586369) ^ (4037 + 4037) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 4037 * (7 : ZMod 264586369) ^ 4037 := by rw [pow_add]
          _ = 190374163 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 264586369) ^ 16149 = 219052363 := by
        calc
          (7 : ZMod 264586369) ^ 16149 = (7 : ZMod 264586369) ^ (8074 + 8074 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 8074 * (7 : ZMod 264586369) ^ 8074) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 219052363 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 264586369) ^ 32298 = 83136723 := by
        calc
          (7 : ZMod 264586369) ^ 32298 = (7 : ZMod 264586369) ^ (16149 + 16149) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 16149 * (7 : ZMod 264586369) ^ 16149 := by rw [pow_add]
          _ = 83136723 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 264586369) ^ 64596 = 136320525 := by
        calc
          (7 : ZMod 264586369) ^ 64596 = (7 : ZMod 264586369) ^ (32298 + 32298) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 32298 * (7 : ZMod 264586369) ^ 32298 := by rw [pow_add]
          _ = 136320525 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 264586369) ^ 129192 = 260936648 := by
        calc
          (7 : ZMod 264586369) ^ 129192 = (7 : ZMod 264586369) ^ (64596 + 64596) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 64596 * (7 : ZMod 264586369) ^ 64596 := by rw [pow_add]
          _ = 260936648 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 264586369) ^ 258385 = 96759228 := by
        calc
          (7 : ZMod 264586369) ^ 258385 = (7 : ZMod 264586369) ^ (129192 + 129192 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 129192 * (7 : ZMod 264586369) ^ 129192) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 96759228 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 264586369) ^ 516770 = 17805441 := by
        calc
          (7 : ZMod 264586369) ^ 516770 = (7 : ZMod 264586369) ^ (258385 + 258385) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 258385 * (7 : ZMod 264586369) ^ 258385 := by rw [pow_add]
          _ = 17805441 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 264586369) ^ 1033540 = 256382194 := by
        calc
          (7 : ZMod 264586369) ^ 1033540 = (7 : ZMod 264586369) ^ (516770 + 516770) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 516770 * (7 : ZMod 264586369) ^ 516770 := by rw [pow_add]
          _ = 256382194 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 264586369) ^ 2067081 = 145867684 := by
        calc
          (7 : ZMod 264586369) ^ 2067081 = (7 : ZMod 264586369) ^ (1033540 + 1033540 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 1033540 * (7 : ZMod 264586369) ^ 1033540) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 145867684 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 264586369) ^ 4134162 = 27220762 := by
        calc
          (7 : ZMod 264586369) ^ 4134162 = (7 : ZMod 264586369) ^ (2067081 + 2067081) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 2067081 * (7 : ZMod 264586369) ^ 2067081 := by rw [pow_add]
          _ = 27220762 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 264586369) ^ 8268324 = 255444417 := by
        calc
          (7 : ZMod 264586369) ^ 8268324 = (7 : ZMod 264586369) ^ (4134162 + 4134162) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 4134162 * (7 : ZMod 264586369) ^ 4134162 := by rw [pow_add]
          _ = 255444417 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 264586369) ^ 16536648 = 125407905 := by
        calc
          (7 : ZMod 264586369) ^ 16536648 = (7 : ZMod 264586369) ^ (8268324 + 8268324) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 8268324 * (7 : ZMod 264586369) ^ 8268324 := by rw [pow_add]
          _ = 125407905 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 264586369) ^ 33073296 = 9567322 := by
        calc
          (7 : ZMod 264586369) ^ 33073296 = (7 : ZMod 264586369) ^ (16536648 + 16536648) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 16536648 * (7 : ZMod 264586369) ^ 16536648 := by rw [pow_add]
          _ = 9567322 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 264586369) ^ 66146592 = 260482503 := by
        calc
          (7 : ZMod 264586369) ^ 66146592 = (7 : ZMod 264586369) ^ (33073296 + 33073296) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 33073296 * (7 : ZMod 264586369) ^ 33073296 := by rw [pow_add]
          _ = 260482503 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 264586369) ^ 132293184 = 264586368 := by
        calc
          (7 : ZMod 264586369) ^ 132293184 = (7 : ZMod 264586369) ^ (66146592 + 66146592) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 66146592 * (7 : ZMod 264586369) ^ 66146592 := by rw [pow_add]
          _ = 264586368 := by rw [factor_0_25]; decide
      change (7 : ZMod 264586369) ^ 132293184 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (7 : ZMod 264586369) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 264586369) ^ 2 = 49 := by
        calc
          (7 : ZMod 264586369) ^ 2 = (7 : ZMod 264586369) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 1 * (7 : ZMod 264586369) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 264586369) ^ 5 = 16807 := by
        calc
          (7 : ZMod 264586369) ^ 5 = (7 : ZMod 264586369) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 2 * (7 : ZMod 264586369) ^ 2) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 264586369) ^ 10 = 17888880 := by
        calc
          (7 : ZMod 264586369) ^ 10 = (7 : ZMod 264586369) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 5 * (7 : ZMod 264586369) ^ 5 := by rw [pow_add]
          _ = 17888880 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 264586369) ^ 21 = 213361222 := by
        calc
          (7 : ZMod 264586369) ^ 21 = (7 : ZMod 264586369) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 10 * (7 : ZMod 264586369) ^ 10) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 213361222 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 264586369) ^ 42 = 214591784 := by
        calc
          (7 : ZMod 264586369) ^ 42 = (7 : ZMod 264586369) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 21 * (7 : ZMod 264586369) ^ 21 := by rw [pow_add]
          _ = 214591784 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 264586369) ^ 84 = 2399209 := by
        calc
          (7 : ZMod 264586369) ^ 84 = (7 : ZMod 264586369) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 42 * (7 : ZMod 264586369) ^ 42 := by rw [pow_add]
          _ = 2399209 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 264586369) ^ 168 = 127368086 := by
        calc
          (7 : ZMod 264586369) ^ 168 = (7 : ZMod 264586369) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 84 * (7 : ZMod 264586369) ^ 84 := by rw [pow_add]
          _ = 127368086 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 264586369) ^ 336 = 44537297 := by
        calc
          (7 : ZMod 264586369) ^ 336 = (7 : ZMod 264586369) ^ (168 + 168) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 168 * (7 : ZMod 264586369) ^ 168 := by rw [pow_add]
          _ = 44537297 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 264586369) ^ 672 = 153555703 := by
        calc
          (7 : ZMod 264586369) ^ 672 = (7 : ZMod 264586369) ^ (336 + 336) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 336 * (7 : ZMod 264586369) ^ 336 := by rw [pow_add]
          _ = 153555703 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 264586369) ^ 1345 = 126655871 := by
        calc
          (7 : ZMod 264586369) ^ 1345 = (7 : ZMod 264586369) ^ (672 + 672 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 672 * (7 : ZMod 264586369) ^ 672) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 126655871 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 264586369) ^ 2691 = 232095283 := by
        calc
          (7 : ZMod 264586369) ^ 2691 = (7 : ZMod 264586369) ^ (1345 + 1345 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 1345 * (7 : ZMod 264586369) ^ 1345) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 232095283 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 264586369) ^ 5383 = 73204426 := by
        calc
          (7 : ZMod 264586369) ^ 5383 = (7 : ZMod 264586369) ^ (2691 + 2691 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 2691 * (7 : ZMod 264586369) ^ 2691) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 73204426 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 264586369) ^ 10766 = 118773468 := by
        calc
          (7 : ZMod 264586369) ^ 10766 = (7 : ZMod 264586369) ^ (5383 + 5383) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 5383 * (7 : ZMod 264586369) ^ 5383 := by rw [pow_add]
          _ = 118773468 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 264586369) ^ 21532 = 54315724 := by
        calc
          (7 : ZMod 264586369) ^ 21532 = (7 : ZMod 264586369) ^ (10766 + 10766) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 10766 * (7 : ZMod 264586369) ^ 10766 := by rw [pow_add]
          _ = 54315724 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 264586369) ^ 43064 = 62774782 := by
        calc
          (7 : ZMod 264586369) ^ 43064 = (7 : ZMod 264586369) ^ (21532 + 21532) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 21532 * (7 : ZMod 264586369) ^ 21532 := by rw [pow_add]
          _ = 62774782 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 264586369) ^ 86128 = 76135796 := by
        calc
          (7 : ZMod 264586369) ^ 86128 = (7 : ZMod 264586369) ^ (43064 + 43064) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 43064 * (7 : ZMod 264586369) ^ 43064 := by rw [pow_add]
          _ = 76135796 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 264586369) ^ 172256 = 188508658 := by
        calc
          (7 : ZMod 264586369) ^ 172256 = (7 : ZMod 264586369) ^ (86128 + 86128) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 86128 * (7 : ZMod 264586369) ^ 86128 := by rw [pow_add]
          _ = 188508658 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 264586369) ^ 344513 = 143322886 := by
        calc
          (7 : ZMod 264586369) ^ 344513 = (7 : ZMod 264586369) ^ (172256 + 172256 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 172256 * (7 : ZMod 264586369) ^ 172256) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 143322886 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 264586369) ^ 689027 = 47837262 := by
        calc
          (7 : ZMod 264586369) ^ 689027 = (7 : ZMod 264586369) ^ (344513 + 344513 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 344513 * (7 : ZMod 264586369) ^ 344513) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 47837262 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 264586369) ^ 1378054 = 98971179 := by
        calc
          (7 : ZMod 264586369) ^ 1378054 = (7 : ZMod 264586369) ^ (689027 + 689027) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 689027 * (7 : ZMod 264586369) ^ 689027 := by rw [pow_add]
          _ = 98971179 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 264586369) ^ 2756108 = 236668370 := by
        calc
          (7 : ZMod 264586369) ^ 2756108 = (7 : ZMod 264586369) ^ (1378054 + 1378054) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 1378054 * (7 : ZMod 264586369) ^ 1378054 := by rw [pow_add]
          _ = 236668370 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 264586369) ^ 5512216 = 111159336 := by
        calc
          (7 : ZMod 264586369) ^ 5512216 = (7 : ZMod 264586369) ^ (2756108 + 2756108) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 2756108 * (7 : ZMod 264586369) ^ 2756108 := by rw [pow_add]
          _ = 111159336 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 264586369) ^ 11024432 = 232702006 := by
        calc
          (7 : ZMod 264586369) ^ 11024432 = (7 : ZMod 264586369) ^ (5512216 + 5512216) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 5512216 * (7 : ZMod 264586369) ^ 5512216 := by rw [pow_add]
          _ = 232702006 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 264586369) ^ 22048864 = 71311770 := by
        calc
          (7 : ZMod 264586369) ^ 22048864 = (7 : ZMod 264586369) ^ (11024432 + 11024432) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 11024432 * (7 : ZMod 264586369) ^ 11024432 := by rw [pow_add]
          _ = 71311770 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 264586369) ^ 44097728 = 7307070 := by
        calc
          (7 : ZMod 264586369) ^ 44097728 = (7 : ZMod 264586369) ^ (22048864 + 22048864) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 22048864 * (7 : ZMod 264586369) ^ 22048864 := by rw [pow_add]
          _ = 7307070 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 264586369) ^ 88195456 = 7307069 := by
        calc
          (7 : ZMod 264586369) ^ 88195456 = (7 : ZMod 264586369) ^ (44097728 + 44097728) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 44097728 * (7 : ZMod 264586369) ^ 44097728 := by rw [pow_add]
          _ = 7307069 := by rw [factor_1_25]; decide
      change (7 : ZMod 264586369) ^ 88195456 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (7 : ZMod 264586369) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 264586369) ^ 3 = 343 := by
        calc
          (7 : ZMod 264586369) ^ 3 = (7 : ZMod 264586369) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 1 * (7 : ZMod 264586369) ^ 1) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 264586369) ^ 7 = 823543 := by
        calc
          (7 : ZMod 264586369) ^ 7 = (7 : ZMod 264586369) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 3 * (7 : ZMod 264586369) ^ 3) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 264586369) ^ 14 = 88209102 := by
        calc
          (7 : ZMod 264586369) ^ 14 = (7 : ZMod 264586369) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 7 * (7 : ZMod 264586369) ^ 7 := by rw [pow_add]
          _ = 88209102 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 264586369) ^ 29 = 215685570 := by
        calc
          (7 : ZMod 264586369) ^ 29 = (7 : ZMod 264586369) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 14 * (7 : ZMod 264586369) ^ 14) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 215685570 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 264586369) ^ 59 = 53039157 := by
        calc
          (7 : ZMod 264586369) ^ 59 = (7 : ZMod 264586369) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 29 * (7 : ZMod 264586369) ^ 29) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 53039157 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 264586369) ^ 118 = 49261233 := by
        calc
          (7 : ZMod 264586369) ^ 118 = (7 : ZMod 264586369) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 59 * (7 : ZMod 264586369) ^ 59 := by rw [pow_add]
          _ = 49261233 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 264586369) ^ 237 = 254643554 := by
        calc
          (7 : ZMod 264586369) ^ 237 = (7 : ZMod 264586369) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 118 * (7 : ZMod 264586369) ^ 118) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 254643554 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 264586369) ^ 474 = 48383803 := by
        calc
          (7 : ZMod 264586369) ^ 474 = (7 : ZMod 264586369) ^ (237 + 237) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 237 * (7 : ZMod 264586369) ^ 237 := by rw [pow_add]
          _ = 48383803 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 264586369) ^ 949 = 66761649 := by
        calc
          (7 : ZMod 264586369) ^ 949 = (7 : ZMod 264586369) ^ (474 + 474 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 474 * (7 : ZMod 264586369) ^ 474) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 66761649 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 264586369) ^ 1899 = 99795740 := by
        calc
          (7 : ZMod 264586369) ^ 1899 = (7 : ZMod 264586369) ^ (949 + 949 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 949 * (7 : ZMod 264586369) ^ 949) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 99795740 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 264586369) ^ 3799 = 23577031 := by
        calc
          (7 : ZMod 264586369) ^ 3799 = (7 : ZMod 264586369) ^ (1899 + 1899 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 1899 * (7 : ZMod 264586369) ^ 1899) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 23577031 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 264586369) ^ 7599 = 62280869 := by
        calc
          (7 : ZMod 264586369) ^ 7599 = (7 : ZMod 264586369) ^ (3799 + 3799 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 3799 * (7 : ZMod 264586369) ^ 3799) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 62280869 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 264586369) ^ 15199 = 127994311 := by
        calc
          (7 : ZMod 264586369) ^ 15199 = (7 : ZMod 264586369) ^ (7599 + 7599 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 7599 * (7 : ZMod 264586369) ^ 7599) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 127994311 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 264586369) ^ 30398 = 212279605 := by
        calc
          (7 : ZMod 264586369) ^ 30398 = (7 : ZMod 264586369) ^ (15199 + 15199) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 15199 * (7 : ZMod 264586369) ^ 15199 := by rw [pow_add]
          _ = 212279605 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 264586369) ^ 60796 = 142274525 := by
        calc
          (7 : ZMod 264586369) ^ 60796 = (7 : ZMod 264586369) ^ (30398 + 30398) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 30398 * (7 : ZMod 264586369) ^ 30398 := by rw [pow_add]
          _ = 142274525 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 264586369) ^ 121593 = 36634199 := by
        calc
          (7 : ZMod 264586369) ^ 121593 = (7 : ZMod 264586369) ^ (60796 + 60796 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 60796 * (7 : ZMod 264586369) ^ 60796) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 36634199 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 264586369) ^ 243186 = 186442842 := by
        calc
          (7 : ZMod 264586369) ^ 243186 = (7 : ZMod 264586369) ^ (121593 + 121593) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 121593 * (7 : ZMod 264586369) ^ 121593 := by rw [pow_add]
          _ = 186442842 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 264586369) ^ 486372 = 41180102 := by
        calc
          (7 : ZMod 264586369) ^ 486372 = (7 : ZMod 264586369) ^ (243186 + 243186) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 243186 * (7 : ZMod 264586369) ^ 243186 := by rw [pow_add]
          _ = 41180102 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 264586369) ^ 972744 = 86044416 := by
        calc
          (7 : ZMod 264586369) ^ 972744 = (7 : ZMod 264586369) ^ (486372 + 486372) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 486372 * (7 : ZMod 264586369) ^ 486372 := by rw [pow_add]
          _ = 86044416 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 264586369) ^ 1945488 = 35086982 := by
        calc
          (7 : ZMod 264586369) ^ 1945488 = (7 : ZMod 264586369) ^ (972744 + 972744) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 972744 * (7 : ZMod 264586369) ^ 972744 := by rw [pow_add]
          _ = 35086982 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 264586369) ^ 3890976 = 8270903 := by
        calc
          (7 : ZMod 264586369) ^ 3890976 = (7 : ZMod 264586369) ^ (1945488 + 1945488) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 1945488 * (7 : ZMod 264586369) ^ 1945488 := by rw [pow_add]
          _ = 8270903 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 264586369) ^ 7781952 = 89075935 := by
        calc
          (7 : ZMod 264586369) ^ 7781952 = (7 : ZMod 264586369) ^ (3890976 + 3890976) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 3890976 * (7 : ZMod 264586369) ^ 3890976 := by rw [pow_add]
          _ = 89075935 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 264586369) ^ 15563904 = 63418256 := by
        calc
          (7 : ZMod 264586369) ^ 15563904 = (7 : ZMod 264586369) ^ (7781952 + 7781952) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 7781952 * (7 : ZMod 264586369) ^ 7781952 := by rw [pow_add]
          _ = 63418256 := by rw [factor_2_22]; decide
      change (7 : ZMod 264586369) ^ 15563904 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (7 : ZMod 264586369) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 264586369) ^ 3 = 343 := by
        calc
          (7 : ZMod 264586369) ^ 3 = (7 : ZMod 264586369) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 1 * (7 : ZMod 264586369) ^ 1) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 264586369) ^ 6 = 117649 := by
        calc
          (7 : ZMod 264586369) ^ 6 = (7 : ZMod 264586369) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 3 * (7 : ZMod 264586369) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 264586369) ^ 12 = 82796013 := by
        calc
          (7 : ZMod 264586369) ^ 12 = (7 : ZMod 264586369) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 6 * (7 : ZMod 264586369) ^ 6 := by rw [pow_add]
          _ = 82796013 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 264586369) ^ 25 = 41083638 := by
        calc
          (7 : ZMod 264586369) ^ 25 = (7 : ZMod 264586369) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 12 * (7 : ZMod 264586369) ^ 12) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 41083638 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 264586369) ^ 51 = 232470359 := by
        calc
          (7 : ZMod 264586369) ^ 51 = (7 : ZMod 264586369) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = ((7 : ZMod 264586369) ^ 25 * (7 : ZMod 264586369) ^ 25) * (7 : ZMod 264586369) := by rw [pow_succ, pow_add]
          _ = 232470359 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 264586369) ^ 102 = 262288293 := by
        calc
          (7 : ZMod 264586369) ^ 102 = (7 : ZMod 264586369) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 51 * (7 : ZMod 264586369) ^ 51 := by rw [pow_add]
          _ = 262288293 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 264586369) ^ 204 = 9376536 := by
        calc
          (7 : ZMod 264586369) ^ 204 = (7 : ZMod 264586369) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 102 * (7 : ZMod 264586369) ^ 102 := by rw [pow_add]
          _ = 9376536 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 264586369) ^ 408 = 22804286 := by
        calc
          (7 : ZMod 264586369) ^ 408 = (7 : ZMod 264586369) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 204 * (7 : ZMod 264586369) ^ 204 := by rw [pow_add]
          _ = 22804286 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 264586369) ^ 816 = 212223211 := by
        calc
          (7 : ZMod 264586369) ^ 816 = (7 : ZMod 264586369) ^ (408 + 408) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 408 * (7 : ZMod 264586369) ^ 408 := by rw [pow_add]
          _ = 212223211 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 264586369) ^ 1632 = 240549772 := by
        calc
          (7 : ZMod 264586369) ^ 1632 = (7 : ZMod 264586369) ^ (816 + 816) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 816 * (7 : ZMod 264586369) ^ 816 := by rw [pow_add]
          _ = 240549772 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 264586369) ^ 3264 = 56160046 := by
        calc
          (7 : ZMod 264586369) ^ 3264 = (7 : ZMod 264586369) ^ (1632 + 1632) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 1632 * (7 : ZMod 264586369) ^ 1632 := by rw [pow_add]
          _ = 56160046 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 264586369) ^ 6528 = 20226833 := by
        calc
          (7 : ZMod 264586369) ^ 6528 = (7 : ZMod 264586369) ^ (3264 + 3264) :=
            congrArg (fun n : ℕ => (7 : ZMod 264586369) ^ n) (by norm_num)
          _ = (7 : ZMod 264586369) ^ 3264 * (7 : ZMod 264586369) ^ 3264 := by rw [pow_add]
          _ = 20226833 := by rw [factor_3_11]; decide
      change (7 : ZMod 264586369) ^ 6528 ≠ 1
      rw [factor_3_12]
      decide

#print axioms prime_lucas_264586369

end TotientTailPeriodKiller
end Erdos249257
