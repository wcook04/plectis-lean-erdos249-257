import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_121260691 : Nat.Prime 121260691 := by
  apply lucas_primality 121260691 (10 : ZMod 121260691)
  ·
      have fermat_0 : (10 : ZMod 121260691) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 121260691) ^ 3 = 1000 := by
        calc
          (10 : ZMod 121260691) ^ 3 = (10 : ZMod 121260691) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 1 * (10 : ZMod 121260691) ^ 1) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 121260691) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 121260691) ^ 7 = (10 : ZMod 121260691) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 3 * (10 : ZMod 121260691) ^ 3) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 121260691) ^ 14 = 67213721 := by
        calc
          (10 : ZMod 121260691) ^ 14 = (10 : ZMod 121260691) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 7 * (10 : ZMod 121260691) ^ 7 := by rw [pow_add]
          _ = 67213721 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 121260691) ^ 28 = 109633335 := by
        calc
          (10 : ZMod 121260691) ^ 28 = (10 : ZMod 121260691) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 14 * (10 : ZMod 121260691) ^ 14 := by rw [pow_add]
          _ = 109633335 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 121260691) ^ 57 = 78662637 := by
        calc
          (10 : ZMod 121260691) ^ 57 = (10 : ZMod 121260691) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 28 * (10 : ZMod 121260691) ^ 28) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 78662637 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 121260691) ^ 115 = 47484391 := by
        calc
          (10 : ZMod 121260691) ^ 115 = (10 : ZMod 121260691) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 57 * (10 : ZMod 121260691) ^ 57) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 47484391 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 121260691) ^ 231 = 89982319 := by
        calc
          (10 : ZMod 121260691) ^ 231 = (10 : ZMod 121260691) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 115 * (10 : ZMod 121260691) ^ 115) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 89982319 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 121260691) ^ 462 = 85772671 := by
        calc
          (10 : ZMod 121260691) ^ 462 = (10 : ZMod 121260691) ^ (231 + 231) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 231 * (10 : ZMod 121260691) ^ 231 := by rw [pow_add]
          _ = 85772671 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 121260691) ^ 925 = 81520723 := by
        calc
          (10 : ZMod 121260691) ^ 925 = (10 : ZMod 121260691) ^ (462 + 462 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 462 * (10 : ZMod 121260691) ^ 462) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 81520723 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 121260691) ^ 1850 = 12571886 := by
        calc
          (10 : ZMod 121260691) ^ 1850 = (10 : ZMod 121260691) ^ (925 + 925) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 925 * (10 : ZMod 121260691) ^ 925 := by rw [pow_add]
          _ = 12571886 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 121260691) ^ 3700 = 41601377 := by
        calc
          (10 : ZMod 121260691) ^ 3700 = (10 : ZMod 121260691) ^ (1850 + 1850) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 1850 * (10 : ZMod 121260691) ^ 1850 := by rw [pow_add]
          _ = 41601377 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 121260691) ^ 7401 = 58929048 := by
        calc
          (10 : ZMod 121260691) ^ 7401 = (10 : ZMod 121260691) ^ (3700 + 3700 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 3700 * (10 : ZMod 121260691) ^ 3700) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 58929048 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 121260691) ^ 14802 = 72065200 := by
        calc
          (10 : ZMod 121260691) ^ 14802 = (10 : ZMod 121260691) ^ (7401 + 7401) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 7401 * (10 : ZMod 121260691) ^ 7401 := by rw [pow_add]
          _ = 72065200 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 121260691) ^ 29604 = 39603279 := by
        calc
          (10 : ZMod 121260691) ^ 29604 = (10 : ZMod 121260691) ^ (14802 + 14802) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 14802 * (10 : ZMod 121260691) ^ 14802 := by rw [pow_add]
          _ = 39603279 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 121260691) ^ 59209 = 14164992 := by
        calc
          (10 : ZMod 121260691) ^ 59209 = (10 : ZMod 121260691) ^ (29604 + 29604 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 29604 * (10 : ZMod 121260691) ^ 29604) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 14164992 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 121260691) ^ 118418 = 85740330 := by
        calc
          (10 : ZMod 121260691) ^ 118418 = (10 : ZMod 121260691) ^ (59209 + 59209) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 59209 * (10 : ZMod 121260691) ^ 59209 := by rw [pow_add]
          _ = 85740330 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 121260691) ^ 236837 = 67315589 := by
        calc
          (10 : ZMod 121260691) ^ 236837 = (10 : ZMod 121260691) ^ (118418 + 118418 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 118418 * (10 : ZMod 121260691) ^ 118418) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 67315589 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 121260691) ^ 473674 = 64391050 := by
        calc
          (10 : ZMod 121260691) ^ 473674 = (10 : ZMod 121260691) ^ (236837 + 236837) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 236837 * (10 : ZMod 121260691) ^ 236837 := by rw [pow_add]
          _ = 64391050 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 121260691) ^ 947349 = 32345046 := by
        calc
          (10 : ZMod 121260691) ^ 947349 = (10 : ZMod 121260691) ^ (473674 + 473674 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 473674 * (10 : ZMod 121260691) ^ 473674) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 32345046 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 121260691) ^ 1894698 = 45655197 := by
        calc
          (10 : ZMod 121260691) ^ 1894698 = (10 : ZMod 121260691) ^ (947349 + 947349) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 947349 * (10 : ZMod 121260691) ^ 947349 := by rw [pow_add]
          _ = 45655197 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 121260691) ^ 3789396 = 67622392 := by
        calc
          (10 : ZMod 121260691) ^ 3789396 = (10 : ZMod 121260691) ^ (1894698 + 1894698) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 1894698 * (10 : ZMod 121260691) ^ 1894698 := by rw [pow_add]
          _ = 67622392 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 121260691) ^ 7578793 = 111525195 := by
        calc
          (10 : ZMod 121260691) ^ 7578793 = (10 : ZMod 121260691) ^ (3789396 + 3789396 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 3789396 * (10 : ZMod 121260691) ^ 3789396) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 111525195 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 121260691) ^ 15157586 = 101066596 := by
        calc
          (10 : ZMod 121260691) ^ 15157586 = (10 : ZMod 121260691) ^ (7578793 + 7578793) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 7578793 * (10 : ZMod 121260691) ^ 7578793 := by rw [pow_add]
          _ = 101066596 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 121260691) ^ 30315172 = 71386351 := by
        calc
          (10 : ZMod 121260691) ^ 30315172 = (10 : ZMod 121260691) ^ (15157586 + 15157586) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 15157586 * (10 : ZMod 121260691) ^ 15157586 := by rw [pow_add]
          _ = 71386351 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 121260691) ^ 60630345 = 121260690 := by
        calc
          (10 : ZMod 121260691) ^ 60630345 = (10 : ZMod 121260691) ^ (30315172 + 30315172 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 30315172 * (10 : ZMod 121260691) ^ 30315172) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 121260690 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 121260691) ^ 121260690 = 1 := by
        calc
          (10 : ZMod 121260691) ^ 121260690 = (10 : ZMod 121260691) ^ (60630345 + 60630345) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 60630345 * (10 : ZMod 121260691) ^ 60630345 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (1347341, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (1347341, 1)] : List FactorBlock).map factorBlockValue).prod = 121260691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 121260691) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 121260691) ^ 3 = 1000 := by
        calc
          (10 : ZMod 121260691) ^ 3 = (10 : ZMod 121260691) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 1 * (10 : ZMod 121260691) ^ 1) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 121260691) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 121260691) ^ 7 = (10 : ZMod 121260691) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 3 * (10 : ZMod 121260691) ^ 3) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 121260691) ^ 14 = 67213721 := by
        calc
          (10 : ZMod 121260691) ^ 14 = (10 : ZMod 121260691) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 7 * (10 : ZMod 121260691) ^ 7 := by rw [pow_add]
          _ = 67213721 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 121260691) ^ 28 = 109633335 := by
        calc
          (10 : ZMod 121260691) ^ 28 = (10 : ZMod 121260691) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 14 * (10 : ZMod 121260691) ^ 14 := by rw [pow_add]
          _ = 109633335 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 121260691) ^ 57 = 78662637 := by
        calc
          (10 : ZMod 121260691) ^ 57 = (10 : ZMod 121260691) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 28 * (10 : ZMod 121260691) ^ 28) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 78662637 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 121260691) ^ 115 = 47484391 := by
        calc
          (10 : ZMod 121260691) ^ 115 = (10 : ZMod 121260691) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 57 * (10 : ZMod 121260691) ^ 57) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 47484391 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 121260691) ^ 231 = 89982319 := by
        calc
          (10 : ZMod 121260691) ^ 231 = (10 : ZMod 121260691) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 115 * (10 : ZMod 121260691) ^ 115) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 89982319 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 121260691) ^ 462 = 85772671 := by
        calc
          (10 : ZMod 121260691) ^ 462 = (10 : ZMod 121260691) ^ (231 + 231) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 231 * (10 : ZMod 121260691) ^ 231 := by rw [pow_add]
          _ = 85772671 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 121260691) ^ 925 = 81520723 := by
        calc
          (10 : ZMod 121260691) ^ 925 = (10 : ZMod 121260691) ^ (462 + 462 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 462 * (10 : ZMod 121260691) ^ 462) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 81520723 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 121260691) ^ 1850 = 12571886 := by
        calc
          (10 : ZMod 121260691) ^ 1850 = (10 : ZMod 121260691) ^ (925 + 925) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 925 * (10 : ZMod 121260691) ^ 925 := by rw [pow_add]
          _ = 12571886 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 121260691) ^ 3700 = 41601377 := by
        calc
          (10 : ZMod 121260691) ^ 3700 = (10 : ZMod 121260691) ^ (1850 + 1850) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 1850 * (10 : ZMod 121260691) ^ 1850 := by rw [pow_add]
          _ = 41601377 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 121260691) ^ 7401 = 58929048 := by
        calc
          (10 : ZMod 121260691) ^ 7401 = (10 : ZMod 121260691) ^ (3700 + 3700 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 3700 * (10 : ZMod 121260691) ^ 3700) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 58929048 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 121260691) ^ 14802 = 72065200 := by
        calc
          (10 : ZMod 121260691) ^ 14802 = (10 : ZMod 121260691) ^ (7401 + 7401) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 7401 * (10 : ZMod 121260691) ^ 7401 := by rw [pow_add]
          _ = 72065200 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 121260691) ^ 29604 = 39603279 := by
        calc
          (10 : ZMod 121260691) ^ 29604 = (10 : ZMod 121260691) ^ (14802 + 14802) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 14802 * (10 : ZMod 121260691) ^ 14802 := by rw [pow_add]
          _ = 39603279 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 121260691) ^ 59209 = 14164992 := by
        calc
          (10 : ZMod 121260691) ^ 59209 = (10 : ZMod 121260691) ^ (29604 + 29604 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 29604 * (10 : ZMod 121260691) ^ 29604) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 14164992 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 121260691) ^ 118418 = 85740330 := by
        calc
          (10 : ZMod 121260691) ^ 118418 = (10 : ZMod 121260691) ^ (59209 + 59209) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 59209 * (10 : ZMod 121260691) ^ 59209 := by rw [pow_add]
          _ = 85740330 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 121260691) ^ 236837 = 67315589 := by
        calc
          (10 : ZMod 121260691) ^ 236837 = (10 : ZMod 121260691) ^ (118418 + 118418 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 118418 * (10 : ZMod 121260691) ^ 118418) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 67315589 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 121260691) ^ 473674 = 64391050 := by
        calc
          (10 : ZMod 121260691) ^ 473674 = (10 : ZMod 121260691) ^ (236837 + 236837) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 236837 * (10 : ZMod 121260691) ^ 236837 := by rw [pow_add]
          _ = 64391050 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 121260691) ^ 947349 = 32345046 := by
        calc
          (10 : ZMod 121260691) ^ 947349 = (10 : ZMod 121260691) ^ (473674 + 473674 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 473674 * (10 : ZMod 121260691) ^ 473674) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 32345046 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 121260691) ^ 1894698 = 45655197 := by
        calc
          (10 : ZMod 121260691) ^ 1894698 = (10 : ZMod 121260691) ^ (947349 + 947349) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 947349 * (10 : ZMod 121260691) ^ 947349 := by rw [pow_add]
          _ = 45655197 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 121260691) ^ 3789396 = 67622392 := by
        calc
          (10 : ZMod 121260691) ^ 3789396 = (10 : ZMod 121260691) ^ (1894698 + 1894698) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 1894698 * (10 : ZMod 121260691) ^ 1894698 := by rw [pow_add]
          _ = 67622392 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 121260691) ^ 7578793 = 111525195 := by
        calc
          (10 : ZMod 121260691) ^ 7578793 = (10 : ZMod 121260691) ^ (3789396 + 3789396 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 3789396 * (10 : ZMod 121260691) ^ 3789396) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 111525195 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 121260691) ^ 15157586 = 101066596 := by
        calc
          (10 : ZMod 121260691) ^ 15157586 = (10 : ZMod 121260691) ^ (7578793 + 7578793) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 7578793 * (10 : ZMod 121260691) ^ 7578793 := by rw [pow_add]
          _ = 101066596 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 121260691) ^ 30315172 = 71386351 := by
        calc
          (10 : ZMod 121260691) ^ 30315172 = (10 : ZMod 121260691) ^ (15157586 + 15157586) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 15157586 * (10 : ZMod 121260691) ^ 15157586 := by rw [pow_add]
          _ = 71386351 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 121260691) ^ 60630345 = 121260690 := by
        calc
          (10 : ZMod 121260691) ^ 60630345 = (10 : ZMod 121260691) ^ (30315172 + 30315172 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 30315172 * (10 : ZMod 121260691) ^ 30315172) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 121260690 := by rw [factor_0_24]; decide
      change (10 : ZMod 121260691) ^ 60630345 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (10 : ZMod 121260691) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 121260691) ^ 2 = 100 := by
        calc
          (10 : ZMod 121260691) ^ 2 = (10 : ZMod 121260691) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 1 * (10 : ZMod 121260691) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 121260691) ^ 4 = 10000 := by
        calc
          (10 : ZMod 121260691) ^ 4 = (10 : ZMod 121260691) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 2 * (10 : ZMod 121260691) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 121260691) ^ 9 = 29914472 := by
        calc
          (10 : ZMod 121260691) ^ 9 = (10 : ZMod 121260691) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 4 * (10 : ZMod 121260691) ^ 4) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 29914472 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 121260691) ^ 19 = 13258561 := by
        calc
          (10 : ZMod 121260691) ^ 19 = (10 : ZMod 121260691) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 9 * (10 : ZMod 121260691) ^ 9) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 13258561 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 121260691) ^ 38 = 120001150 := by
        calc
          (10 : ZMod 121260691) ^ 38 = (10 : ZMod 121260691) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 19 * (10 : ZMod 121260691) ^ 19 := by rw [pow_add]
          _ = 120001150 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 121260691) ^ 77 = 20363971 := by
        calc
          (10 : ZMod 121260691) ^ 77 = (10 : ZMod 121260691) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 38 * (10 : ZMod 121260691) ^ 38) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 20363971 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 121260691) ^ 154 = 2204238 := by
        calc
          (10 : ZMod 121260691) ^ 154 = (10 : ZMod 121260691) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 77 * (10 : ZMod 121260691) ^ 77 := by rw [pow_add]
          _ = 2204238 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 121260691) ^ 308 = 113054347 := by
        calc
          (10 : ZMod 121260691) ^ 308 = (10 : ZMod 121260691) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 154 * (10 : ZMod 121260691) ^ 154 := by rw [pow_add]
          _ = 113054347 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 121260691) ^ 616 = 16928430 := by
        calc
          (10 : ZMod 121260691) ^ 616 = (10 : ZMod 121260691) ^ (308 + 308) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 308 * (10 : ZMod 121260691) ^ 308 := by rw [pow_add]
          _ = 16928430 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 121260691) ^ 1233 = 11713991 := by
        calc
          (10 : ZMod 121260691) ^ 1233 = (10 : ZMod 121260691) ^ (616 + 616 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 616 * (10 : ZMod 121260691) ^ 616) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 11713991 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 121260691) ^ 2467 = 58022854 := by
        calc
          (10 : ZMod 121260691) ^ 2467 = (10 : ZMod 121260691) ^ (1233 + 1233 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 1233 * (10 : ZMod 121260691) ^ 1233) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 58022854 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 121260691) ^ 4934 = 76554066 := by
        calc
          (10 : ZMod 121260691) ^ 4934 = (10 : ZMod 121260691) ^ (2467 + 2467) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 2467 * (10 : ZMod 121260691) ^ 2467 := by rw [pow_add]
          _ = 76554066 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 121260691) ^ 9868 = 69226541 := by
        calc
          (10 : ZMod 121260691) ^ 9868 = (10 : ZMod 121260691) ^ (4934 + 4934) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 4934 * (10 : ZMod 121260691) ^ 4934 := by rw [pow_add]
          _ = 69226541 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 121260691) ^ 19736 = 39943667 := by
        calc
          (10 : ZMod 121260691) ^ 19736 = (10 : ZMod 121260691) ^ (9868 + 9868) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 9868 * (10 : ZMod 121260691) ^ 9868 := by rw [pow_add]
          _ = 39943667 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 121260691) ^ 39472 = 18283255 := by
        calc
          (10 : ZMod 121260691) ^ 39472 = (10 : ZMod 121260691) ^ (19736 + 19736) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 19736 * (10 : ZMod 121260691) ^ 19736 := by rw [pow_add]
          _ = 18283255 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 121260691) ^ 78945 = 66863810 := by
        calc
          (10 : ZMod 121260691) ^ 78945 = (10 : ZMod 121260691) ^ (39472 + 39472 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 39472 * (10 : ZMod 121260691) ^ 39472) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 66863810 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 121260691) ^ 157891 = 10976935 := by
        calc
          (10 : ZMod 121260691) ^ 157891 = (10 : ZMod 121260691) ^ (78945 + 78945 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 78945 * (10 : ZMod 121260691) ^ 78945) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 10976935 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 121260691) ^ 315783 = 32943241 := by
        calc
          (10 : ZMod 121260691) ^ 315783 = (10 : ZMod 121260691) ^ (157891 + 157891 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 157891 * (10 : ZMod 121260691) ^ 157891) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 32943241 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 121260691) ^ 631566 = 14182646 := by
        calc
          (10 : ZMod 121260691) ^ 631566 = (10 : ZMod 121260691) ^ (315783 + 315783) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 315783 * (10 : ZMod 121260691) ^ 315783 := by rw [pow_add]
          _ = 14182646 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 121260691) ^ 1263132 = 92069825 := by
        calc
          (10 : ZMod 121260691) ^ 1263132 = (10 : ZMod 121260691) ^ (631566 + 631566) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 631566 * (10 : ZMod 121260691) ^ 631566 := by rw [pow_add]
          _ = 92069825 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 121260691) ^ 2526264 = 21488732 := by
        calc
          (10 : ZMod 121260691) ^ 2526264 = (10 : ZMod 121260691) ^ (1263132 + 1263132) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 1263132 * (10 : ZMod 121260691) ^ 1263132 := by rw [pow_add]
          _ = 21488732 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 121260691) ^ 5052528 = 41212184 := by
        calc
          (10 : ZMod 121260691) ^ 5052528 = (10 : ZMod 121260691) ^ (2526264 + 2526264) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 2526264 * (10 : ZMod 121260691) ^ 2526264 := by rw [pow_add]
          _ = 41212184 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 121260691) ^ 10105057 = 87588386 := by
        calc
          (10 : ZMod 121260691) ^ 10105057 = (10 : ZMod 121260691) ^ (5052528 + 5052528 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 5052528 * (10 : ZMod 121260691) ^ 5052528) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 87588386 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 121260691) ^ 20210115 = 60561357 := by
        calc
          (10 : ZMod 121260691) ^ 20210115 = (10 : ZMod 121260691) ^ (10105057 + 10105057 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 10105057 * (10 : ZMod 121260691) ^ 10105057) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 60561357 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 121260691) ^ 40420230 = 60561356 := by
        calc
          (10 : ZMod 121260691) ^ 40420230 = (10 : ZMod 121260691) ^ (20210115 + 20210115) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 20210115 * (10 : ZMod 121260691) ^ 20210115 := by rw [pow_add]
          _ = 60561356 := by rw [factor_1_24]; decide
      change (10 : ZMod 121260691) ^ 40420230 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (10 : ZMod 121260691) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 121260691) ^ 2 = 100 := by
        calc
          (10 : ZMod 121260691) ^ 2 = (10 : ZMod 121260691) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 1 * (10 : ZMod 121260691) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 121260691) ^ 5 = 100000 := by
        calc
          (10 : ZMod 121260691) ^ 5 = (10 : ZMod 121260691) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 2 * (10 : ZMod 121260691) ^ 2) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 121260691) ^ 11 = 81190616 := by
        calc
          (10 : ZMod 121260691) ^ 11 = (10 : ZMod 121260691) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 5 * (10 : ZMod 121260691) ^ 5) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 81190616 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 121260691) ^ 23 = 47674737 := by
        calc
          (10 : ZMod 121260691) ^ 23 = (10 : ZMod 121260691) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 11 * (10 : ZMod 121260691) ^ 11) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 47674737 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 121260691) ^ 46 = 107305846 := by
        calc
          (10 : ZMod 121260691) ^ 46 = (10 : ZMod 121260691) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 23 * (10 : ZMod 121260691) ^ 23 := by rw [pow_add]
          _ = 107305846 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 121260691) ^ 92 = 62348103 := by
        calc
          (10 : ZMod 121260691) ^ 92 = (10 : ZMod 121260691) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 46 * (10 : ZMod 121260691) ^ 46 := by rw [pow_add]
          _ = 62348103 := by rw [factor_2_5]; decide
      have factor_2_7 : (10 : ZMod 121260691) ^ 185 = 119934614 := by
        calc
          (10 : ZMod 121260691) ^ 185 = (10 : ZMod 121260691) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 92 * (10 : ZMod 121260691) ^ 92) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 119934614 := by rw [factor_2_6]; decide
      have factor_2_8 : (10 : ZMod 121260691) ^ 370 = 78929738 := by
        calc
          (10 : ZMod 121260691) ^ 370 = (10 : ZMod 121260691) ^ (185 + 185) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 185 * (10 : ZMod 121260691) ^ 185 := by rw [pow_add]
          _ = 78929738 := by rw [factor_2_7]; decide
      have factor_2_9 : (10 : ZMod 121260691) ^ 740 = 92431797 := by
        calc
          (10 : ZMod 121260691) ^ 740 = (10 : ZMod 121260691) ^ (370 + 370) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 370 * (10 : ZMod 121260691) ^ 370 := by rw [pow_add]
          _ = 92431797 := by rw [factor_2_8]; decide
      have factor_2_10 : (10 : ZMod 121260691) ^ 1480 = 117039066 := by
        calc
          (10 : ZMod 121260691) ^ 1480 = (10 : ZMod 121260691) ^ (740 + 740) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 740 * (10 : ZMod 121260691) ^ 740 := by rw [pow_add]
          _ = 117039066 := by rw [factor_2_9]; decide
      have factor_2_11 : (10 : ZMod 121260691) ^ 2960 = 70102282 := by
        calc
          (10 : ZMod 121260691) ^ 2960 = (10 : ZMod 121260691) ^ (1480 + 1480) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 1480 * (10 : ZMod 121260691) ^ 1480 := by rw [pow_add]
          _ = 70102282 := by rw [factor_2_10]; decide
      have factor_2_12 : (10 : ZMod 121260691) ^ 5920 = 100142962 := by
        calc
          (10 : ZMod 121260691) ^ 5920 = (10 : ZMod 121260691) ^ (2960 + 2960) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 2960 * (10 : ZMod 121260691) ^ 2960 := by rw [pow_add]
          _ = 100142962 := by rw [factor_2_11]; decide
      have factor_2_13 : (10 : ZMod 121260691) ^ 11841 = 113760043 := by
        calc
          (10 : ZMod 121260691) ^ 11841 = (10 : ZMod 121260691) ^ (5920 + 5920 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 5920 * (10 : ZMod 121260691) ^ 5920) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 113760043 := by rw [factor_2_12]; decide
      have factor_2_14 : (10 : ZMod 121260691) ^ 23683 = 103838243 := by
        calc
          (10 : ZMod 121260691) ^ 23683 = (10 : ZMod 121260691) ^ (11841 + 11841 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 11841 * (10 : ZMod 121260691) ^ 11841) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 103838243 := by rw [factor_2_13]; decide
      have factor_2_15 : (10 : ZMod 121260691) ^ 47367 = 45565171 := by
        calc
          (10 : ZMod 121260691) ^ 47367 = (10 : ZMod 121260691) ^ (23683 + 23683 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 23683 * (10 : ZMod 121260691) ^ 23683) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 45565171 := by rw [factor_2_14]; decide
      have factor_2_16 : (10 : ZMod 121260691) ^ 94734 = 549417 := by
        calc
          (10 : ZMod 121260691) ^ 94734 = (10 : ZMod 121260691) ^ (47367 + 47367) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 47367 * (10 : ZMod 121260691) ^ 47367 := by rw [pow_add]
          _ = 549417 := by rw [factor_2_15]; decide
      have factor_2_17 : (10 : ZMod 121260691) ^ 189469 = 48017827 := by
        calc
          (10 : ZMod 121260691) ^ 189469 = (10 : ZMod 121260691) ^ (94734 + 94734 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 94734 * (10 : ZMod 121260691) ^ 94734) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 48017827 := by rw [factor_2_16]; decide
      have factor_2_18 : (10 : ZMod 121260691) ^ 378939 = 97567706 := by
        calc
          (10 : ZMod 121260691) ^ 378939 = (10 : ZMod 121260691) ^ (189469 + 189469 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 189469 * (10 : ZMod 121260691) ^ 189469) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 97567706 := by rw [factor_2_17]; decide
      have factor_2_19 : (10 : ZMod 121260691) ^ 757879 = 10110373 := by
        calc
          (10 : ZMod 121260691) ^ 757879 = (10 : ZMod 121260691) ^ (378939 + 378939 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 378939 * (10 : ZMod 121260691) ^ 378939) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 10110373 := by rw [factor_2_18]; decide
      have factor_2_20 : (10 : ZMod 121260691) ^ 1515758 = 32464095 := by
        calc
          (10 : ZMod 121260691) ^ 1515758 = (10 : ZMod 121260691) ^ (757879 + 757879) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 757879 * (10 : ZMod 121260691) ^ 757879 := by rw [pow_add]
          _ = 32464095 := by rw [factor_2_19]; decide
      have factor_2_21 : (10 : ZMod 121260691) ^ 3031517 = 65915726 := by
        calc
          (10 : ZMod 121260691) ^ 3031517 = (10 : ZMod 121260691) ^ (1515758 + 1515758 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 1515758 * (10 : ZMod 121260691) ^ 1515758) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 65915726 := by rw [factor_2_20]; decide
      have factor_2_22 : (10 : ZMod 121260691) ^ 6063034 = 88177210 := by
        calc
          (10 : ZMod 121260691) ^ 6063034 = (10 : ZMod 121260691) ^ (3031517 + 3031517) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 3031517 * (10 : ZMod 121260691) ^ 3031517 := by rw [pow_add]
          _ = 88177210 := by rw [factor_2_21]; decide
      have factor_2_23 : (10 : ZMod 121260691) ^ 12126069 = 19244059 := by
        calc
          (10 : ZMod 121260691) ^ 12126069 = (10 : ZMod 121260691) ^ (6063034 + 6063034 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 6063034 * (10 : ZMod 121260691) ^ 6063034) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 19244059 := by rw [factor_2_22]; decide
      have factor_2_24 : (10 : ZMod 121260691) ^ 24252138 = 18660751 := by
        calc
          (10 : ZMod 121260691) ^ 24252138 = (10 : ZMod 121260691) ^ (12126069 + 12126069) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 12126069 * (10 : ZMod 121260691) ^ 12126069 := by rw [pow_add]
          _ = 18660751 := by rw [factor_2_23]; decide
      change (10 : ZMod 121260691) ^ 24252138 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (10 : ZMod 121260691) ^ 1 = 10 := by norm_num
      have factor_3_1 : (10 : ZMod 121260691) ^ 2 = 100 := by
        calc
          (10 : ZMod 121260691) ^ 2 = (10 : ZMod 121260691) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 1 * (10 : ZMod 121260691) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_3_0]; decide
      have factor_3_2 : (10 : ZMod 121260691) ^ 5 = 100000 := by
        calc
          (10 : ZMod 121260691) ^ 5 = (10 : ZMod 121260691) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 2 * (10 : ZMod 121260691) ^ 2) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_3_1]; decide
      have factor_3_3 : (10 : ZMod 121260691) ^ 11 = 81190616 := by
        calc
          (10 : ZMod 121260691) ^ 11 = (10 : ZMod 121260691) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 5 * (10 : ZMod 121260691) ^ 5) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 81190616 := by rw [factor_3_2]; decide
      have factor_3_4 : (10 : ZMod 121260691) ^ 22 = 41145681 := by
        calc
          (10 : ZMod 121260691) ^ 22 = (10 : ZMod 121260691) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 11 * (10 : ZMod 121260691) ^ 11 := by rw [pow_add]
          _ = 41145681 := by rw [factor_3_3]; decide
      have factor_3_5 : (10 : ZMod 121260691) ^ 45 = 59234861 := by
        calc
          (10 : ZMod 121260691) ^ 45 = (10 : ZMod 121260691) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = ((10 : ZMod 121260691) ^ 22 * (10 : ZMod 121260691) ^ 22) * (10 : ZMod 121260691) := by rw [pow_succ, pow_add]
          _ = 59234861 := by rw [factor_3_4]; decide
      have factor_3_6 : (10 : ZMod 121260691) ^ 90 = 81868144 := by
        calc
          (10 : ZMod 121260691) ^ 90 = (10 : ZMod 121260691) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (10 : ZMod 121260691) ^ n) (by norm_num)
          _ = (10 : ZMod 121260691) ^ 45 * (10 : ZMod 121260691) ^ 45 := by rw [pow_add]
          _ = 81868144 := by rw [factor_3_5]; decide
      change (10 : ZMod 121260691) ^ 90 ≠ 1
      rw [factor_3_6]
      decide

#print axioms prime_lucas_121260691

end TotientTailPeriodKiller
end Erdos249257
