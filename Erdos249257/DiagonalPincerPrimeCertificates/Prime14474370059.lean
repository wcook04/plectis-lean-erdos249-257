import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime108017687

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_14474370059 : Nat.Prime 14474370059 := by
  apply lucas_primality 14474370059 (2 : ZMod 14474370059)
  ·
      have fermat_0 : (2 : ZMod 14474370059) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 14474370059) ^ 3 = 8 := by
        calc
          (2 : ZMod 14474370059) ^ 3 = (2 : ZMod 14474370059) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 1 * (2 : ZMod 14474370059) ^ 1) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 14474370059) ^ 6 = 64 := by
        calc
          (2 : ZMod 14474370059) ^ 6 = (2 : ZMod 14474370059) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 3 * (2 : ZMod 14474370059) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 14474370059) ^ 13 = 8192 := by
        calc
          (2 : ZMod 14474370059) ^ 13 = (2 : ZMod 14474370059) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 6 * (2 : ZMod 14474370059) ^ 6) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 14474370059) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 14474370059) ^ 26 = (2 : ZMod 14474370059) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 13 * (2 : ZMod 14474370059) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 14474370059) ^ 53 = 1408206118 := by
        calc
          (2 : ZMod 14474370059) ^ 53 = (2 : ZMod 14474370059) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 26 * (2 : ZMod 14474370059) ^ 26) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 1408206118 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 14474370059) ^ 107 = 5883585194 := by
        calc
          (2 : ZMod 14474370059) ^ 107 = (2 : ZMod 14474370059) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 53 * (2 : ZMod 14474370059) ^ 53) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 5883585194 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 14474370059) ^ 215 = 842574934 := by
        calc
          (2 : ZMod 14474370059) ^ 215 = (2 : ZMod 14474370059) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 107 * (2 : ZMod 14474370059) ^ 107) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 842574934 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 14474370059) ^ 431 = 14371306809 := by
        calc
          (2 : ZMod 14474370059) ^ 431 = (2 : ZMod 14474370059) ^ (215 + 215 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 215 * (2 : ZMod 14474370059) ^ 215) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 14371306809 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 14474370059) ^ 862 = 2558395291 := by
        calc
          (2 : ZMod 14474370059) ^ 862 = (2 : ZMod 14474370059) ^ (431 + 431) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 431 * (2 : ZMod 14474370059) ^ 431 := by rw [pow_add]
          _ = 2558395291 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 14474370059) ^ 1725 = 1955707148 := by
        calc
          (2 : ZMod 14474370059) ^ 1725 = (2 : ZMod 14474370059) ^ (862 + 862 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 862 * (2 : ZMod 14474370059) ^ 862) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 1955707148 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 14474370059) ^ 3450 = 9630806011 := by
        calc
          (2 : ZMod 14474370059) ^ 3450 = (2 : ZMod 14474370059) ^ (1725 + 1725) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 1725 * (2 : ZMod 14474370059) ^ 1725 := by rw [pow_add]
          _ = 9630806011 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 14474370059) ^ 6901 = 5550424887 := by
        calc
          (2 : ZMod 14474370059) ^ 6901 = (2 : ZMod 14474370059) ^ (3450 + 3450 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 3450 * (2 : ZMod 14474370059) ^ 3450) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 5550424887 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 14474370059) ^ 13803 = 12100573044 := by
        calc
          (2 : ZMod 14474370059) ^ 13803 = (2 : ZMod 14474370059) ^ (6901 + 6901 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 6901 * (2 : ZMod 14474370059) ^ 6901) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 12100573044 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 14474370059) ^ 27607 = 9065104357 := by
        calc
          (2 : ZMod 14474370059) ^ 27607 = (2 : ZMod 14474370059) ^ (13803 + 13803 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 13803 * (2 : ZMod 14474370059) ^ 13803) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 9065104357 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 14474370059) ^ 55215 = 9837191803 := by
        calc
          (2 : ZMod 14474370059) ^ 55215 = (2 : ZMod 14474370059) ^ (27607 + 27607 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 27607 * (2 : ZMod 14474370059) ^ 27607) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 9837191803 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 14474370059) ^ 110430 = 5463656785 := by
        calc
          (2 : ZMod 14474370059) ^ 110430 = (2 : ZMod 14474370059) ^ (55215 + 55215) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 55215 * (2 : ZMod 14474370059) ^ 55215 := by rw [pow_add]
          _ = 5463656785 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 14474370059) ^ 220861 = 603085443 := by
        calc
          (2 : ZMod 14474370059) ^ 220861 = (2 : ZMod 14474370059) ^ (110430 + 110430 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 110430 * (2 : ZMod 14474370059) ^ 110430) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 603085443 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 14474370059) ^ 441722 = 8344103954 := by
        calc
          (2 : ZMod 14474370059) ^ 441722 = (2 : ZMod 14474370059) ^ (220861 + 220861) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 220861 * (2 : ZMod 14474370059) ^ 220861 := by rw [pow_add]
          _ = 8344103954 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 14474370059) ^ 883445 = 14431193675 := by
        calc
          (2 : ZMod 14474370059) ^ 883445 = (2 : ZMod 14474370059) ^ (441722 + 441722 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 441722 * (2 : ZMod 14474370059) ^ 441722) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 14431193675 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 14474370059) ^ 1766890 = 2592306669 := by
        calc
          (2 : ZMod 14474370059) ^ 1766890 = (2 : ZMod 14474370059) ^ (883445 + 883445) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 883445 * (2 : ZMod 14474370059) ^ 883445 := by rw [pow_add]
          _ = 2592306669 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 14474370059) ^ 3533781 = 8039010723 := by
        calc
          (2 : ZMod 14474370059) ^ 3533781 = (2 : ZMod 14474370059) ^ (1766890 + 1766890 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 1766890 * (2 : ZMod 14474370059) ^ 1766890) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 8039010723 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 14474370059) ^ 7067563 = 5327527633 := by
        calc
          (2 : ZMod 14474370059) ^ 7067563 = (2 : ZMod 14474370059) ^ (3533781 + 3533781 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 3533781 * (2 : ZMod 14474370059) ^ 3533781) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 5327527633 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 14474370059) ^ 14135127 = 3369164739 := by
        calc
          (2 : ZMod 14474370059) ^ 14135127 = (2 : ZMod 14474370059) ^ (7067563 + 7067563 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 7067563 * (2 : ZMod 14474370059) ^ 7067563) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 3369164739 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 14474370059) ^ 28270254 = 12034212214 := by
        calc
          (2 : ZMod 14474370059) ^ 28270254 = (2 : ZMod 14474370059) ^ (14135127 + 14135127) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 14135127 * (2 : ZMod 14474370059) ^ 14135127 := by rw [pow_add]
          _ = 12034212214 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 14474370059) ^ 56540508 = 5563335549 := by
        calc
          (2 : ZMod 14474370059) ^ 56540508 = (2 : ZMod 14474370059) ^ (28270254 + 28270254) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 28270254 * (2 : ZMod 14474370059) ^ 28270254 := by rw [pow_add]
          _ = 5563335549 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 14474370059) ^ 113081016 = 2487251723 := by
        calc
          (2 : ZMod 14474370059) ^ 113081016 = (2 : ZMod 14474370059) ^ (56540508 + 56540508) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 56540508 * (2 : ZMod 14474370059) ^ 56540508 := by rw [pow_add]
          _ = 2487251723 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 14474370059) ^ 226162032 = 2304971516 := by
        calc
          (2 : ZMod 14474370059) ^ 226162032 = (2 : ZMod 14474370059) ^ (113081016 + 113081016) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 113081016 * (2 : ZMod 14474370059) ^ 113081016 := by rw [pow_add]
          _ = 2304971516 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 14474370059) ^ 452324064 = 9754507857 := by
        calc
          (2 : ZMod 14474370059) ^ 452324064 = (2 : ZMod 14474370059) ^ (226162032 + 226162032) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 226162032 * (2 : ZMod 14474370059) ^ 226162032 := by rw [pow_add]
          _ = 9754507857 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 14474370059) ^ 904648128 = 10614184609 := by
        calc
          (2 : ZMod 14474370059) ^ 904648128 = (2 : ZMod 14474370059) ^ (452324064 + 452324064) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 452324064 * (2 : ZMod 14474370059) ^ 452324064 := by rw [pow_add]
          _ = 10614184609 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 14474370059) ^ 1809296257 = 12580553808 := by
        calc
          (2 : ZMod 14474370059) ^ 1809296257 = (2 : ZMod 14474370059) ^ (904648128 + 904648128 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 904648128 * (2 : ZMod 14474370059) ^ 904648128) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 12580553808 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 14474370059) ^ 3618592514 = 514556548 := by
        calc
          (2 : ZMod 14474370059) ^ 3618592514 = (2 : ZMod 14474370059) ^ (1809296257 + 1809296257) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 1809296257 * (2 : ZMod 14474370059) ^ 1809296257 := by rw [pow_add]
          _ = 514556548 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 14474370059) ^ 7237185029 = 14474370058 := by
        calc
          (2 : ZMod 14474370059) ^ 7237185029 = (2 : ZMod 14474370059) ^ (3618592514 + 3618592514 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 3618592514 * (2 : ZMod 14474370059) ^ 3618592514) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 14474370058 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 14474370059) ^ 14474370058 = 1 := by
        calc
          (2 : ZMod 14474370059) ^ 14474370058 = (2 : ZMod 14474370059) ^ (7237185029 + 7237185029) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 7237185029 * (2 : ZMod 14474370059) ^ 7237185029 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (108017687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (108017687, 1)] : List FactorBlock).map factorBlockValue).prod = 14474370059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_108017687) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 14474370059) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 14474370059) ^ 3 = 8 := by
        calc
          (2 : ZMod 14474370059) ^ 3 = (2 : ZMod 14474370059) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 1 * (2 : ZMod 14474370059) ^ 1) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 14474370059) ^ 6 = 64 := by
        calc
          (2 : ZMod 14474370059) ^ 6 = (2 : ZMod 14474370059) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 3 * (2 : ZMod 14474370059) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 14474370059) ^ 13 = 8192 := by
        calc
          (2 : ZMod 14474370059) ^ 13 = (2 : ZMod 14474370059) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 6 * (2 : ZMod 14474370059) ^ 6) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 14474370059) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 14474370059) ^ 26 = (2 : ZMod 14474370059) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 13 * (2 : ZMod 14474370059) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 14474370059) ^ 53 = 1408206118 := by
        calc
          (2 : ZMod 14474370059) ^ 53 = (2 : ZMod 14474370059) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 26 * (2 : ZMod 14474370059) ^ 26) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 1408206118 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 14474370059) ^ 107 = 5883585194 := by
        calc
          (2 : ZMod 14474370059) ^ 107 = (2 : ZMod 14474370059) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 53 * (2 : ZMod 14474370059) ^ 53) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 5883585194 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 14474370059) ^ 215 = 842574934 := by
        calc
          (2 : ZMod 14474370059) ^ 215 = (2 : ZMod 14474370059) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 107 * (2 : ZMod 14474370059) ^ 107) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 842574934 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 14474370059) ^ 431 = 14371306809 := by
        calc
          (2 : ZMod 14474370059) ^ 431 = (2 : ZMod 14474370059) ^ (215 + 215 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 215 * (2 : ZMod 14474370059) ^ 215) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 14371306809 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 14474370059) ^ 862 = 2558395291 := by
        calc
          (2 : ZMod 14474370059) ^ 862 = (2 : ZMod 14474370059) ^ (431 + 431) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 431 * (2 : ZMod 14474370059) ^ 431 := by rw [pow_add]
          _ = 2558395291 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 14474370059) ^ 1725 = 1955707148 := by
        calc
          (2 : ZMod 14474370059) ^ 1725 = (2 : ZMod 14474370059) ^ (862 + 862 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 862 * (2 : ZMod 14474370059) ^ 862) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 1955707148 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 14474370059) ^ 3450 = 9630806011 := by
        calc
          (2 : ZMod 14474370059) ^ 3450 = (2 : ZMod 14474370059) ^ (1725 + 1725) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 1725 * (2 : ZMod 14474370059) ^ 1725 := by rw [pow_add]
          _ = 9630806011 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 14474370059) ^ 6901 = 5550424887 := by
        calc
          (2 : ZMod 14474370059) ^ 6901 = (2 : ZMod 14474370059) ^ (3450 + 3450 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 3450 * (2 : ZMod 14474370059) ^ 3450) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 5550424887 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 14474370059) ^ 13803 = 12100573044 := by
        calc
          (2 : ZMod 14474370059) ^ 13803 = (2 : ZMod 14474370059) ^ (6901 + 6901 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 6901 * (2 : ZMod 14474370059) ^ 6901) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 12100573044 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 14474370059) ^ 27607 = 9065104357 := by
        calc
          (2 : ZMod 14474370059) ^ 27607 = (2 : ZMod 14474370059) ^ (13803 + 13803 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 13803 * (2 : ZMod 14474370059) ^ 13803) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 9065104357 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 14474370059) ^ 55215 = 9837191803 := by
        calc
          (2 : ZMod 14474370059) ^ 55215 = (2 : ZMod 14474370059) ^ (27607 + 27607 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 27607 * (2 : ZMod 14474370059) ^ 27607) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 9837191803 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 14474370059) ^ 110430 = 5463656785 := by
        calc
          (2 : ZMod 14474370059) ^ 110430 = (2 : ZMod 14474370059) ^ (55215 + 55215) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 55215 * (2 : ZMod 14474370059) ^ 55215 := by rw [pow_add]
          _ = 5463656785 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 14474370059) ^ 220861 = 603085443 := by
        calc
          (2 : ZMod 14474370059) ^ 220861 = (2 : ZMod 14474370059) ^ (110430 + 110430 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 110430 * (2 : ZMod 14474370059) ^ 110430) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 603085443 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 14474370059) ^ 441722 = 8344103954 := by
        calc
          (2 : ZMod 14474370059) ^ 441722 = (2 : ZMod 14474370059) ^ (220861 + 220861) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 220861 * (2 : ZMod 14474370059) ^ 220861 := by rw [pow_add]
          _ = 8344103954 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 14474370059) ^ 883445 = 14431193675 := by
        calc
          (2 : ZMod 14474370059) ^ 883445 = (2 : ZMod 14474370059) ^ (441722 + 441722 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 441722 * (2 : ZMod 14474370059) ^ 441722) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 14431193675 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 14474370059) ^ 1766890 = 2592306669 := by
        calc
          (2 : ZMod 14474370059) ^ 1766890 = (2 : ZMod 14474370059) ^ (883445 + 883445) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 883445 * (2 : ZMod 14474370059) ^ 883445 := by rw [pow_add]
          _ = 2592306669 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 14474370059) ^ 3533781 = 8039010723 := by
        calc
          (2 : ZMod 14474370059) ^ 3533781 = (2 : ZMod 14474370059) ^ (1766890 + 1766890 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 1766890 * (2 : ZMod 14474370059) ^ 1766890) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 8039010723 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 14474370059) ^ 7067563 = 5327527633 := by
        calc
          (2 : ZMod 14474370059) ^ 7067563 = (2 : ZMod 14474370059) ^ (3533781 + 3533781 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 3533781 * (2 : ZMod 14474370059) ^ 3533781) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 5327527633 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 14474370059) ^ 14135127 = 3369164739 := by
        calc
          (2 : ZMod 14474370059) ^ 14135127 = (2 : ZMod 14474370059) ^ (7067563 + 7067563 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 7067563 * (2 : ZMod 14474370059) ^ 7067563) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 3369164739 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 14474370059) ^ 28270254 = 12034212214 := by
        calc
          (2 : ZMod 14474370059) ^ 28270254 = (2 : ZMod 14474370059) ^ (14135127 + 14135127) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 14135127 * (2 : ZMod 14474370059) ^ 14135127 := by rw [pow_add]
          _ = 12034212214 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 14474370059) ^ 56540508 = 5563335549 := by
        calc
          (2 : ZMod 14474370059) ^ 56540508 = (2 : ZMod 14474370059) ^ (28270254 + 28270254) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 28270254 * (2 : ZMod 14474370059) ^ 28270254 := by rw [pow_add]
          _ = 5563335549 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 14474370059) ^ 113081016 = 2487251723 := by
        calc
          (2 : ZMod 14474370059) ^ 113081016 = (2 : ZMod 14474370059) ^ (56540508 + 56540508) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 56540508 * (2 : ZMod 14474370059) ^ 56540508 := by rw [pow_add]
          _ = 2487251723 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 14474370059) ^ 226162032 = 2304971516 := by
        calc
          (2 : ZMod 14474370059) ^ 226162032 = (2 : ZMod 14474370059) ^ (113081016 + 113081016) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 113081016 * (2 : ZMod 14474370059) ^ 113081016 := by rw [pow_add]
          _ = 2304971516 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 14474370059) ^ 452324064 = 9754507857 := by
        calc
          (2 : ZMod 14474370059) ^ 452324064 = (2 : ZMod 14474370059) ^ (226162032 + 226162032) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 226162032 * (2 : ZMod 14474370059) ^ 226162032 := by rw [pow_add]
          _ = 9754507857 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 14474370059) ^ 904648128 = 10614184609 := by
        calc
          (2 : ZMod 14474370059) ^ 904648128 = (2 : ZMod 14474370059) ^ (452324064 + 452324064) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 452324064 * (2 : ZMod 14474370059) ^ 452324064 := by rw [pow_add]
          _ = 10614184609 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 14474370059) ^ 1809296257 = 12580553808 := by
        calc
          (2 : ZMod 14474370059) ^ 1809296257 = (2 : ZMod 14474370059) ^ (904648128 + 904648128 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 904648128 * (2 : ZMod 14474370059) ^ 904648128) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 12580553808 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 14474370059) ^ 3618592514 = 514556548 := by
        calc
          (2 : ZMod 14474370059) ^ 3618592514 = (2 : ZMod 14474370059) ^ (1809296257 + 1809296257) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 1809296257 * (2 : ZMod 14474370059) ^ 1809296257 := by rw [pow_add]
          _ = 514556548 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 14474370059) ^ 7237185029 = 14474370058 := by
        calc
          (2 : ZMod 14474370059) ^ 7237185029 = (2 : ZMod 14474370059) ^ (3618592514 + 3618592514 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 3618592514 * (2 : ZMod 14474370059) ^ 3618592514) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 14474370058 := by rw [factor_0_31]; decide
      change (2 : ZMod 14474370059) ^ 7237185029 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (2 : ZMod 14474370059) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 14474370059) ^ 3 = 8 := by
        calc
          (2 : ZMod 14474370059) ^ 3 = (2 : ZMod 14474370059) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 1 * (2 : ZMod 14474370059) ^ 1) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 14474370059) ^ 6 = 64 := by
        calc
          (2 : ZMod 14474370059) ^ 6 = (2 : ZMod 14474370059) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 3 * (2 : ZMod 14474370059) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 14474370059) ^ 12 = 4096 := by
        calc
          (2 : ZMod 14474370059) ^ 12 = (2 : ZMod 14474370059) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 6 * (2 : ZMod 14474370059) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 14474370059) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 14474370059) ^ 25 = (2 : ZMod 14474370059) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 12 * (2 : ZMod 14474370059) ^ 12) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 14474370059) ^ 51 = 7589236559 := by
        calc
          (2 : ZMod 14474370059) ^ 51 = (2 : ZMod 14474370059) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 25 * (2 : ZMod 14474370059) ^ 25) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 7589236559 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 14474370059) ^ 103 = 2177020332 := by
        calc
          (2 : ZMod 14474370059) ^ 103 = (2 : ZMod 14474370059) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 51 * (2 : ZMod 14474370059) ^ 51) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 2177020332 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 14474370059) ^ 206 = 8991586433 := by
        calc
          (2 : ZMod 14474370059) ^ 206 = (2 : ZMod 14474370059) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 103 * (2 : ZMod 14474370059) ^ 103 := by rw [pow_add]
          _ = 8991586433 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 14474370059) ^ 412 = 10726518237 := by
        calc
          (2 : ZMod 14474370059) ^ 412 = (2 : ZMod 14474370059) ^ (206 + 206) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 206 * (2 : ZMod 14474370059) ^ 206 := by rw [pow_add]
          _ = 10726518237 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 14474370059) ^ 824 = 5033706020 := by
        calc
          (2 : ZMod 14474370059) ^ 824 = (2 : ZMod 14474370059) ^ (412 + 412) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 412 * (2 : ZMod 14474370059) ^ 412 := by rw [pow_add]
          _ = 5033706020 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 14474370059) ^ 1648 = 1947382565 := by
        calc
          (2 : ZMod 14474370059) ^ 1648 = (2 : ZMod 14474370059) ^ (824 + 824) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 824 * (2 : ZMod 14474370059) ^ 824 := by rw [pow_add]
          _ = 1947382565 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 14474370059) ^ 3296 = 3612722585 := by
        calc
          (2 : ZMod 14474370059) ^ 3296 = (2 : ZMod 14474370059) ^ (1648 + 1648) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 1648 * (2 : ZMod 14474370059) ^ 1648 := by rw [pow_add]
          _ = 3612722585 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 14474370059) ^ 6592 = 4360585129 := by
        calc
          (2 : ZMod 14474370059) ^ 6592 = (2 : ZMod 14474370059) ^ (3296 + 3296) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 3296 * (2 : ZMod 14474370059) ^ 3296 := by rw [pow_add]
          _ = 4360585129 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 14474370059) ^ 13185 = 12509733808 := by
        calc
          (2 : ZMod 14474370059) ^ 13185 = (2 : ZMod 14474370059) ^ (6592 + 6592 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 6592 * (2 : ZMod 14474370059) ^ 6592) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 12509733808 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 14474370059) ^ 26371 = 5874930243 := by
        calc
          (2 : ZMod 14474370059) ^ 26371 = (2 : ZMod 14474370059) ^ (13185 + 13185 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 13185 * (2 : ZMod 14474370059) ^ 13185) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 5874930243 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 14474370059) ^ 52743 = 1950346409 := by
        calc
          (2 : ZMod 14474370059) ^ 52743 = (2 : ZMod 14474370059) ^ (26371 + 26371 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 26371 * (2 : ZMod 14474370059) ^ 26371) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 1950346409 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 14474370059) ^ 105486 = 8963189679 := by
        calc
          (2 : ZMod 14474370059) ^ 105486 = (2 : ZMod 14474370059) ^ (52743 + 52743) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 52743 * (2 : ZMod 14474370059) ^ 52743 := by rw [pow_add]
          _ = 8963189679 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 14474370059) ^ 210972 = 5303673290 := by
        calc
          (2 : ZMod 14474370059) ^ 210972 = (2 : ZMod 14474370059) ^ (105486 + 105486) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 105486 * (2 : ZMod 14474370059) ^ 105486 := by rw [pow_add]
          _ = 5303673290 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 14474370059) ^ 421944 = 9479346924 := by
        calc
          (2 : ZMod 14474370059) ^ 421944 = (2 : ZMod 14474370059) ^ (210972 + 210972) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 210972 * (2 : ZMod 14474370059) ^ 210972 := by rw [pow_add]
          _ = 9479346924 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 14474370059) ^ 843888 = 10001580720 := by
        calc
          (2 : ZMod 14474370059) ^ 843888 = (2 : ZMod 14474370059) ^ (421944 + 421944) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 421944 * (2 : ZMod 14474370059) ^ 421944 := by rw [pow_add]
          _ = 10001580720 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 14474370059) ^ 1687776 = 13261004247 := by
        calc
          (2 : ZMod 14474370059) ^ 1687776 = (2 : ZMod 14474370059) ^ (843888 + 843888) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 843888 * (2 : ZMod 14474370059) ^ 843888 := by rw [pow_add]
          _ = 13261004247 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 14474370059) ^ 3375552 = 9156630510 := by
        calc
          (2 : ZMod 14474370059) ^ 3375552 = (2 : ZMod 14474370059) ^ (1687776 + 1687776) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 1687776 * (2 : ZMod 14474370059) ^ 1687776 := by rw [pow_add]
          _ = 9156630510 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 14474370059) ^ 6751105 = 6161183766 := by
        calc
          (2 : ZMod 14474370059) ^ 6751105 = (2 : ZMod 14474370059) ^ (3375552 + 3375552 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 3375552 * (2 : ZMod 14474370059) ^ 3375552) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 6161183766 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 14474370059) ^ 13502210 = 2365105501 := by
        calc
          (2 : ZMod 14474370059) ^ 13502210 = (2 : ZMod 14474370059) ^ (6751105 + 6751105) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 6751105 * (2 : ZMod 14474370059) ^ 6751105 := by rw [pow_add]
          _ = 2365105501 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 14474370059) ^ 27004421 = 10922506473 := by
        calc
          (2 : ZMod 14474370059) ^ 27004421 = (2 : ZMod 14474370059) ^ (13502210 + 13502210 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 13502210 * (2 : ZMod 14474370059) ^ 13502210) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 10922506473 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 14474370059) ^ 54008843 = 7988226100 := by
        calc
          (2 : ZMod 14474370059) ^ 54008843 = (2 : ZMod 14474370059) ^ (27004421 + 27004421 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 27004421 * (2 : ZMod 14474370059) ^ 27004421) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 7988226100 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 14474370059) ^ 108017687 = 4063775585 := by
        calc
          (2 : ZMod 14474370059) ^ 108017687 = (2 : ZMod 14474370059) ^ (54008843 + 54008843 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 54008843 * (2 : ZMod 14474370059) ^ 54008843) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 4063775585 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 14474370059) ^ 216035374 = 10612734166 := by
        calc
          (2 : ZMod 14474370059) ^ 216035374 = (2 : ZMod 14474370059) ^ (108017687 + 108017687) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 108017687 * (2 : ZMod 14474370059) ^ 108017687 := by rw [pow_add]
          _ = 10612734166 := by rw [factor_1_26]; decide
      change (2 : ZMod 14474370059) ^ 216035374 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 14474370059) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 14474370059) ^ 2 = 4 := by
        calc
          (2 : ZMod 14474370059) ^ 2 = (2 : ZMod 14474370059) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 1 * (2 : ZMod 14474370059) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 14474370059) ^ 4 = 16 := by
        calc
          (2 : ZMod 14474370059) ^ 4 = (2 : ZMod 14474370059) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 2 * (2 : ZMod 14474370059) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 14474370059) ^ 8 = 256 := by
        calc
          (2 : ZMod 14474370059) ^ 8 = (2 : ZMod 14474370059) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 4 * (2 : ZMod 14474370059) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 14474370059) ^ 16 = 65536 := by
        calc
          (2 : ZMod 14474370059) ^ 16 = (2 : ZMod 14474370059) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 8 * (2 : ZMod 14474370059) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 14474370059) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 14474370059) ^ 33 = (2 : ZMod 14474370059) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 16 * (2 : ZMod 14474370059) ^ 16) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 14474370059) ^ 67 = 14377533325 := by
        calc
          (2 : ZMod 14474370059) ^ 67 = (2 : ZMod 14474370059) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = ((2 : ZMod 14474370059) ^ 33 * (2 : ZMod 14474370059) ^ 33) * (2 : ZMod 14474370059) := by rw [pow_succ, pow_add]
          _ = 14377533325 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 14474370059) ^ 134 = 2139733075 := by
        calc
          (2 : ZMod 14474370059) ^ 134 = (2 : ZMod 14474370059) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (2 : ZMod 14474370059) ^ n) (by norm_num)
          _ = (2 : ZMod 14474370059) ^ 67 * (2 : ZMod 14474370059) ^ 67 := by rw [pow_add]
          _ = 2139733075 := by rw [factor_2_6]; decide
      change (2 : ZMod 14474370059) ^ 134 ≠ 1
      rw [factor_2_7]
      decide

#print axioms prime_lucas_14474370059

end TotientTailPeriodKiller
end Erdos249257
