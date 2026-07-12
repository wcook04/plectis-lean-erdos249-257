import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime4537773511

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_54453282133 : Nat.Prime 54453282133 := by
  apply lucas_primality 54453282133 (5 : ZMod 54453282133)
  ·
      have fermat_0 : (5 : ZMod 54453282133) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 54453282133) ^ 3 = 125 := by
        calc
          (5 : ZMod 54453282133) ^ 3 = (5 : ZMod 54453282133) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1 * (5 : ZMod 54453282133) ^ 1) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 54453282133) ^ 6 = 15625 := by
        calc
          (5 : ZMod 54453282133) ^ 6 = (5 : ZMod 54453282133) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 3 * (5 : ZMod 54453282133) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 54453282133) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 54453282133) ^ 12 = (5 : ZMod 54453282133) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 6 * (5 : ZMod 54453282133) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 54453282133) ^ 25 = 29590069194 := by
        calc
          (5 : ZMod 54453282133) ^ 25 = (5 : ZMod 54453282133) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 12 * (5 : ZMod 54453282133) ^ 12) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 29590069194 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 54453282133) ^ 50 = 30911323302 := by
        calc
          (5 : ZMod 54453282133) ^ 50 = (5 : ZMod 54453282133) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 25 * (5 : ZMod 54453282133) ^ 25 := by rw [pow_add]
          _ = 30911323302 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 54453282133) ^ 101 = 54066422986 := by
        calc
          (5 : ZMod 54453282133) ^ 101 = (5 : ZMod 54453282133) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 50 * (5 : ZMod 54453282133) ^ 50) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 54066422986 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 54453282133) ^ 202 = 17126946 := by
        calc
          (5 : ZMod 54453282133) ^ 202 = (5 : ZMod 54453282133) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 101 * (5 : ZMod 54453282133) ^ 101 := by rw [pow_add]
          _ = 17126946 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 54453282133) ^ 405 = 16695464358 := by
        calc
          (5 : ZMod 54453282133) ^ 405 = (5 : ZMod 54453282133) ^ (202 + 202 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 202 * (5 : ZMod 54453282133) ^ 202) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 16695464358 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 54453282133) ^ 811 = 22217292637 := by
        calc
          (5 : ZMod 54453282133) ^ 811 = (5 : ZMod 54453282133) ^ (405 + 405 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 405 * (5 : ZMod 54453282133) ^ 405) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 22217292637 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 54453282133) ^ 1622 = 5417428048 := by
        calc
          (5 : ZMod 54453282133) ^ 1622 = (5 : ZMod 54453282133) ^ (811 + 811) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 811 * (5 : ZMod 54453282133) ^ 811 := by rw [pow_add]
          _ = 5417428048 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 54453282133) ^ 3245 = 12383747059 := by
        calc
          (5 : ZMod 54453282133) ^ 3245 = (5 : ZMod 54453282133) ^ (1622 + 1622 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1622 * (5 : ZMod 54453282133) ^ 1622) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 12383747059 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 54453282133) ^ 6491 = 25676688838 := by
        calc
          (5 : ZMod 54453282133) ^ 6491 = (5 : ZMod 54453282133) ^ (3245 + 3245 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 3245 * (5 : ZMod 54453282133) ^ 3245) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 25676688838 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 54453282133) ^ 12982 = 19911487702 := by
        calc
          (5 : ZMod 54453282133) ^ 12982 = (5 : ZMod 54453282133) ^ (6491 + 6491) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 6491 * (5 : ZMod 54453282133) ^ 6491 := by rw [pow_add]
          _ = 19911487702 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 54453282133) ^ 25965 = 16889917625 := by
        calc
          (5 : ZMod 54453282133) ^ 25965 = (5 : ZMod 54453282133) ^ (12982 + 12982 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 12982 * (5 : ZMod 54453282133) ^ 12982) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 16889917625 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 54453282133) ^ 51930 = 13646918404 := by
        calc
          (5 : ZMod 54453282133) ^ 51930 = (5 : ZMod 54453282133) ^ (25965 + 25965) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 25965 * (5 : ZMod 54453282133) ^ 25965 := by rw [pow_add]
          _ = 13646918404 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 54453282133) ^ 103861 = 25724894011 := by
        calc
          (5 : ZMod 54453282133) ^ 103861 = (5 : ZMod 54453282133) ^ (51930 + 51930 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 51930 * (5 : ZMod 54453282133) ^ 51930) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 25724894011 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 54453282133) ^ 207722 = 47795876390 := by
        calc
          (5 : ZMod 54453282133) ^ 207722 = (5 : ZMod 54453282133) ^ (103861 + 103861) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 103861 * (5 : ZMod 54453282133) ^ 103861 := by rw [pow_add]
          _ = 47795876390 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 54453282133) ^ 415445 = 292429718 := by
        calc
          (5 : ZMod 54453282133) ^ 415445 = (5 : ZMod 54453282133) ^ (207722 + 207722 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 207722 * (5 : ZMod 54453282133) ^ 207722) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 292429718 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 54453282133) ^ 830891 = 33827468872 := by
        calc
          (5 : ZMod 54453282133) ^ 830891 = (5 : ZMod 54453282133) ^ (415445 + 415445 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 415445 * (5 : ZMod 54453282133) ^ 415445) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 33827468872 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 54453282133) ^ 1661782 = 50454628117 := by
        calc
          (5 : ZMod 54453282133) ^ 1661782 = (5 : ZMod 54453282133) ^ (830891 + 830891) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 830891 * (5 : ZMod 54453282133) ^ 830891 := by rw [pow_add]
          _ = 50454628117 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 54453282133) ^ 3323564 = 13576527237 := by
        calc
          (5 : ZMod 54453282133) ^ 3323564 = (5 : ZMod 54453282133) ^ (1661782 + 1661782) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 1661782 * (5 : ZMod 54453282133) ^ 1661782 := by rw [pow_add]
          _ = 13576527237 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 54453282133) ^ 6647129 = 23512392888 := by
        calc
          (5 : ZMod 54453282133) ^ 6647129 = (5 : ZMod 54453282133) ^ (3323564 + 3323564 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 3323564 * (5 : ZMod 54453282133) ^ 3323564) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 23512392888 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 54453282133) ^ 13294258 = 30081436453 := by
        calc
          (5 : ZMod 54453282133) ^ 13294258 = (5 : ZMod 54453282133) ^ (6647129 + 6647129) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 6647129 * (5 : ZMod 54453282133) ^ 6647129 := by rw [pow_add]
          _ = 30081436453 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 54453282133) ^ 26588516 = 30832759499 := by
        calc
          (5 : ZMod 54453282133) ^ 26588516 = (5 : ZMod 54453282133) ^ (13294258 + 13294258) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 13294258 * (5 : ZMod 54453282133) ^ 13294258 := by rw [pow_add]
          _ = 30832759499 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 54453282133) ^ 53177033 = 8918089065 := by
        calc
          (5 : ZMod 54453282133) ^ 53177033 = (5 : ZMod 54453282133) ^ (26588516 + 26588516 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 26588516 * (5 : ZMod 54453282133) ^ 26588516) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 8918089065 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 54453282133) ^ 106354066 = 28083284789 := by
        calc
          (5 : ZMod 54453282133) ^ 106354066 = (5 : ZMod 54453282133) ^ (53177033 + 53177033) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 53177033 * (5 : ZMod 54453282133) ^ 53177033 := by rw [pow_add]
          _ = 28083284789 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 54453282133) ^ 212708133 = 29414126628 := by
        calc
          (5 : ZMod 54453282133) ^ 212708133 = (5 : ZMod 54453282133) ^ (106354066 + 106354066 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 106354066 * (5 : ZMod 54453282133) ^ 106354066) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 29414126628 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 54453282133) ^ 425416266 = 10063848149 := by
        calc
          (5 : ZMod 54453282133) ^ 425416266 = (5 : ZMod 54453282133) ^ (212708133 + 212708133) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 212708133 * (5 : ZMod 54453282133) ^ 212708133 := by rw [pow_add]
          _ = 10063848149 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 54453282133) ^ 850832533 = 24097793928 := by
        calc
          (5 : ZMod 54453282133) ^ 850832533 = (5 : ZMod 54453282133) ^ (425416266 + 425416266 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 425416266 * (5 : ZMod 54453282133) ^ 425416266) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 24097793928 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 54453282133) ^ 1701665066 = 46497826631 := by
        calc
          (5 : ZMod 54453282133) ^ 1701665066 = (5 : ZMod 54453282133) ^ (850832533 + 850832533) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 850832533 * (5 : ZMod 54453282133) ^ 850832533 := by rw [pow_add]
          _ = 46497826631 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 54453282133) ^ 3403330133 = 24743890413 := by
        calc
          (5 : ZMod 54453282133) ^ 3403330133 = (5 : ZMod 54453282133) ^ (1701665066 + 1701665066 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1701665066 * (5 : ZMod 54453282133) ^ 1701665066) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 24743890413 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 54453282133) ^ 6806660266 = 26248616957 := by
        calc
          (5 : ZMod 54453282133) ^ 6806660266 = (5 : ZMod 54453282133) ^ (3403330133 + 3403330133) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 3403330133 * (5 : ZMod 54453282133) ^ 3403330133 := by rw [pow_add]
          _ = 26248616957 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 54453282133) ^ 13613320533 = 51017490898 := by
        calc
          (5 : ZMod 54453282133) ^ 13613320533 = (5 : ZMod 54453282133) ^ (6806660266 + 6806660266 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 6806660266 * (5 : ZMod 54453282133) ^ 6806660266) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 51017490898 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 54453282133) ^ 27226641066 = 54453282132 := by
        calc
          (5 : ZMod 54453282133) ^ 27226641066 = (5 : ZMod 54453282133) ^ (13613320533 + 13613320533) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 13613320533 * (5 : ZMod 54453282133) ^ 13613320533 := by rw [pow_add]
          _ = 54453282132 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 54453282133) ^ 54453282132 = 1 := by
        calc
          (5 : ZMod 54453282133) ^ 54453282132 = (5 : ZMod 54453282133) ^ (27226641066 + 27226641066) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 27226641066 * (5 : ZMod 54453282133) ^ 27226641066 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (4537773511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (4537773511, 1)] : List FactorBlock).map factorBlockValue).prod = 54453282133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_4537773511) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 54453282133) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 54453282133) ^ 3 = 125 := by
        calc
          (5 : ZMod 54453282133) ^ 3 = (5 : ZMod 54453282133) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1 * (5 : ZMod 54453282133) ^ 1) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 54453282133) ^ 6 = 15625 := by
        calc
          (5 : ZMod 54453282133) ^ 6 = (5 : ZMod 54453282133) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 3 * (5 : ZMod 54453282133) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 54453282133) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 54453282133) ^ 12 = (5 : ZMod 54453282133) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 6 * (5 : ZMod 54453282133) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 54453282133) ^ 25 = 29590069194 := by
        calc
          (5 : ZMod 54453282133) ^ 25 = (5 : ZMod 54453282133) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 12 * (5 : ZMod 54453282133) ^ 12) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 29590069194 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 54453282133) ^ 50 = 30911323302 := by
        calc
          (5 : ZMod 54453282133) ^ 50 = (5 : ZMod 54453282133) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 25 * (5 : ZMod 54453282133) ^ 25 := by rw [pow_add]
          _ = 30911323302 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 54453282133) ^ 101 = 54066422986 := by
        calc
          (5 : ZMod 54453282133) ^ 101 = (5 : ZMod 54453282133) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 50 * (5 : ZMod 54453282133) ^ 50) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 54066422986 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 54453282133) ^ 202 = 17126946 := by
        calc
          (5 : ZMod 54453282133) ^ 202 = (5 : ZMod 54453282133) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 101 * (5 : ZMod 54453282133) ^ 101 := by rw [pow_add]
          _ = 17126946 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 54453282133) ^ 405 = 16695464358 := by
        calc
          (5 : ZMod 54453282133) ^ 405 = (5 : ZMod 54453282133) ^ (202 + 202 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 202 * (5 : ZMod 54453282133) ^ 202) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 16695464358 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 54453282133) ^ 811 = 22217292637 := by
        calc
          (5 : ZMod 54453282133) ^ 811 = (5 : ZMod 54453282133) ^ (405 + 405 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 405 * (5 : ZMod 54453282133) ^ 405) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 22217292637 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 54453282133) ^ 1622 = 5417428048 := by
        calc
          (5 : ZMod 54453282133) ^ 1622 = (5 : ZMod 54453282133) ^ (811 + 811) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 811 * (5 : ZMod 54453282133) ^ 811 := by rw [pow_add]
          _ = 5417428048 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 54453282133) ^ 3245 = 12383747059 := by
        calc
          (5 : ZMod 54453282133) ^ 3245 = (5 : ZMod 54453282133) ^ (1622 + 1622 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1622 * (5 : ZMod 54453282133) ^ 1622) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 12383747059 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 54453282133) ^ 6491 = 25676688838 := by
        calc
          (5 : ZMod 54453282133) ^ 6491 = (5 : ZMod 54453282133) ^ (3245 + 3245 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 3245 * (5 : ZMod 54453282133) ^ 3245) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 25676688838 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 54453282133) ^ 12982 = 19911487702 := by
        calc
          (5 : ZMod 54453282133) ^ 12982 = (5 : ZMod 54453282133) ^ (6491 + 6491) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 6491 * (5 : ZMod 54453282133) ^ 6491 := by rw [pow_add]
          _ = 19911487702 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 54453282133) ^ 25965 = 16889917625 := by
        calc
          (5 : ZMod 54453282133) ^ 25965 = (5 : ZMod 54453282133) ^ (12982 + 12982 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 12982 * (5 : ZMod 54453282133) ^ 12982) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 16889917625 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 54453282133) ^ 51930 = 13646918404 := by
        calc
          (5 : ZMod 54453282133) ^ 51930 = (5 : ZMod 54453282133) ^ (25965 + 25965) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 25965 * (5 : ZMod 54453282133) ^ 25965 := by rw [pow_add]
          _ = 13646918404 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 54453282133) ^ 103861 = 25724894011 := by
        calc
          (5 : ZMod 54453282133) ^ 103861 = (5 : ZMod 54453282133) ^ (51930 + 51930 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 51930 * (5 : ZMod 54453282133) ^ 51930) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 25724894011 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 54453282133) ^ 207722 = 47795876390 := by
        calc
          (5 : ZMod 54453282133) ^ 207722 = (5 : ZMod 54453282133) ^ (103861 + 103861) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 103861 * (5 : ZMod 54453282133) ^ 103861 := by rw [pow_add]
          _ = 47795876390 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 54453282133) ^ 415445 = 292429718 := by
        calc
          (5 : ZMod 54453282133) ^ 415445 = (5 : ZMod 54453282133) ^ (207722 + 207722 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 207722 * (5 : ZMod 54453282133) ^ 207722) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 292429718 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 54453282133) ^ 830891 = 33827468872 := by
        calc
          (5 : ZMod 54453282133) ^ 830891 = (5 : ZMod 54453282133) ^ (415445 + 415445 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 415445 * (5 : ZMod 54453282133) ^ 415445) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 33827468872 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 54453282133) ^ 1661782 = 50454628117 := by
        calc
          (5 : ZMod 54453282133) ^ 1661782 = (5 : ZMod 54453282133) ^ (830891 + 830891) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 830891 * (5 : ZMod 54453282133) ^ 830891 := by rw [pow_add]
          _ = 50454628117 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 54453282133) ^ 3323564 = 13576527237 := by
        calc
          (5 : ZMod 54453282133) ^ 3323564 = (5 : ZMod 54453282133) ^ (1661782 + 1661782) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 1661782 * (5 : ZMod 54453282133) ^ 1661782 := by rw [pow_add]
          _ = 13576527237 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 54453282133) ^ 6647129 = 23512392888 := by
        calc
          (5 : ZMod 54453282133) ^ 6647129 = (5 : ZMod 54453282133) ^ (3323564 + 3323564 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 3323564 * (5 : ZMod 54453282133) ^ 3323564) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 23512392888 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 54453282133) ^ 13294258 = 30081436453 := by
        calc
          (5 : ZMod 54453282133) ^ 13294258 = (5 : ZMod 54453282133) ^ (6647129 + 6647129) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 6647129 * (5 : ZMod 54453282133) ^ 6647129 := by rw [pow_add]
          _ = 30081436453 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 54453282133) ^ 26588516 = 30832759499 := by
        calc
          (5 : ZMod 54453282133) ^ 26588516 = (5 : ZMod 54453282133) ^ (13294258 + 13294258) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 13294258 * (5 : ZMod 54453282133) ^ 13294258 := by rw [pow_add]
          _ = 30832759499 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 54453282133) ^ 53177033 = 8918089065 := by
        calc
          (5 : ZMod 54453282133) ^ 53177033 = (5 : ZMod 54453282133) ^ (26588516 + 26588516 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 26588516 * (5 : ZMod 54453282133) ^ 26588516) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 8918089065 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 54453282133) ^ 106354066 = 28083284789 := by
        calc
          (5 : ZMod 54453282133) ^ 106354066 = (5 : ZMod 54453282133) ^ (53177033 + 53177033) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 53177033 * (5 : ZMod 54453282133) ^ 53177033 := by rw [pow_add]
          _ = 28083284789 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 54453282133) ^ 212708133 = 29414126628 := by
        calc
          (5 : ZMod 54453282133) ^ 212708133 = (5 : ZMod 54453282133) ^ (106354066 + 106354066 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 106354066 * (5 : ZMod 54453282133) ^ 106354066) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 29414126628 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 54453282133) ^ 425416266 = 10063848149 := by
        calc
          (5 : ZMod 54453282133) ^ 425416266 = (5 : ZMod 54453282133) ^ (212708133 + 212708133) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 212708133 * (5 : ZMod 54453282133) ^ 212708133 := by rw [pow_add]
          _ = 10063848149 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 54453282133) ^ 850832533 = 24097793928 := by
        calc
          (5 : ZMod 54453282133) ^ 850832533 = (5 : ZMod 54453282133) ^ (425416266 + 425416266 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 425416266 * (5 : ZMod 54453282133) ^ 425416266) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 24097793928 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 54453282133) ^ 1701665066 = 46497826631 := by
        calc
          (5 : ZMod 54453282133) ^ 1701665066 = (5 : ZMod 54453282133) ^ (850832533 + 850832533) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 850832533 * (5 : ZMod 54453282133) ^ 850832533 := by rw [pow_add]
          _ = 46497826631 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 54453282133) ^ 3403330133 = 24743890413 := by
        calc
          (5 : ZMod 54453282133) ^ 3403330133 = (5 : ZMod 54453282133) ^ (1701665066 + 1701665066 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1701665066 * (5 : ZMod 54453282133) ^ 1701665066) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 24743890413 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 54453282133) ^ 6806660266 = 26248616957 := by
        calc
          (5 : ZMod 54453282133) ^ 6806660266 = (5 : ZMod 54453282133) ^ (3403330133 + 3403330133) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 3403330133 * (5 : ZMod 54453282133) ^ 3403330133 := by rw [pow_add]
          _ = 26248616957 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 54453282133) ^ 13613320533 = 51017490898 := by
        calc
          (5 : ZMod 54453282133) ^ 13613320533 = (5 : ZMod 54453282133) ^ (6806660266 + 6806660266 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 6806660266 * (5 : ZMod 54453282133) ^ 6806660266) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 51017490898 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 54453282133) ^ 27226641066 = 54453282132 := by
        calc
          (5 : ZMod 54453282133) ^ 27226641066 = (5 : ZMod 54453282133) ^ (13613320533 + 13613320533) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 13613320533 * (5 : ZMod 54453282133) ^ 13613320533 := by rw [pow_add]
          _ = 54453282132 := by rw [factor_0_33]; decide
      change (5 : ZMod 54453282133) ^ 27226641066 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (5 : ZMod 54453282133) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 54453282133) ^ 2 = 25 := by
        calc
          (5 : ZMod 54453282133) ^ 2 = (5 : ZMod 54453282133) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 1 * (5 : ZMod 54453282133) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 54453282133) ^ 4 = 625 := by
        calc
          (5 : ZMod 54453282133) ^ 4 = (5 : ZMod 54453282133) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 2 * (5 : ZMod 54453282133) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 54453282133) ^ 8 = 390625 := by
        calc
          (5 : ZMod 54453282133) ^ 8 = (5 : ZMod 54453282133) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 4 * (5 : ZMod 54453282133) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 54453282133) ^ 16 = 43681326359 := by
        calc
          (5 : ZMod 54453282133) ^ 16 = (5 : ZMod 54453282133) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 8 * (5 : ZMod 54453282133) ^ 8 := by rw [pow_add]
          _ = 43681326359 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 54453282133) ^ 33 = 40393662872 := by
        calc
          (5 : ZMod 54453282133) ^ 33 = (5 : ZMod 54453282133) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 16 * (5 : ZMod 54453282133) ^ 16) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 40393662872 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 54453282133) ^ 67 = 28918243269 := by
        calc
          (5 : ZMod 54453282133) ^ 67 = (5 : ZMod 54453282133) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 33 * (5 : ZMod 54453282133) ^ 33) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 28918243269 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 54453282133) ^ 135 = 19499250571 := by
        calc
          (5 : ZMod 54453282133) ^ 135 = (5 : ZMod 54453282133) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 67 * (5 : ZMod 54453282133) ^ 67) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 19499250571 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 54453282133) ^ 270 = 9551358245 := by
        calc
          (5 : ZMod 54453282133) ^ 270 = (5 : ZMod 54453282133) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 135 * (5 : ZMod 54453282133) ^ 135 := by rw [pow_add]
          _ = 9551358245 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 54453282133) ^ 540 = 9284440737 := by
        calc
          (5 : ZMod 54453282133) ^ 540 = (5 : ZMod 54453282133) ^ (270 + 270) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 270 * (5 : ZMod 54453282133) ^ 270 := by rw [pow_add]
          _ = 9284440737 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 54453282133) ^ 1081 = 10301522923 := by
        calc
          (5 : ZMod 54453282133) ^ 1081 = (5 : ZMod 54453282133) ^ (540 + 540 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 540 * (5 : ZMod 54453282133) ^ 540) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 10301522923 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 54453282133) ^ 2163 = 32263377639 := by
        calc
          (5 : ZMod 54453282133) ^ 2163 = (5 : ZMod 54453282133) ^ (1081 + 1081 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1081 * (5 : ZMod 54453282133) ^ 1081) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 32263377639 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 54453282133) ^ 4327 = 24280079400 := by
        calc
          (5 : ZMod 54453282133) ^ 4327 = (5 : ZMod 54453282133) ^ (2163 + 2163 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 2163 * (5 : ZMod 54453282133) ^ 2163) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 24280079400 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 54453282133) ^ 8655 = 23575702193 := by
        calc
          (5 : ZMod 54453282133) ^ 8655 = (5 : ZMod 54453282133) ^ (4327 + 4327 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 4327 * (5 : ZMod 54453282133) ^ 4327) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 23575702193 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 54453282133) ^ 17310 = 27314532051 := by
        calc
          (5 : ZMod 54453282133) ^ 17310 = (5 : ZMod 54453282133) ^ (8655 + 8655) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 8655 * (5 : ZMod 54453282133) ^ 8655 := by rw [pow_add]
          _ = 27314532051 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 54453282133) ^ 34620 = 14486389194 := by
        calc
          (5 : ZMod 54453282133) ^ 34620 = (5 : ZMod 54453282133) ^ (17310 + 17310) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 17310 * (5 : ZMod 54453282133) ^ 17310 := by rw [pow_add]
          _ = 14486389194 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 54453282133) ^ 69240 = 9707191063 := by
        calc
          (5 : ZMod 54453282133) ^ 69240 = (5 : ZMod 54453282133) ^ (34620 + 34620) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 34620 * (5 : ZMod 54453282133) ^ 34620 := by rw [pow_add]
          _ = 9707191063 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 54453282133) ^ 138481 = 21605678665 := by
        calc
          (5 : ZMod 54453282133) ^ 138481 = (5 : ZMod 54453282133) ^ (69240 + 69240 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 69240 * (5 : ZMod 54453282133) ^ 69240) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 21605678665 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 54453282133) ^ 276963 = 20578332930 := by
        calc
          (5 : ZMod 54453282133) ^ 276963 = (5 : ZMod 54453282133) ^ (138481 + 138481 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 138481 * (5 : ZMod 54453282133) ^ 138481) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 20578332930 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 54453282133) ^ 553927 = 31505267352 := by
        calc
          (5 : ZMod 54453282133) ^ 553927 = (5 : ZMod 54453282133) ^ (276963 + 276963 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 276963 * (5 : ZMod 54453282133) ^ 276963) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 31505267352 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 54453282133) ^ 1107854 = 1379253740 := by
        calc
          (5 : ZMod 54453282133) ^ 1107854 = (5 : ZMod 54453282133) ^ (553927 + 553927) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 553927 * (5 : ZMod 54453282133) ^ 553927 := by rw [pow_add]
          _ = 1379253740 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 54453282133) ^ 2215709 = 16277534140 := by
        calc
          (5 : ZMod 54453282133) ^ 2215709 = (5 : ZMod 54453282133) ^ (1107854 + 1107854 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1107854 * (5 : ZMod 54453282133) ^ 1107854) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 16277534140 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 54453282133) ^ 4431419 = 45989259055 := by
        calc
          (5 : ZMod 54453282133) ^ 4431419 = (5 : ZMod 54453282133) ^ (2215709 + 2215709 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 2215709 * (5 : ZMod 54453282133) ^ 2215709) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 45989259055 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 54453282133) ^ 8862838 = 5660472958 := by
        calc
          (5 : ZMod 54453282133) ^ 8862838 = (5 : ZMod 54453282133) ^ (4431419 + 4431419) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 4431419 * (5 : ZMod 54453282133) ^ 4431419 := by rw [pow_add]
          _ = 5660472958 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 54453282133) ^ 17725677 = 19809473564 := by
        calc
          (5 : ZMod 54453282133) ^ 17725677 = (5 : ZMod 54453282133) ^ (8862838 + 8862838 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 8862838 * (5 : ZMod 54453282133) ^ 8862838) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 19809473564 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 54453282133) ^ 35451355 = 32548457951 := by
        calc
          (5 : ZMod 54453282133) ^ 35451355 = (5 : ZMod 54453282133) ^ (17725677 + 17725677 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 17725677 * (5 : ZMod 54453282133) ^ 17725677) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 32548457951 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 54453282133) ^ 70902711 = 2793724476 := by
        calc
          (5 : ZMod 54453282133) ^ 70902711 = (5 : ZMod 54453282133) ^ (35451355 + 35451355 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 35451355 * (5 : ZMod 54453282133) ^ 35451355) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 2793724476 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 54453282133) ^ 141805422 = 28899654034 := by
        calc
          (5 : ZMod 54453282133) ^ 141805422 = (5 : ZMod 54453282133) ^ (70902711 + 70902711) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 70902711 * (5 : ZMod 54453282133) ^ 70902711 := by rw [pow_add]
          _ = 28899654034 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 54453282133) ^ 283610844 = 53336191707 := by
        calc
          (5 : ZMod 54453282133) ^ 283610844 = (5 : ZMod 54453282133) ^ (141805422 + 141805422) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 141805422 * (5 : ZMod 54453282133) ^ 141805422 := by rw [pow_add]
          _ = 53336191707 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 54453282133) ^ 567221688 = 18964922785 := by
        calc
          (5 : ZMod 54453282133) ^ 567221688 = (5 : ZMod 54453282133) ^ (283610844 + 283610844) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 283610844 * (5 : ZMod 54453282133) ^ 283610844 := by rw [pow_add]
          _ = 18964922785 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 54453282133) ^ 1134443377 = 1669930810 := by
        calc
          (5 : ZMod 54453282133) ^ 1134443377 = (5 : ZMod 54453282133) ^ (567221688 + 567221688 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 567221688 * (5 : ZMod 54453282133) ^ 567221688) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 1669930810 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 54453282133) ^ 2268886755 = 45275167927 := by
        calc
          (5 : ZMod 54453282133) ^ 2268886755 = (5 : ZMod 54453282133) ^ (1134443377 + 1134443377 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1134443377 * (5 : ZMod 54453282133) ^ 1134443377) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 45275167927 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 54453282133) ^ 4537773511 = 18550192422 := by
        calc
          (5 : ZMod 54453282133) ^ 4537773511 = (5 : ZMod 54453282133) ^ (2268886755 + 2268886755 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 2268886755 * (5 : ZMod 54453282133) ^ 2268886755) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 18550192422 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 54453282133) ^ 9075547022 = 46699060795 := by
        calc
          (5 : ZMod 54453282133) ^ 9075547022 = (5 : ZMod 54453282133) ^ (4537773511 + 4537773511) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 4537773511 * (5 : ZMod 54453282133) ^ 4537773511 := by rw [pow_add]
          _ = 46699060795 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 54453282133) ^ 18151094044 = 46699060794 := by
        calc
          (5 : ZMod 54453282133) ^ 18151094044 = (5 : ZMod 54453282133) ^ (9075547022 + 9075547022) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 9075547022 * (5 : ZMod 54453282133) ^ 9075547022 := by rw [pow_add]
          _ = 46699060794 := by rw [factor_1_33]; decide
      change (5 : ZMod 54453282133) ^ 18151094044 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (5 : ZMod 54453282133) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 54453282133) ^ 3 = 125 := by
        calc
          (5 : ZMod 54453282133) ^ 3 = (5 : ZMod 54453282133) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = ((5 : ZMod 54453282133) ^ 1 * (5 : ZMod 54453282133) ^ 1) * (5 : ZMod 54453282133) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 54453282133) ^ 6 = 15625 := by
        calc
          (5 : ZMod 54453282133) ^ 6 = (5 : ZMod 54453282133) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 3 * (5 : ZMod 54453282133) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 54453282133) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 54453282133) ^ 12 = (5 : ZMod 54453282133) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 54453282133) ^ n) (by norm_num)
          _ = (5 : ZMod 54453282133) ^ 6 * (5 : ZMod 54453282133) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_2_2]; decide
      change (5 : ZMod 54453282133) ^ 12 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_54453282133

end TotientTailPeriodKiller
end Erdos249257
