import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_542848051 : Nat.Prime 542848051 := by
  apply lucas_primality 542848051 (2 : ZMod 542848051)
  ·
      have fermat_0 : (2 : ZMod 542848051) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 542848051) ^ 2 = 4 := by
        calc
          (2 : ZMod 542848051) ^ 2 = (2 : ZMod 542848051) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1 * (2 : ZMod 542848051) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 542848051) ^ 4 = 16 := by
        calc
          (2 : ZMod 542848051) ^ 4 = (2 : ZMod 542848051) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 2 * (2 : ZMod 542848051) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 542848051) ^ 8 = 256 := by
        calc
          (2 : ZMod 542848051) ^ 8 = (2 : ZMod 542848051) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 4 * (2 : ZMod 542848051) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 542848051) ^ 16 = 65536 := by
        calc
          (2 : ZMod 542848051) ^ 16 = (2 : ZMod 542848051) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 8 * (2 : ZMod 542848051) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 542848051) ^ 32 = 495030939 := by
        calc
          (2 : ZMod 542848051) ^ 32 = (2 : ZMod 542848051) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 16 * (2 : ZMod 542848051) ^ 16 := by rw [pow_add]
          _ = 495030939 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 542848051) ^ 64 = 209208544 := by
        calc
          (2 : ZMod 542848051) ^ 64 = (2 : ZMod 542848051) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 32 * (2 : ZMod 542848051) ^ 32 := by rw [pow_add]
          _ = 209208544 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 542848051) ^ 129 = 377980954 := by
        calc
          (2 : ZMod 542848051) ^ 129 = (2 : ZMod 542848051) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 64 * (2 : ZMod 542848051) ^ 64) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 377980954 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 542848051) ^ 258 = 486606264 := by
        calc
          (2 : ZMod 542848051) ^ 258 = (2 : ZMod 542848051) ^ (129 + 129) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 129 * (2 : ZMod 542848051) ^ 129 := by rw [pow_add]
          _ = 486606264 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 542848051) ^ 517 = 393735725 := by
        calc
          (2 : ZMod 542848051) ^ 517 = (2 : ZMod 542848051) ^ (258 + 258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 258 * (2 : ZMod 542848051) ^ 258) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 393735725 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 542848051) ^ 1035 = 258943754 := by
        calc
          (2 : ZMod 542848051) ^ 1035 = (2 : ZMod 542848051) ^ (517 + 517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 517 * (2 : ZMod 542848051) ^ 517) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 258943754 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 542848051) ^ 2070 = 92544499 := by
        calc
          (2 : ZMod 542848051) ^ 2070 = (2 : ZMod 542848051) ^ (1035 + 1035) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1035 * (2 : ZMod 542848051) ^ 1035 := by rw [pow_add]
          _ = 92544499 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 542848051) ^ 4141 = 359505561 := by
        calc
          (2 : ZMod 542848051) ^ 4141 = (2 : ZMod 542848051) ^ (2070 + 2070 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 2070 * (2 : ZMod 542848051) ^ 2070) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 359505561 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 542848051) ^ 8283 = 201368697 := by
        calc
          (2 : ZMod 542848051) ^ 8283 = (2 : ZMod 542848051) ^ (4141 + 4141 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 4141 * (2 : ZMod 542848051) ^ 4141) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 201368697 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 542848051) ^ 16566 = 12661083 := by
        calc
          (2 : ZMod 542848051) ^ 16566 = (2 : ZMod 542848051) ^ (8283 + 8283) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 8283 * (2 : ZMod 542848051) ^ 8283 := by rw [pow_add]
          _ = 12661083 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 542848051) ^ 33132 = 536120640 := by
        calc
          (2 : ZMod 542848051) ^ 33132 = (2 : ZMod 542848051) ^ (16566 + 16566) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 16566 * (2 : ZMod 542848051) ^ 16566 := by rw [pow_add]
          _ = 536120640 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 542848051) ^ 66265 = 4957949 := by
        calc
          (2 : ZMod 542848051) ^ 66265 = (2 : ZMod 542848051) ^ (33132 + 33132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 33132 * (2 : ZMod 542848051) ^ 33132) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 4957949 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 542848051) ^ 132531 = 25682438 := by
        calc
          (2 : ZMod 542848051) ^ 132531 = (2 : ZMod 542848051) ^ (66265 + 66265 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 66265 * (2 : ZMod 542848051) ^ 66265) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 25682438 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 542848051) ^ 265062 = 97256294 := by
        calc
          (2 : ZMod 542848051) ^ 265062 = (2 : ZMod 542848051) ^ (132531 + 132531) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 132531 * (2 : ZMod 542848051) ^ 132531 := by rw [pow_add]
          _ = 97256294 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 542848051) ^ 530125 = 142182877 := by
        calc
          (2 : ZMod 542848051) ^ 530125 = (2 : ZMod 542848051) ^ (265062 + 265062 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 265062 * (2 : ZMod 542848051) ^ 265062) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 142182877 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 542848051) ^ 1060250 = 212216110 := by
        calc
          (2 : ZMod 542848051) ^ 1060250 = (2 : ZMod 542848051) ^ (530125 + 530125) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 530125 * (2 : ZMod 542848051) ^ 530125 := by rw [pow_add]
          _ = 212216110 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 542848051) ^ 2120500 = 392221903 := by
        calc
          (2 : ZMod 542848051) ^ 2120500 = (2 : ZMod 542848051) ^ (1060250 + 1060250) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1060250 * (2 : ZMod 542848051) ^ 1060250 := by rw [pow_add]
          _ = 392221903 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 542848051) ^ 4241000 = 425270135 := by
        calc
          (2 : ZMod 542848051) ^ 4241000 = (2 : ZMod 542848051) ^ (2120500 + 2120500) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 2120500 * (2 : ZMod 542848051) ^ 2120500 := by rw [pow_add]
          _ = 425270135 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 542848051) ^ 8482000 = 499363724 := by
        calc
          (2 : ZMod 542848051) ^ 8482000 = (2 : ZMod 542848051) ^ (4241000 + 4241000) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 4241000 * (2 : ZMod 542848051) ^ 4241000 := by rw [pow_add]
          _ = 499363724 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 542848051) ^ 16964001 = 185224267 := by
        calc
          (2 : ZMod 542848051) ^ 16964001 = (2 : ZMod 542848051) ^ (8482000 + 8482000 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 8482000 * (2 : ZMod 542848051) ^ 8482000) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 185224267 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 542848051) ^ 33928003 = 468904560 := by
        calc
          (2 : ZMod 542848051) ^ 33928003 = (2 : ZMod 542848051) ^ (16964001 + 16964001 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 16964001 * (2 : ZMod 542848051) ^ 16964001) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 468904560 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 542848051) ^ 67856006 = 464260145 := by
        calc
          (2 : ZMod 542848051) ^ 67856006 = (2 : ZMod 542848051) ^ (33928003 + 33928003) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 33928003 * (2 : ZMod 542848051) ^ 33928003 := by rw [pow_add]
          _ = 464260145 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 542848051) ^ 135712012 = 151662645 := by
        calc
          (2 : ZMod 542848051) ^ 135712012 = (2 : ZMod 542848051) ^ (67856006 + 67856006) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 67856006 * (2 : ZMod 542848051) ^ 67856006 := by rw [pow_add]
          _ = 151662645 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 542848051) ^ 271424025 = 542848050 := by
        calc
          (2 : ZMod 542848051) ^ 271424025 = (2 : ZMod 542848051) ^ (135712012 + 135712012 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 135712012 * (2 : ZMod 542848051) ^ 135712012) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 542848050 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 542848051) ^ 542848050 = 1 := by
        calc
          (2 : ZMod 542848051) ^ 542848050 = (2 : ZMod 542848051) ^ (271424025 + 271424025) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 271424025 * (2 : ZMod 542848051) ^ 271424025 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 2), (19, 1), (173, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 2), (19, 1), (173, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod = 542848051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 542848051) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 542848051) ^ 2 = 4 := by
        calc
          (2 : ZMod 542848051) ^ 2 = (2 : ZMod 542848051) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1 * (2 : ZMod 542848051) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 542848051) ^ 4 = 16 := by
        calc
          (2 : ZMod 542848051) ^ 4 = (2 : ZMod 542848051) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 2 * (2 : ZMod 542848051) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 542848051) ^ 8 = 256 := by
        calc
          (2 : ZMod 542848051) ^ 8 = (2 : ZMod 542848051) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 4 * (2 : ZMod 542848051) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 542848051) ^ 16 = 65536 := by
        calc
          (2 : ZMod 542848051) ^ 16 = (2 : ZMod 542848051) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 8 * (2 : ZMod 542848051) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 542848051) ^ 32 = 495030939 := by
        calc
          (2 : ZMod 542848051) ^ 32 = (2 : ZMod 542848051) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 16 * (2 : ZMod 542848051) ^ 16 := by rw [pow_add]
          _ = 495030939 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 542848051) ^ 64 = 209208544 := by
        calc
          (2 : ZMod 542848051) ^ 64 = (2 : ZMod 542848051) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 32 * (2 : ZMod 542848051) ^ 32 := by rw [pow_add]
          _ = 209208544 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 542848051) ^ 129 = 377980954 := by
        calc
          (2 : ZMod 542848051) ^ 129 = (2 : ZMod 542848051) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 64 * (2 : ZMod 542848051) ^ 64) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 377980954 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 542848051) ^ 258 = 486606264 := by
        calc
          (2 : ZMod 542848051) ^ 258 = (2 : ZMod 542848051) ^ (129 + 129) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 129 * (2 : ZMod 542848051) ^ 129 := by rw [pow_add]
          _ = 486606264 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 542848051) ^ 517 = 393735725 := by
        calc
          (2 : ZMod 542848051) ^ 517 = (2 : ZMod 542848051) ^ (258 + 258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 258 * (2 : ZMod 542848051) ^ 258) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 393735725 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 542848051) ^ 1035 = 258943754 := by
        calc
          (2 : ZMod 542848051) ^ 1035 = (2 : ZMod 542848051) ^ (517 + 517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 517 * (2 : ZMod 542848051) ^ 517) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 258943754 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 542848051) ^ 2070 = 92544499 := by
        calc
          (2 : ZMod 542848051) ^ 2070 = (2 : ZMod 542848051) ^ (1035 + 1035) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1035 * (2 : ZMod 542848051) ^ 1035 := by rw [pow_add]
          _ = 92544499 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 542848051) ^ 4141 = 359505561 := by
        calc
          (2 : ZMod 542848051) ^ 4141 = (2 : ZMod 542848051) ^ (2070 + 2070 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 2070 * (2 : ZMod 542848051) ^ 2070) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 359505561 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 542848051) ^ 8283 = 201368697 := by
        calc
          (2 : ZMod 542848051) ^ 8283 = (2 : ZMod 542848051) ^ (4141 + 4141 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 4141 * (2 : ZMod 542848051) ^ 4141) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 201368697 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 542848051) ^ 16566 = 12661083 := by
        calc
          (2 : ZMod 542848051) ^ 16566 = (2 : ZMod 542848051) ^ (8283 + 8283) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 8283 * (2 : ZMod 542848051) ^ 8283 := by rw [pow_add]
          _ = 12661083 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 542848051) ^ 33132 = 536120640 := by
        calc
          (2 : ZMod 542848051) ^ 33132 = (2 : ZMod 542848051) ^ (16566 + 16566) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 16566 * (2 : ZMod 542848051) ^ 16566 := by rw [pow_add]
          _ = 536120640 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 542848051) ^ 66265 = 4957949 := by
        calc
          (2 : ZMod 542848051) ^ 66265 = (2 : ZMod 542848051) ^ (33132 + 33132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 33132 * (2 : ZMod 542848051) ^ 33132) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 4957949 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 542848051) ^ 132531 = 25682438 := by
        calc
          (2 : ZMod 542848051) ^ 132531 = (2 : ZMod 542848051) ^ (66265 + 66265 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 66265 * (2 : ZMod 542848051) ^ 66265) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 25682438 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 542848051) ^ 265062 = 97256294 := by
        calc
          (2 : ZMod 542848051) ^ 265062 = (2 : ZMod 542848051) ^ (132531 + 132531) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 132531 * (2 : ZMod 542848051) ^ 132531 := by rw [pow_add]
          _ = 97256294 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 542848051) ^ 530125 = 142182877 := by
        calc
          (2 : ZMod 542848051) ^ 530125 = (2 : ZMod 542848051) ^ (265062 + 265062 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 265062 * (2 : ZMod 542848051) ^ 265062) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 142182877 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 542848051) ^ 1060250 = 212216110 := by
        calc
          (2 : ZMod 542848051) ^ 1060250 = (2 : ZMod 542848051) ^ (530125 + 530125) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 530125 * (2 : ZMod 542848051) ^ 530125 := by rw [pow_add]
          _ = 212216110 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 542848051) ^ 2120500 = 392221903 := by
        calc
          (2 : ZMod 542848051) ^ 2120500 = (2 : ZMod 542848051) ^ (1060250 + 1060250) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1060250 * (2 : ZMod 542848051) ^ 1060250 := by rw [pow_add]
          _ = 392221903 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 542848051) ^ 4241000 = 425270135 := by
        calc
          (2 : ZMod 542848051) ^ 4241000 = (2 : ZMod 542848051) ^ (2120500 + 2120500) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 2120500 * (2 : ZMod 542848051) ^ 2120500 := by rw [pow_add]
          _ = 425270135 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 542848051) ^ 8482000 = 499363724 := by
        calc
          (2 : ZMod 542848051) ^ 8482000 = (2 : ZMod 542848051) ^ (4241000 + 4241000) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 4241000 * (2 : ZMod 542848051) ^ 4241000 := by rw [pow_add]
          _ = 499363724 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 542848051) ^ 16964001 = 185224267 := by
        calc
          (2 : ZMod 542848051) ^ 16964001 = (2 : ZMod 542848051) ^ (8482000 + 8482000 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 8482000 * (2 : ZMod 542848051) ^ 8482000) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 185224267 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 542848051) ^ 33928003 = 468904560 := by
        calc
          (2 : ZMod 542848051) ^ 33928003 = (2 : ZMod 542848051) ^ (16964001 + 16964001 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 16964001 * (2 : ZMod 542848051) ^ 16964001) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 468904560 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 542848051) ^ 67856006 = 464260145 := by
        calc
          (2 : ZMod 542848051) ^ 67856006 = (2 : ZMod 542848051) ^ (33928003 + 33928003) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 33928003 * (2 : ZMod 542848051) ^ 33928003 := by rw [pow_add]
          _ = 464260145 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 542848051) ^ 135712012 = 151662645 := by
        calc
          (2 : ZMod 542848051) ^ 135712012 = (2 : ZMod 542848051) ^ (67856006 + 67856006) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 67856006 * (2 : ZMod 542848051) ^ 67856006 := by rw [pow_add]
          _ = 151662645 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 542848051) ^ 271424025 = 542848050 := by
        calc
          (2 : ZMod 542848051) ^ 271424025 = (2 : ZMod 542848051) ^ (135712012 + 135712012 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 135712012 * (2 : ZMod 542848051) ^ 135712012) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 542848050 := by rw [factor_0_27]; decide
      change (2 : ZMod 542848051) ^ 271424025 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (2 : ZMod 542848051) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 542848051) ^ 2 = 4 := by
        calc
          (2 : ZMod 542848051) ^ 2 = (2 : ZMod 542848051) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1 * (2 : ZMod 542848051) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 542848051) ^ 5 = 32 := by
        calc
          (2 : ZMod 542848051) ^ 5 = (2 : ZMod 542848051) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 2 * (2 : ZMod 542848051) ^ 2) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 542848051) ^ 10 = 1024 := by
        calc
          (2 : ZMod 542848051) ^ 10 = (2 : ZMod 542848051) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 5 * (2 : ZMod 542848051) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 542848051) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 542848051) ^ 21 = (2 : ZMod 542848051) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 10 * (2 : ZMod 542848051) ^ 10) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 542848051) ^ 43 = 326051855 := by
        calc
          (2 : ZMod 542848051) ^ 43 = (2 : ZMod 542848051) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 21 * (2 : ZMod 542848051) ^ 21) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 326051855 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 542848051) ^ 86 = 215134681 := by
        calc
          (2 : ZMod 542848051) ^ 86 = (2 : ZMod 542848051) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 43 * (2 : ZMod 542848051) ^ 43 := by rw [pow_add]
          _ = 215134681 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 542848051) ^ 172 = 364355403 := by
        calc
          (2 : ZMod 542848051) ^ 172 = (2 : ZMod 542848051) ^ (86 + 86) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 86 * (2 : ZMod 542848051) ^ 86 := by rw [pow_add]
          _ = 364355403 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 542848051) ^ 345 = 63763625 := by
        calc
          (2 : ZMod 542848051) ^ 345 = (2 : ZMod 542848051) ^ (172 + 172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 172 * (2 : ZMod 542848051) ^ 172) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 63763625 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 542848051) ^ 690 = 426075069 := by
        calc
          (2 : ZMod 542848051) ^ 690 = (2 : ZMod 542848051) ^ (345 + 345) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 345 * (2 : ZMod 542848051) ^ 345 := by rw [pow_add]
          _ = 426075069 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 542848051) ^ 1380 = 477115237 := by
        calc
          (2 : ZMod 542848051) ^ 1380 = (2 : ZMod 542848051) ^ (690 + 690) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 690 * (2 : ZMod 542848051) ^ 690 := by rw [pow_add]
          _ = 477115237 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 542848051) ^ 2761 = 491823529 := by
        calc
          (2 : ZMod 542848051) ^ 2761 = (2 : ZMod 542848051) ^ (1380 + 1380 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 1380 * (2 : ZMod 542848051) ^ 1380) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 491823529 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 542848051) ^ 5522 = 421340280 := by
        calc
          (2 : ZMod 542848051) ^ 5522 = (2 : ZMod 542848051) ^ (2761 + 2761) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 2761 * (2 : ZMod 542848051) ^ 2761 := by rw [pow_add]
          _ = 421340280 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 542848051) ^ 11044 = 318217289 := by
        calc
          (2 : ZMod 542848051) ^ 11044 = (2 : ZMod 542848051) ^ (5522 + 5522) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 5522 * (2 : ZMod 542848051) ^ 5522 := by rw [pow_add]
          _ = 318217289 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 542848051) ^ 22088 = 2948936 := by
        calc
          (2 : ZMod 542848051) ^ 22088 = (2 : ZMod 542848051) ^ (11044 + 11044) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 11044 * (2 : ZMod 542848051) ^ 11044 := by rw [pow_add]
          _ = 2948936 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 542848051) ^ 44177 = 138358203 := by
        calc
          (2 : ZMod 542848051) ^ 44177 = (2 : ZMod 542848051) ^ (22088 + 22088 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 22088 * (2 : ZMod 542848051) ^ 22088) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 138358203 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 542848051) ^ 88354 = 295469362 := by
        calc
          (2 : ZMod 542848051) ^ 88354 = (2 : ZMod 542848051) ^ (44177 + 44177) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 44177 * (2 : ZMod 542848051) ^ 44177 := by rw [pow_add]
          _ = 295469362 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 542848051) ^ 176708 = 112407012 := by
        calc
          (2 : ZMod 542848051) ^ 176708 = (2 : ZMod 542848051) ^ (88354 + 88354) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 88354 * (2 : ZMod 542848051) ^ 88354 := by rw [pow_add]
          _ = 112407012 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 542848051) ^ 353416 = 226059685 := by
        calc
          (2 : ZMod 542848051) ^ 353416 = (2 : ZMod 542848051) ^ (176708 + 176708) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 176708 * (2 : ZMod 542848051) ^ 176708 := by rw [pow_add]
          _ = 226059685 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 542848051) ^ 706833 = 269144456 := by
        calc
          (2 : ZMod 542848051) ^ 706833 = (2 : ZMod 542848051) ^ (353416 + 353416 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 353416 * (2 : ZMod 542848051) ^ 353416) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 269144456 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 542848051) ^ 1413666 = 431273171 := by
        calc
          (2 : ZMod 542848051) ^ 1413666 = (2 : ZMod 542848051) ^ (706833 + 706833) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 706833 * (2 : ZMod 542848051) ^ 706833 := by rw [pow_add]
          _ = 431273171 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 542848051) ^ 2827333 = 523664766 := by
        calc
          (2 : ZMod 542848051) ^ 2827333 = (2 : ZMod 542848051) ^ (1413666 + 1413666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 1413666 * (2 : ZMod 542848051) ^ 1413666) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 523664766 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 542848051) ^ 5654667 = 202148344 := by
        calc
          (2 : ZMod 542848051) ^ 5654667 = (2 : ZMod 542848051) ^ (2827333 + 2827333 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 2827333 * (2 : ZMod 542848051) ^ 2827333) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 202148344 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 542848051) ^ 11309334 = 332193223 := by
        calc
          (2 : ZMod 542848051) ^ 11309334 = (2 : ZMod 542848051) ^ (5654667 + 5654667) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 5654667 * (2 : ZMod 542848051) ^ 5654667 := by rw [pow_add]
          _ = 332193223 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 542848051) ^ 22618668 = 93594403 := by
        calc
          (2 : ZMod 542848051) ^ 22618668 = (2 : ZMod 542848051) ^ (11309334 + 11309334) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 11309334 * (2 : ZMod 542848051) ^ 11309334 := by rw [pow_add]
          _ = 93594403 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 542848051) ^ 45237337 = 289835867 := by
        calc
          (2 : ZMod 542848051) ^ 45237337 = (2 : ZMod 542848051) ^ (22618668 + 22618668 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 22618668 * (2 : ZMod 542848051) ^ 22618668) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 289835867 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 542848051) ^ 90474675 = 384425667 := by
        calc
          (2 : ZMod 542848051) ^ 90474675 = (2 : ZMod 542848051) ^ (45237337 + 45237337 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 45237337 * (2 : ZMod 542848051) ^ 45237337) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 384425667 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 542848051) ^ 180949350 = 384425666 := by
        calc
          (2 : ZMod 542848051) ^ 180949350 = (2 : ZMod 542848051) ^ (90474675 + 90474675) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 90474675 * (2 : ZMod 542848051) ^ 90474675 := by rw [pow_add]
          _ = 384425666 := by rw [factor_1_26]; decide
      change (2 : ZMod 542848051) ^ 180949350 ≠ 1
      rw [factor_1_27]
      decide
    ·
      have factor_2_0 : (2 : ZMod 542848051) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 542848051) ^ 3 = 8 := by
        calc
          (2 : ZMod 542848051) ^ 3 = (2 : ZMod 542848051) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 1 * (2 : ZMod 542848051) ^ 1) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 542848051) ^ 6 = 64 := by
        calc
          (2 : ZMod 542848051) ^ 6 = (2 : ZMod 542848051) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 3 * (2 : ZMod 542848051) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 542848051) ^ 12 = 4096 := by
        calc
          (2 : ZMod 542848051) ^ 12 = (2 : ZMod 542848051) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 6 * (2 : ZMod 542848051) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 542848051) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 542848051) ^ 25 = (2 : ZMod 542848051) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 12 * (2 : ZMod 542848051) ^ 12) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 542848051) ^ 51 = 413523077 := by
        calc
          (2 : ZMod 542848051) ^ 51 = (2 : ZMod 542848051) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 25 * (2 : ZMod 542848051) ^ 25) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 413523077 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 542848051) ^ 103 = 433746888 := by
        calc
          (2 : ZMod 542848051) ^ 103 = (2 : ZMod 542848051) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 51 * (2 : ZMod 542848051) ^ 51) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 433746888 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 542848051) ^ 207 = 165648661 := by
        calc
          (2 : ZMod 542848051) ^ 207 = (2 : ZMod 542848051) ^ (103 + 103 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 103 * (2 : ZMod 542848051) ^ 103) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 165648661 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 542848051) ^ 414 = 30942916 := by
        calc
          (2 : ZMod 542848051) ^ 414 = (2 : ZMod 542848051) ^ (207 + 207) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 207 * (2 : ZMod 542848051) ^ 207 := by rw [pow_add]
          _ = 30942916 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 542848051) ^ 828 = 58038327 := by
        calc
          (2 : ZMod 542848051) ^ 828 = (2 : ZMod 542848051) ^ (414 + 414) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 414 * (2 : ZMod 542848051) ^ 414 := by rw [pow_add]
          _ = 58038327 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 542848051) ^ 1656 = 331472891 := by
        calc
          (2 : ZMod 542848051) ^ 1656 = (2 : ZMod 542848051) ^ (828 + 828) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 828 * (2 : ZMod 542848051) ^ 828 := by rw [pow_add]
          _ = 331472891 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 542848051) ^ 3313 = 209499563 := by
        calc
          (2 : ZMod 542848051) ^ 3313 = (2 : ZMod 542848051) ^ (1656 + 1656 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 1656 * (2 : ZMod 542848051) ^ 1656) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 209499563 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 542848051) ^ 6626 = 187269642 := by
        calc
          (2 : ZMod 542848051) ^ 6626 = (2 : ZMod 542848051) ^ (3313 + 3313) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 3313 * (2 : ZMod 542848051) ^ 3313 := by rw [pow_add]
          _ = 187269642 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 542848051) ^ 13253 = 19508800 := by
        calc
          (2 : ZMod 542848051) ^ 13253 = (2 : ZMod 542848051) ^ (6626 + 6626 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 6626 * (2 : ZMod 542848051) ^ 6626) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 19508800 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 542848051) ^ 26506 = 337491696 := by
        calc
          (2 : ZMod 542848051) ^ 26506 = (2 : ZMod 542848051) ^ (13253 + 13253) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 13253 * (2 : ZMod 542848051) ^ 13253 := by rw [pow_add]
          _ = 337491696 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 542848051) ^ 53012 = 269743375 := by
        calc
          (2 : ZMod 542848051) ^ 53012 = (2 : ZMod 542848051) ^ (26506 + 26506) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 26506 * (2 : ZMod 542848051) ^ 26506 := by rw [pow_add]
          _ = 269743375 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 542848051) ^ 106025 = 23963569 := by
        calc
          (2 : ZMod 542848051) ^ 106025 = (2 : ZMod 542848051) ^ (53012 + 53012 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 53012 * (2 : ZMod 542848051) ^ 53012) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 23963569 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 542848051) ^ 212050 = 285619360 := by
        calc
          (2 : ZMod 542848051) ^ 212050 = (2 : ZMod 542848051) ^ (106025 + 106025) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 106025 * (2 : ZMod 542848051) ^ 106025 := by rw [pow_add]
          _ = 285619360 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 542848051) ^ 424100 = 289355499 := by
        calc
          (2 : ZMod 542848051) ^ 424100 = (2 : ZMod 542848051) ^ (212050 + 212050) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 212050 * (2 : ZMod 542848051) ^ 212050 := by rw [pow_add]
          _ = 289355499 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 542848051) ^ 848200 = 291417099 := by
        calc
          (2 : ZMod 542848051) ^ 848200 = (2 : ZMod 542848051) ^ (424100 + 424100) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 424100 * (2 : ZMod 542848051) ^ 424100 := by rw [pow_add]
          _ = 291417099 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 542848051) ^ 1696400 = 218422871 := by
        calc
          (2 : ZMod 542848051) ^ 1696400 = (2 : ZMod 542848051) ^ (848200 + 848200) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 848200 * (2 : ZMod 542848051) ^ 848200 := by rw [pow_add]
          _ = 218422871 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 542848051) ^ 3392800 = 19602797 := by
        calc
          (2 : ZMod 542848051) ^ 3392800 = (2 : ZMod 542848051) ^ (1696400 + 1696400) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1696400 * (2 : ZMod 542848051) ^ 1696400 := by rw [pow_add]
          _ = 19602797 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 542848051) ^ 6785600 = 425482 := by
        calc
          (2 : ZMod 542848051) ^ 6785600 = (2 : ZMod 542848051) ^ (3392800 + 3392800) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 3392800 * (2 : ZMod 542848051) ^ 3392800 := by rw [pow_add]
          _ = 425482 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 542848051) ^ 13571201 = 533062682 := by
        calc
          (2 : ZMod 542848051) ^ 13571201 = (2 : ZMod 542848051) ^ (6785600 + 6785600 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 6785600 * (2 : ZMod 542848051) ^ 6785600) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 533062682 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 542848051) ^ 27142402 = 478750271 := by
        calc
          (2 : ZMod 542848051) ^ 27142402 = (2 : ZMod 542848051) ^ (13571201 + 13571201) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 13571201 * (2 : ZMod 542848051) ^ 13571201 := by rw [pow_add]
          _ = 478750271 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 542848051) ^ 54284805 = 24625574 := by
        calc
          (2 : ZMod 542848051) ^ 54284805 = (2 : ZMod 542848051) ^ (27142402 + 27142402 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 27142402 * (2 : ZMod 542848051) ^ 27142402) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 24625574 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 542848051) ^ 108569610 = 79969070 := by
        calc
          (2 : ZMod 542848051) ^ 108569610 = (2 : ZMod 542848051) ^ (54284805 + 54284805) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 54284805 * (2 : ZMod 542848051) ^ 54284805 := by rw [pow_add]
          _ = 79969070 := by rw [factor_2_25]; decide
      change (2 : ZMod 542848051) ^ 108569610 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (2 : ZMod 542848051) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 542848051) ^ 3 = 8 := by
        calc
          (2 : ZMod 542848051) ^ 3 = (2 : ZMod 542848051) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 1 * (2 : ZMod 542848051) ^ 1) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 542848051) ^ 6 = 64 := by
        calc
          (2 : ZMod 542848051) ^ 6 = (2 : ZMod 542848051) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 3 * (2 : ZMod 542848051) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 542848051) ^ 13 = 8192 := by
        calc
          (2 : ZMod 542848051) ^ 13 = (2 : ZMod 542848051) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 6 * (2 : ZMod 542848051) ^ 6) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 542848051) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 542848051) ^ 27 = (2 : ZMod 542848051) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 13 * (2 : ZMod 542848051) ^ 13) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 542848051) ^ 54 = 51096310 := by
        calc
          (2 : ZMod 542848051) ^ 54 = (2 : ZMod 542848051) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 27 * (2 : ZMod 542848051) ^ 27 := by rw [pow_add]
          _ = 51096310 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 542848051) ^ 108 = 308699141 := by
        calc
          (2 : ZMod 542848051) ^ 108 = (2 : ZMod 542848051) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 54 * (2 : ZMod 542848051) ^ 54 := by rw [pow_add]
          _ = 308699141 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 542848051) ^ 217 = 255636952 := by
        calc
          (2 : ZMod 542848051) ^ 217 = (2 : ZMod 542848051) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 108 * (2 : ZMod 542848051) ^ 108) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 255636952 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 542848051) ^ 435 = 485006743 := by
        calc
          (2 : ZMod 542848051) ^ 435 = (2 : ZMod 542848051) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 217 * (2 : ZMod 542848051) ^ 217) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 485006743 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 542848051) ^ 871 = 261443415 := by
        calc
          (2 : ZMod 542848051) ^ 871 = (2 : ZMod 542848051) ^ (435 + 435 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 435 * (2 : ZMod 542848051) ^ 435) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 261443415 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 542848051) ^ 1743 = 208612446 := by
        calc
          (2 : ZMod 542848051) ^ 1743 = (2 : ZMod 542848051) ^ (871 + 871 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 871 * (2 : ZMod 542848051) ^ 871) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 208612446 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 542848051) ^ 3487 = 293609177 := by
        calc
          (2 : ZMod 542848051) ^ 3487 = (2 : ZMod 542848051) ^ (1743 + 1743 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 1743 * (2 : ZMod 542848051) ^ 1743) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 293609177 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 542848051) ^ 6975 = 52108151 := by
        calc
          (2 : ZMod 542848051) ^ 6975 = (2 : ZMod 542848051) ^ (3487 + 3487 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 3487 * (2 : ZMod 542848051) ^ 3487) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 52108151 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 542848051) ^ 13950 = 219847074 := by
        calc
          (2 : ZMod 542848051) ^ 13950 = (2 : ZMod 542848051) ^ (6975 + 6975) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 6975 * (2 : ZMod 542848051) ^ 6975 := by rw [pow_add]
          _ = 219847074 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 542848051) ^ 27901 = 488416196 := by
        calc
          (2 : ZMod 542848051) ^ 27901 = (2 : ZMod 542848051) ^ (13950 + 13950 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 13950 * (2 : ZMod 542848051) ^ 13950) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 488416196 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 542848051) ^ 55802 = 175746595 := by
        calc
          (2 : ZMod 542848051) ^ 55802 = (2 : ZMod 542848051) ^ (27901 + 27901) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 27901 * (2 : ZMod 542848051) ^ 27901 := by rw [pow_add]
          _ = 175746595 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 542848051) ^ 111605 = 236003379 := by
        calc
          (2 : ZMod 542848051) ^ 111605 = (2 : ZMod 542848051) ^ (55802 + 55802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 55802 * (2 : ZMod 542848051) ^ 55802) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 236003379 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 542848051) ^ 223210 = 61439540 := by
        calc
          (2 : ZMod 542848051) ^ 223210 = (2 : ZMod 542848051) ^ (111605 + 111605) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 111605 * (2 : ZMod 542848051) ^ 111605 := by rw [pow_add]
          _ = 61439540 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 542848051) ^ 446421 = 395399097 := by
        calc
          (2 : ZMod 542848051) ^ 446421 = (2 : ZMod 542848051) ^ (223210 + 223210 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 223210 * (2 : ZMod 542848051) ^ 223210) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 395399097 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 542848051) ^ 892842 = 395307978 := by
        calc
          (2 : ZMod 542848051) ^ 892842 = (2 : ZMod 542848051) ^ (446421 + 446421) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 446421 * (2 : ZMod 542848051) ^ 446421 := by rw [pow_add]
          _ = 395307978 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 542848051) ^ 1785684 = 379213926 := by
        calc
          (2 : ZMod 542848051) ^ 1785684 = (2 : ZMod 542848051) ^ (892842 + 892842) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 892842 * (2 : ZMod 542848051) ^ 892842 := by rw [pow_add]
          _ = 379213926 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 542848051) ^ 3571368 = 179966855 := by
        calc
          (2 : ZMod 542848051) ^ 3571368 = (2 : ZMod 542848051) ^ (1785684 + 1785684) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1785684 * (2 : ZMod 542848051) ^ 1785684 := by rw [pow_add]
          _ = 179966855 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 542848051) ^ 7142737 = 467756488 := by
        calc
          (2 : ZMod 542848051) ^ 7142737 = (2 : ZMod 542848051) ^ (3571368 + 3571368 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 3571368 * (2 : ZMod 542848051) ^ 3571368) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 467756488 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 542848051) ^ 14285475 = 347834125 := by
        calc
          (2 : ZMod 542848051) ^ 14285475 = (2 : ZMod 542848051) ^ (7142737 + 7142737 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 7142737 * (2 : ZMod 542848051) ^ 7142737) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 347834125 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 542848051) ^ 28570950 = 27126695 := by
        calc
          (2 : ZMod 542848051) ^ 28570950 = (2 : ZMod 542848051) ^ (14285475 + 14285475) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 14285475 * (2 : ZMod 542848051) ^ 14285475 := by rw [pow_add]
          _ = 27126695 := by rw [factor_3_23]; decide
      change (2 : ZMod 542848051) ^ 28570950 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (2 : ZMod 542848051) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 542848051) ^ 2 = 4 := by
        calc
          (2 : ZMod 542848051) ^ 2 = (2 : ZMod 542848051) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1 * (2 : ZMod 542848051) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 542848051) ^ 5 = 32 := by
        calc
          (2 : ZMod 542848051) ^ 5 = (2 : ZMod 542848051) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 2 * (2 : ZMod 542848051) ^ 2) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 542848051) ^ 11 = 2048 := by
        calc
          (2 : ZMod 542848051) ^ 11 = (2 : ZMod 542848051) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 5 * (2 : ZMod 542848051) ^ 5) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 542848051) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 542848051) ^ 23 = (2 : ZMod 542848051) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 11 * (2 : ZMod 542848051) ^ 11) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 542848051) ^ 47 = 331197221 := by
        calc
          (2 : ZMod 542848051) ^ 47 = (2 : ZMod 542848051) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 23 * (2 : ZMod 542848051) ^ 23) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 331197221 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 542848051) ^ 95 = 493650370 := by
        calc
          (2 : ZMod 542848051) ^ 95 = (2 : ZMod 542848051) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 47 * (2 : ZMod 542848051) ^ 47) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 493650370 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 542848051) ^ 191 = 22077266 := by
        calc
          (2 : ZMod 542848051) ^ 191 = (2 : ZMod 542848051) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 95 * (2 : ZMod 542848051) ^ 95) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 22077266 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 542848051) ^ 383 = 103207027 := by
        calc
          (2 : ZMod 542848051) ^ 383 = (2 : ZMod 542848051) ^ (191 + 191 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 191 * (2 : ZMod 542848051) ^ 191) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 103207027 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 542848051) ^ 766 = 335639716 := by
        calc
          (2 : ZMod 542848051) ^ 766 = (2 : ZMod 542848051) ^ (383 + 383) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 383 * (2 : ZMod 542848051) ^ 383 := by rw [pow_add]
          _ = 335639716 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 542848051) ^ 1532 = 478306820 := by
        calc
          (2 : ZMod 542848051) ^ 1532 = (2 : ZMod 542848051) ^ (766 + 766) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 766 * (2 : ZMod 542848051) ^ 766 := by rw [pow_add]
          _ = 478306820 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 542848051) ^ 3064 = 465788464 := by
        calc
          (2 : ZMod 542848051) ^ 3064 = (2 : ZMod 542848051) ^ (1532 + 1532) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1532 * (2 : ZMod 542848051) ^ 1532 := by rw [pow_add]
          _ = 465788464 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 542848051) ^ 6128 = 403844884 := by
        calc
          (2 : ZMod 542848051) ^ 6128 = (2 : ZMod 542848051) ^ (3064 + 3064) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 3064 * (2 : ZMod 542848051) ^ 3064 := by rw [pow_add]
          _ = 403844884 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 542848051) ^ 12257 = 294703361 := by
        calc
          (2 : ZMod 542848051) ^ 12257 = (2 : ZMod 542848051) ^ (6128 + 6128 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 6128 * (2 : ZMod 542848051) ^ 6128) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 294703361 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 542848051) ^ 24514 = 216328069 := by
        calc
          (2 : ZMod 542848051) ^ 24514 = (2 : ZMod 542848051) ^ (12257 + 12257) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 12257 * (2 : ZMod 542848051) ^ 12257 := by rw [pow_add]
          _ = 216328069 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 542848051) ^ 49028 = 56469832 := by
        calc
          (2 : ZMod 542848051) ^ 49028 = (2 : ZMod 542848051) ^ (24514 + 24514) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 24514 * (2 : ZMod 542848051) ^ 24514 := by rw [pow_add]
          _ = 56469832 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 542848051) ^ 98057 = 411311837 := by
        calc
          (2 : ZMod 542848051) ^ 98057 = (2 : ZMod 542848051) ^ (49028 + 49028 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 49028 * (2 : ZMod 542848051) ^ 49028) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 411311837 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 542848051) ^ 196115 = 199492591 := by
        calc
          (2 : ZMod 542848051) ^ 196115 = (2 : ZMod 542848051) ^ (98057 + 98057 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 98057 * (2 : ZMod 542848051) ^ 98057) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 199492591 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 542848051) ^ 392231 = 355687298 := by
        calc
          (2 : ZMod 542848051) ^ 392231 = (2 : ZMod 542848051) ^ (196115 + 196115 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 196115 * (2 : ZMod 542848051) ^ 196115) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 355687298 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 542848051) ^ 784462 = 347039702 := by
        calc
          (2 : ZMod 542848051) ^ 784462 = (2 : ZMod 542848051) ^ (392231 + 392231) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 392231 * (2 : ZMod 542848051) ^ 392231 := by rw [pow_add]
          _ = 347039702 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 542848051) ^ 1568925 = 176931854 := by
        calc
          (2 : ZMod 542848051) ^ 1568925 = (2 : ZMod 542848051) ^ (784462 + 784462 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 784462 * (2 : ZMod 542848051) ^ 784462) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 176931854 := by rw [factor_4_19]; decide
      have factor_4_21 : (2 : ZMod 542848051) ^ 3137850 = 439168915 := by
        calc
          (2 : ZMod 542848051) ^ 3137850 = (2 : ZMod 542848051) ^ (1568925 + 1568925) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1568925 * (2 : ZMod 542848051) ^ 1568925 := by rw [pow_add]
          _ = 439168915 := by rw [factor_4_20]; decide
      change (2 : ZMod 542848051) ^ 3137850 ≠ 1
      rw [factor_4_21]
      decide
    ·
      have factor_5_0 : (2 : ZMod 542848051) ^ 1 = 2 := by norm_num
      have factor_5_1 : (2 : ZMod 542848051) ^ 2 = 4 := by
        calc
          (2 : ZMod 542848051) ^ 2 = (2 : ZMod 542848051) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1 * (2 : ZMod 542848051) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_5_0]; decide
      have factor_5_2 : (2 : ZMod 542848051) ^ 5 = 32 := by
        calc
          (2 : ZMod 542848051) ^ 5 = (2 : ZMod 542848051) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 2 * (2 : ZMod 542848051) ^ 2) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_5_1]; decide
      have factor_5_3 : (2 : ZMod 542848051) ^ 11 = 2048 := by
        calc
          (2 : ZMod 542848051) ^ 11 = (2 : ZMod 542848051) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 5 * (2 : ZMod 542848051) ^ 5) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_5_2]; decide
      have factor_5_4 : (2 : ZMod 542848051) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 542848051) ^ 22 = (2 : ZMod 542848051) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 11 * (2 : ZMod 542848051) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_5_3]; decide
      have factor_5_5 : (2 : ZMod 542848051) ^ 45 = 218511318 := by
        calc
          (2 : ZMod 542848051) ^ 45 = (2 : ZMod 542848051) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 22 * (2 : ZMod 542848051) ^ 22) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 218511318 := by rw [factor_5_4]; decide
      have factor_5_6 : (2 : ZMod 542848051) ^ 90 = 185066590 := by
        calc
          (2 : ZMod 542848051) ^ 90 = (2 : ZMod 542848051) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 45 * (2 : ZMod 542848051) ^ 45 := by rw [pow_add]
          _ = 185066590 := by rw [factor_5_5]; decide
      have factor_5_7 : (2 : ZMod 542848051) ^ 180 = 447966447 := by
        calc
          (2 : ZMod 542848051) ^ 180 = (2 : ZMod 542848051) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 90 * (2 : ZMod 542848051) ^ 90 := by rw [pow_add]
          _ = 447966447 := by rw [factor_5_6]; decide
      have factor_5_8 : (2 : ZMod 542848051) ^ 361 = 511479453 := by
        calc
          (2 : ZMod 542848051) ^ 361 = (2 : ZMod 542848051) ^ (180 + 180 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 180 * (2 : ZMod 542848051) ^ 180) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 511479453 := by rw [factor_5_7]; decide
      have factor_5_9 : (2 : ZMod 542848051) ^ 722 = 306472913 := by
        calc
          (2 : ZMod 542848051) ^ 722 = (2 : ZMod 542848051) ^ (361 + 361) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 361 * (2 : ZMod 542848051) ^ 361 := by rw [pow_add]
          _ = 306472913 := by rw [factor_5_8]; decide
      have factor_5_10 : (2 : ZMod 542848051) ^ 1444 = 224890494 := by
        calc
          (2 : ZMod 542848051) ^ 1444 = (2 : ZMod 542848051) ^ (722 + 722) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 722 * (2 : ZMod 542848051) ^ 722 := by rw [pow_add]
          _ = 224890494 := by rw [factor_5_9]; decide
      have factor_5_11 : (2 : ZMod 542848051) ^ 2888 = 384699350 := by
        calc
          (2 : ZMod 542848051) ^ 2888 = (2 : ZMod 542848051) ^ (1444 + 1444) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 1444 * (2 : ZMod 542848051) ^ 1444 := by rw [pow_add]
          _ = 384699350 := by rw [factor_5_10]; decide
      have factor_5_12 : (2 : ZMod 542848051) ^ 5777 = 332458677 := by
        calc
          (2 : ZMod 542848051) ^ 5777 = (2 : ZMod 542848051) ^ (2888 + 2888 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 2888 * (2 : ZMod 542848051) ^ 2888) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 332458677 := by rw [factor_5_11]; decide
      have factor_5_13 : (2 : ZMod 542848051) ^ 11555 = 50978323 := by
        calc
          (2 : ZMod 542848051) ^ 11555 = (2 : ZMod 542848051) ^ (5777 + 5777 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 5777 * (2 : ZMod 542848051) ^ 5777) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 50978323 := by rw [factor_5_12]; decide
      have factor_5_14 : (2 : ZMod 542848051) ^ 23111 = 368821661 := by
        calc
          (2 : ZMod 542848051) ^ 23111 = (2 : ZMod 542848051) ^ (11555 + 11555 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 11555 * (2 : ZMod 542848051) ^ 11555) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 368821661 := by rw [factor_5_13]; decide
      have factor_5_15 : (2 : ZMod 542848051) ^ 46223 = 520518187 := by
        calc
          (2 : ZMod 542848051) ^ 46223 = (2 : ZMod 542848051) ^ (23111 + 23111 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 23111 * (2 : ZMod 542848051) ^ 23111) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 520518187 := by rw [factor_5_14]; decide
      have factor_5_16 : (2 : ZMod 542848051) ^ 92446 = 63125415 := by
        calc
          (2 : ZMod 542848051) ^ 92446 = (2 : ZMod 542848051) ^ (46223 + 46223) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 46223 * (2 : ZMod 542848051) ^ 46223 := by rw [pow_add]
          _ = 63125415 := by rw [factor_5_15]; decide
      have factor_5_17 : (2 : ZMod 542848051) ^ 184893 = 202513596 := by
        calc
          (2 : ZMod 542848051) ^ 184893 = (2 : ZMod 542848051) ^ (92446 + 92446 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 92446 * (2 : ZMod 542848051) ^ 92446) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 202513596 := by rw [factor_5_16]; decide
      have factor_5_18 : (2 : ZMod 542848051) ^ 369787 = 466880207 := by
        calc
          (2 : ZMod 542848051) ^ 369787 = (2 : ZMod 542848051) ^ (184893 + 184893 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 184893 * (2 : ZMod 542848051) ^ 184893) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 466880207 := by rw [factor_5_17]; decide
      have factor_5_19 : (2 : ZMod 542848051) ^ 739575 = 301140720 := by
        calc
          (2 : ZMod 542848051) ^ 739575 = (2 : ZMod 542848051) ^ (369787 + 369787 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = ((2 : ZMod 542848051) ^ 369787 * (2 : ZMod 542848051) ^ 369787) * (2 : ZMod 542848051) := by rw [pow_succ, pow_add]
          _ = 301140720 := by rw [factor_5_18]; decide
      have factor_5_20 : (2 : ZMod 542848051) ^ 1479150 = 200817736 := by
        calc
          (2 : ZMod 542848051) ^ 1479150 = (2 : ZMod 542848051) ^ (739575 + 739575) :=
            congrArg (fun n : ℕ => (2 : ZMod 542848051) ^ n) (by norm_num)
          _ = (2 : ZMod 542848051) ^ 739575 * (2 : ZMod 542848051) ^ 739575 := by rw [pow_add]
          _ = 200817736 := by rw [factor_5_19]; decide
      change (2 : ZMod 542848051) ^ 1479150 ≠ 1
      rw [factor_5_20]
      decide

#print axioms prime_lucas_542848051

end TotientTailPeriodKiller
end Erdos249257
