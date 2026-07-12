import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_36975198103 : Nat.Prime 36975198103 := by
  apply lucas_primality 36975198103 (3 : ZMod 36975198103)
  ·
      have fermat_0 : (3 : ZMod 36975198103) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 36975198103) ^ 2 = 9 := by
        calc
          (3 : ZMod 36975198103) ^ 2 = (3 : ZMod 36975198103) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1 * (3 : ZMod 36975198103) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 36975198103) ^ 4 = 81 := by
        calc
          (3 : ZMod 36975198103) ^ 4 = (3 : ZMod 36975198103) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 2 * (3 : ZMod 36975198103) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 36975198103) ^ 8 = 6561 := by
        calc
          (3 : ZMod 36975198103) ^ 8 = (3 : ZMod 36975198103) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 4 * (3 : ZMod 36975198103) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 36975198103) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 36975198103) ^ 17 = (3 : ZMod 36975198103) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 8 * (3 : ZMod 36975198103) ^ 8) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 36975198103) ^ 34 = 36248081861 := by
        calc
          (3 : ZMod 36975198103) ^ 34 = (3 : ZMod 36975198103) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 17 * (3 : ZMod 36975198103) ^ 17 := by rw [pow_add]
          _ = 36248081861 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 36975198103) ^ 68 = 24760874404 := by
        calc
          (3 : ZMod 36975198103) ^ 68 = (3 : ZMod 36975198103) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 34 * (3 : ZMod 36975198103) ^ 34 := by rw [pow_add]
          _ = 24760874404 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 36975198103) ^ 137 = 2910954809 := by
        calc
          (3 : ZMod 36975198103) ^ 137 = (3 : ZMod 36975198103) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 68 * (3 : ZMod 36975198103) ^ 68) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 2910954809 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 36975198103) ^ 275 = 30445513049 := by
        calc
          (3 : ZMod 36975198103) ^ 275 = (3 : ZMod 36975198103) ^ (137 + 137 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 137 * (3 : ZMod 36975198103) ^ 137) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 30445513049 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 36975198103) ^ 550 = 7986476060 := by
        calc
          (3 : ZMod 36975198103) ^ 550 = (3 : ZMod 36975198103) ^ (275 + 275) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 275 * (3 : ZMod 36975198103) ^ 275 := by rw [pow_add]
          _ = 7986476060 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 36975198103) ^ 1101 = 34563634759 := by
        calc
          (3 : ZMod 36975198103) ^ 1101 = (3 : ZMod 36975198103) ^ (550 + 550 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 550 * (3 : ZMod 36975198103) ^ 550) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 34563634759 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 36975198103) ^ 2203 = 5858156435 := by
        calc
          (3 : ZMod 36975198103) ^ 2203 = (3 : ZMod 36975198103) ^ (1101 + 1101 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1101 * (3 : ZMod 36975198103) ^ 1101) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 5858156435 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 36975198103) ^ 4407 = 9719294485 := by
        calc
          (3 : ZMod 36975198103) ^ 4407 = (3 : ZMod 36975198103) ^ (2203 + 2203 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2203 * (3 : ZMod 36975198103) ^ 2203) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 9719294485 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 36975198103) ^ 8815 = 30676578046 := by
        calc
          (3 : ZMod 36975198103) ^ 8815 = (3 : ZMod 36975198103) ^ (4407 + 4407 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 4407 * (3 : ZMod 36975198103) ^ 4407) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 30676578046 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 36975198103) ^ 17631 = 19042968194 := by
        calc
          (3 : ZMod 36975198103) ^ 17631 = (3 : ZMod 36975198103) ^ (8815 + 8815 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 8815 * (3 : ZMod 36975198103) ^ 8815) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 19042968194 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 36975198103) ^ 35262 = 29900330925 := by
        calc
          (3 : ZMod 36975198103) ^ 35262 = (3 : ZMod 36975198103) ^ (17631 + 17631) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 17631 * (3 : ZMod 36975198103) ^ 17631 := by rw [pow_add]
          _ = 29900330925 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 36975198103) ^ 70524 = 23960926016 := by
        calc
          (3 : ZMod 36975198103) ^ 70524 = (3 : ZMod 36975198103) ^ (35262 + 35262) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 35262 * (3 : ZMod 36975198103) ^ 35262 := by rw [pow_add]
          _ = 23960926016 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 36975198103) ^ 141049 = 8706745934 := by
        calc
          (3 : ZMod 36975198103) ^ 141049 = (3 : ZMod 36975198103) ^ (70524 + 70524 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 70524 * (3 : ZMod 36975198103) ^ 70524) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 8706745934 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 36975198103) ^ 282098 = 32424550878 := by
        calc
          (3 : ZMod 36975198103) ^ 282098 = (3 : ZMod 36975198103) ^ (141049 + 141049) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 141049 * (3 : ZMod 36975198103) ^ 141049 := by rw [pow_add]
          _ = 32424550878 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 36975198103) ^ 564196 = 3558735499 := by
        calc
          (3 : ZMod 36975198103) ^ 564196 = (3 : ZMod 36975198103) ^ (282098 + 282098) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 282098 * (3 : ZMod 36975198103) ^ 282098 := by rw [pow_add]
          _ = 3558735499 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 36975198103) ^ 1128393 = 16989507364 := by
        calc
          (3 : ZMod 36975198103) ^ 1128393 = (3 : ZMod 36975198103) ^ (564196 + 564196 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 564196 * (3 : ZMod 36975198103) ^ 564196) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 16989507364 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 36975198103) ^ 2256786 = 31843953881 := by
        calc
          (3 : ZMod 36975198103) ^ 2256786 = (3 : ZMod 36975198103) ^ (1128393 + 1128393) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1128393 * (3 : ZMod 36975198103) ^ 1128393 := by rw [pow_add]
          _ = 31843953881 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 36975198103) ^ 4513573 = 4804306830 := by
        calc
          (3 : ZMod 36975198103) ^ 4513573 = (3 : ZMod 36975198103) ^ (2256786 + 2256786 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2256786 * (3 : ZMod 36975198103) ^ 2256786) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 4804306830 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 36975198103) ^ 9027147 = 5393023066 := by
        calc
          (3 : ZMod 36975198103) ^ 9027147 = (3 : ZMod 36975198103) ^ (4513573 + 4513573 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 4513573 * (3 : ZMod 36975198103) ^ 4513573) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 5393023066 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 36975198103) ^ 18054295 = 33752990976 := by
        calc
          (3 : ZMod 36975198103) ^ 18054295 = (3 : ZMod 36975198103) ^ (9027147 + 9027147 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 9027147 * (3 : ZMod 36975198103) ^ 9027147) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 33752990976 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 36975198103) ^ 36108591 = 7972587291 := by
        calc
          (3 : ZMod 36975198103) ^ 36108591 = (3 : ZMod 36975198103) ^ (18054295 + 18054295 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 18054295 * (3 : ZMod 36975198103) ^ 18054295) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 7972587291 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 36975198103) ^ 72217183 = 34746717256 := by
        calc
          (3 : ZMod 36975198103) ^ 72217183 = (3 : ZMod 36975198103) ^ (36108591 + 36108591 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 36108591 * (3 : ZMod 36975198103) ^ 36108591) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 34746717256 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 36975198103) ^ 144434367 = 24588278343 := by
        calc
          (3 : ZMod 36975198103) ^ 144434367 = (3 : ZMod 36975198103) ^ (72217183 + 72217183 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 72217183 * (3 : ZMod 36975198103) ^ 72217183) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 24588278343 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 36975198103) ^ 288868735 = 18667531100 := by
        calc
          (3 : ZMod 36975198103) ^ 288868735 = (3 : ZMod 36975198103) ^ (144434367 + 144434367 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 144434367 * (3 : ZMod 36975198103) ^ 144434367) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 18667531100 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 36975198103) ^ 577737470 = 30887020975 := by
        calc
          (3 : ZMod 36975198103) ^ 577737470 = (3 : ZMod 36975198103) ^ (288868735 + 288868735) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 288868735 * (3 : ZMod 36975198103) ^ 288868735 := by rw [pow_add]
          _ = 30887020975 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 36975198103) ^ 1155474940 = 617396483 := by
        calc
          (3 : ZMod 36975198103) ^ 1155474940 = (3 : ZMod 36975198103) ^ (577737470 + 577737470) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 577737470 * (3 : ZMod 36975198103) ^ 577737470 := by rw [pow_add]
          _ = 617396483 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 36975198103) ^ 2310949881 = 9138195700 := by
        calc
          (3 : ZMod 36975198103) ^ 2310949881 = (3 : ZMod 36975198103) ^ (1155474940 + 1155474940 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1155474940 * (3 : ZMod 36975198103) ^ 1155474940) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 9138195700 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 36975198103) ^ 4621899762 = 25361343260 := by
        calc
          (3 : ZMod 36975198103) ^ 4621899762 = (3 : ZMod 36975198103) ^ (2310949881 + 2310949881) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 2310949881 * (3 : ZMod 36975198103) ^ 2310949881 := by rw [pow_add]
          _ = 25361343260 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 36975198103) ^ 9243799525 = 10850850435 := by
        calc
          (3 : ZMod 36975198103) ^ 9243799525 = (3 : ZMod 36975198103) ^ (4621899762 + 4621899762 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 4621899762 * (3 : ZMod 36975198103) ^ 4621899762) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 10850850435 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 36975198103) ^ 18487599051 = 36975198102 := by
        calc
          (3 : ZMod 36975198103) ^ 18487599051 = (3 : ZMod 36975198103) ^ (9243799525 + 9243799525 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 9243799525 * (3 : ZMod 36975198103) ^ 9243799525) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 36975198102 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 36975198103) ^ 36975198102 = 1 := by
        calc
          (3 : ZMod 36975198103) ^ 36975198102 = (3 : ZMod 36975198103) ^ (18487599051 + 18487599051) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 18487599051 * (3 : ZMod 36975198103) ^ 18487599051 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (773, 1), (419591, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (773, 1), (419591, 1)] : List FactorBlock).map factorBlockValue).prod = 36975198103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 36975198103) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 36975198103) ^ 2 = 9 := by
        calc
          (3 : ZMod 36975198103) ^ 2 = (3 : ZMod 36975198103) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1 * (3 : ZMod 36975198103) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 36975198103) ^ 4 = 81 := by
        calc
          (3 : ZMod 36975198103) ^ 4 = (3 : ZMod 36975198103) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 2 * (3 : ZMod 36975198103) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 36975198103) ^ 8 = 6561 := by
        calc
          (3 : ZMod 36975198103) ^ 8 = (3 : ZMod 36975198103) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 4 * (3 : ZMod 36975198103) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 36975198103) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 36975198103) ^ 17 = (3 : ZMod 36975198103) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 8 * (3 : ZMod 36975198103) ^ 8) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 36975198103) ^ 34 = 36248081861 := by
        calc
          (3 : ZMod 36975198103) ^ 34 = (3 : ZMod 36975198103) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 17 * (3 : ZMod 36975198103) ^ 17 := by rw [pow_add]
          _ = 36248081861 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 36975198103) ^ 68 = 24760874404 := by
        calc
          (3 : ZMod 36975198103) ^ 68 = (3 : ZMod 36975198103) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 34 * (3 : ZMod 36975198103) ^ 34 := by rw [pow_add]
          _ = 24760874404 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 36975198103) ^ 137 = 2910954809 := by
        calc
          (3 : ZMod 36975198103) ^ 137 = (3 : ZMod 36975198103) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 68 * (3 : ZMod 36975198103) ^ 68) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 2910954809 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 36975198103) ^ 275 = 30445513049 := by
        calc
          (3 : ZMod 36975198103) ^ 275 = (3 : ZMod 36975198103) ^ (137 + 137 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 137 * (3 : ZMod 36975198103) ^ 137) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 30445513049 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 36975198103) ^ 550 = 7986476060 := by
        calc
          (3 : ZMod 36975198103) ^ 550 = (3 : ZMod 36975198103) ^ (275 + 275) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 275 * (3 : ZMod 36975198103) ^ 275 := by rw [pow_add]
          _ = 7986476060 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 36975198103) ^ 1101 = 34563634759 := by
        calc
          (3 : ZMod 36975198103) ^ 1101 = (3 : ZMod 36975198103) ^ (550 + 550 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 550 * (3 : ZMod 36975198103) ^ 550) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 34563634759 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 36975198103) ^ 2203 = 5858156435 := by
        calc
          (3 : ZMod 36975198103) ^ 2203 = (3 : ZMod 36975198103) ^ (1101 + 1101 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1101 * (3 : ZMod 36975198103) ^ 1101) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 5858156435 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 36975198103) ^ 4407 = 9719294485 := by
        calc
          (3 : ZMod 36975198103) ^ 4407 = (3 : ZMod 36975198103) ^ (2203 + 2203 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2203 * (3 : ZMod 36975198103) ^ 2203) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 9719294485 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 36975198103) ^ 8815 = 30676578046 := by
        calc
          (3 : ZMod 36975198103) ^ 8815 = (3 : ZMod 36975198103) ^ (4407 + 4407 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 4407 * (3 : ZMod 36975198103) ^ 4407) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 30676578046 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 36975198103) ^ 17631 = 19042968194 := by
        calc
          (3 : ZMod 36975198103) ^ 17631 = (3 : ZMod 36975198103) ^ (8815 + 8815 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 8815 * (3 : ZMod 36975198103) ^ 8815) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 19042968194 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 36975198103) ^ 35262 = 29900330925 := by
        calc
          (3 : ZMod 36975198103) ^ 35262 = (3 : ZMod 36975198103) ^ (17631 + 17631) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 17631 * (3 : ZMod 36975198103) ^ 17631 := by rw [pow_add]
          _ = 29900330925 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 36975198103) ^ 70524 = 23960926016 := by
        calc
          (3 : ZMod 36975198103) ^ 70524 = (3 : ZMod 36975198103) ^ (35262 + 35262) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 35262 * (3 : ZMod 36975198103) ^ 35262 := by rw [pow_add]
          _ = 23960926016 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 36975198103) ^ 141049 = 8706745934 := by
        calc
          (3 : ZMod 36975198103) ^ 141049 = (3 : ZMod 36975198103) ^ (70524 + 70524 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 70524 * (3 : ZMod 36975198103) ^ 70524) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 8706745934 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 36975198103) ^ 282098 = 32424550878 := by
        calc
          (3 : ZMod 36975198103) ^ 282098 = (3 : ZMod 36975198103) ^ (141049 + 141049) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 141049 * (3 : ZMod 36975198103) ^ 141049 := by rw [pow_add]
          _ = 32424550878 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 36975198103) ^ 564196 = 3558735499 := by
        calc
          (3 : ZMod 36975198103) ^ 564196 = (3 : ZMod 36975198103) ^ (282098 + 282098) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 282098 * (3 : ZMod 36975198103) ^ 282098 := by rw [pow_add]
          _ = 3558735499 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 36975198103) ^ 1128393 = 16989507364 := by
        calc
          (3 : ZMod 36975198103) ^ 1128393 = (3 : ZMod 36975198103) ^ (564196 + 564196 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 564196 * (3 : ZMod 36975198103) ^ 564196) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 16989507364 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 36975198103) ^ 2256786 = 31843953881 := by
        calc
          (3 : ZMod 36975198103) ^ 2256786 = (3 : ZMod 36975198103) ^ (1128393 + 1128393) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1128393 * (3 : ZMod 36975198103) ^ 1128393 := by rw [pow_add]
          _ = 31843953881 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 36975198103) ^ 4513573 = 4804306830 := by
        calc
          (3 : ZMod 36975198103) ^ 4513573 = (3 : ZMod 36975198103) ^ (2256786 + 2256786 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2256786 * (3 : ZMod 36975198103) ^ 2256786) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 4804306830 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 36975198103) ^ 9027147 = 5393023066 := by
        calc
          (3 : ZMod 36975198103) ^ 9027147 = (3 : ZMod 36975198103) ^ (4513573 + 4513573 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 4513573 * (3 : ZMod 36975198103) ^ 4513573) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 5393023066 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 36975198103) ^ 18054295 = 33752990976 := by
        calc
          (3 : ZMod 36975198103) ^ 18054295 = (3 : ZMod 36975198103) ^ (9027147 + 9027147 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 9027147 * (3 : ZMod 36975198103) ^ 9027147) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 33752990976 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 36975198103) ^ 36108591 = 7972587291 := by
        calc
          (3 : ZMod 36975198103) ^ 36108591 = (3 : ZMod 36975198103) ^ (18054295 + 18054295 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 18054295 * (3 : ZMod 36975198103) ^ 18054295) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 7972587291 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 36975198103) ^ 72217183 = 34746717256 := by
        calc
          (3 : ZMod 36975198103) ^ 72217183 = (3 : ZMod 36975198103) ^ (36108591 + 36108591 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 36108591 * (3 : ZMod 36975198103) ^ 36108591) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 34746717256 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 36975198103) ^ 144434367 = 24588278343 := by
        calc
          (3 : ZMod 36975198103) ^ 144434367 = (3 : ZMod 36975198103) ^ (72217183 + 72217183 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 72217183 * (3 : ZMod 36975198103) ^ 72217183) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 24588278343 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 36975198103) ^ 288868735 = 18667531100 := by
        calc
          (3 : ZMod 36975198103) ^ 288868735 = (3 : ZMod 36975198103) ^ (144434367 + 144434367 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 144434367 * (3 : ZMod 36975198103) ^ 144434367) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 18667531100 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 36975198103) ^ 577737470 = 30887020975 := by
        calc
          (3 : ZMod 36975198103) ^ 577737470 = (3 : ZMod 36975198103) ^ (288868735 + 288868735) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 288868735 * (3 : ZMod 36975198103) ^ 288868735 := by rw [pow_add]
          _ = 30887020975 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 36975198103) ^ 1155474940 = 617396483 := by
        calc
          (3 : ZMod 36975198103) ^ 1155474940 = (3 : ZMod 36975198103) ^ (577737470 + 577737470) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 577737470 * (3 : ZMod 36975198103) ^ 577737470 := by rw [pow_add]
          _ = 617396483 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 36975198103) ^ 2310949881 = 9138195700 := by
        calc
          (3 : ZMod 36975198103) ^ 2310949881 = (3 : ZMod 36975198103) ^ (1155474940 + 1155474940 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1155474940 * (3 : ZMod 36975198103) ^ 1155474940) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 9138195700 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 36975198103) ^ 4621899762 = 25361343260 := by
        calc
          (3 : ZMod 36975198103) ^ 4621899762 = (3 : ZMod 36975198103) ^ (2310949881 + 2310949881) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 2310949881 * (3 : ZMod 36975198103) ^ 2310949881 := by rw [pow_add]
          _ = 25361343260 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 36975198103) ^ 9243799525 = 10850850435 := by
        calc
          (3 : ZMod 36975198103) ^ 9243799525 = (3 : ZMod 36975198103) ^ (4621899762 + 4621899762 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 4621899762 * (3 : ZMod 36975198103) ^ 4621899762) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 10850850435 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 36975198103) ^ 18487599051 = 36975198102 := by
        calc
          (3 : ZMod 36975198103) ^ 18487599051 = (3 : ZMod 36975198103) ^ (9243799525 + 9243799525 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 9243799525 * (3 : ZMod 36975198103) ^ 9243799525) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 36975198102 := by rw [factor_0_33]; decide
      change (3 : ZMod 36975198103) ^ 18487599051 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (3 : ZMod 36975198103) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 36975198103) ^ 2 = 9 := by
        calc
          (3 : ZMod 36975198103) ^ 2 = (3 : ZMod 36975198103) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1 * (3 : ZMod 36975198103) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 36975198103) ^ 5 = 243 := by
        calc
          (3 : ZMod 36975198103) ^ 5 = (3 : ZMod 36975198103) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2 * (3 : ZMod 36975198103) ^ 2) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 36975198103) ^ 11 = 177147 := by
        calc
          (3 : ZMod 36975198103) ^ 11 = (3 : ZMod 36975198103) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 5 * (3 : ZMod 36975198103) ^ 5) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 36975198103) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 36975198103) ^ 22 = (3 : ZMod 36975198103) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 11 * (3 : ZMod 36975198103) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 36975198103) ^ 45 = 15129269278 := by
        calc
          (3 : ZMod 36975198103) ^ 45 = (3 : ZMod 36975198103) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 22 * (3 : ZMod 36975198103) ^ 22) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 15129269278 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 36975198103) ^ 91 = 25726892143 := by
        calc
          (3 : ZMod 36975198103) ^ 91 = (3 : ZMod 36975198103) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 45 * (3 : ZMod 36975198103) ^ 45) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 25726892143 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 36975198103) ^ 183 = 26643666677 := by
        calc
          (3 : ZMod 36975198103) ^ 183 = (3 : ZMod 36975198103) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 91 * (3 : ZMod 36975198103) ^ 91) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 26643666677 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 36975198103) ^ 367 = 24130650058 := by
        calc
          (3 : ZMod 36975198103) ^ 367 = (3 : ZMod 36975198103) ^ (183 + 183 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 183 * (3 : ZMod 36975198103) ^ 183) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 24130650058 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 36975198103) ^ 734 = 6978549326 := by
        calc
          (3 : ZMod 36975198103) ^ 734 = (3 : ZMod 36975198103) ^ (367 + 367) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 367 * (3 : ZMod 36975198103) ^ 367 := by rw [pow_add]
          _ = 6978549326 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 36975198103) ^ 1469 = 2851312783 := by
        calc
          (3 : ZMod 36975198103) ^ 1469 = (3 : ZMod 36975198103) ^ (734 + 734 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 734 * (3 : ZMod 36975198103) ^ 734) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 2851312783 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 36975198103) ^ 2938 = 8790106886 := by
        calc
          (3 : ZMod 36975198103) ^ 2938 = (3 : ZMod 36975198103) ^ (1469 + 1469) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1469 * (3 : ZMod 36975198103) ^ 1469 := by rw [pow_add]
          _ = 8790106886 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 36975198103) ^ 5877 = 34105212290 := by
        calc
          (3 : ZMod 36975198103) ^ 5877 = (3 : ZMod 36975198103) ^ (2938 + 2938 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2938 * (3 : ZMod 36975198103) ^ 2938) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 34105212290 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 36975198103) ^ 11754 = 33250052643 := by
        calc
          (3 : ZMod 36975198103) ^ 11754 = (3 : ZMod 36975198103) ^ (5877 + 5877) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 5877 * (3 : ZMod 36975198103) ^ 5877 := by rw [pow_add]
          _ = 33250052643 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 36975198103) ^ 23508 = 7323245247 := by
        calc
          (3 : ZMod 36975198103) ^ 23508 = (3 : ZMod 36975198103) ^ (11754 + 11754) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 11754 * (3 : ZMod 36975198103) ^ 11754 := by rw [pow_add]
          _ = 7323245247 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 36975198103) ^ 47016 = 3682598578 := by
        calc
          (3 : ZMod 36975198103) ^ 47016 = (3 : ZMod 36975198103) ^ (23508 + 23508) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 23508 * (3 : ZMod 36975198103) ^ 23508 := by rw [pow_add]
          _ = 3682598578 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 36975198103) ^ 94032 = 36581435319 := by
        calc
          (3 : ZMod 36975198103) ^ 94032 = (3 : ZMod 36975198103) ^ (47016 + 47016) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 47016 * (3 : ZMod 36975198103) ^ 47016 := by rw [pow_add]
          _ = 36581435319 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 36975198103) ^ 188065 = 26632919719 := by
        calc
          (3 : ZMod 36975198103) ^ 188065 = (3 : ZMod 36975198103) ^ (94032 + 94032 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 94032 * (3 : ZMod 36975198103) ^ 94032) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 26632919719 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 36975198103) ^ 376131 = 30266719426 := by
        calc
          (3 : ZMod 36975198103) ^ 376131 = (3 : ZMod 36975198103) ^ (188065 + 188065 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 188065 * (3 : ZMod 36975198103) ^ 188065) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 30266719426 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 36975198103) ^ 752262 = 28095326096 := by
        calc
          (3 : ZMod 36975198103) ^ 752262 = (3 : ZMod 36975198103) ^ (376131 + 376131) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 376131 * (3 : ZMod 36975198103) ^ 376131 := by rw [pow_add]
          _ = 28095326096 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 36975198103) ^ 1504524 = 4319836839 := by
        calc
          (3 : ZMod 36975198103) ^ 1504524 = (3 : ZMod 36975198103) ^ (752262 + 752262) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 752262 * (3 : ZMod 36975198103) ^ 752262 := by rw [pow_add]
          _ = 4319836839 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 36975198103) ^ 3009049 = 12820675120 := by
        calc
          (3 : ZMod 36975198103) ^ 3009049 = (3 : ZMod 36975198103) ^ (1504524 + 1504524 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1504524 * (3 : ZMod 36975198103) ^ 1504524) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 12820675120 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 36975198103) ^ 6018098 = 13102473123 := by
        calc
          (3 : ZMod 36975198103) ^ 6018098 = (3 : ZMod 36975198103) ^ (3009049 + 3009049) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 3009049 * (3 : ZMod 36975198103) ^ 3009049 := by rw [pow_add]
          _ = 13102473123 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 36975198103) ^ 12036197 = 22562208526 := by
        calc
          (3 : ZMod 36975198103) ^ 12036197 = (3 : ZMod 36975198103) ^ (6018098 + 6018098 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 6018098 * (3 : ZMod 36975198103) ^ 6018098) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 22562208526 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 36975198103) ^ 24072394 = 27658040447 := by
        calc
          (3 : ZMod 36975198103) ^ 24072394 = (3 : ZMod 36975198103) ^ (12036197 + 12036197) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 12036197 * (3 : ZMod 36975198103) ^ 12036197 := by rw [pow_add]
          _ = 27658040447 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 36975198103) ^ 48144789 = 12345252319 := by
        calc
          (3 : ZMod 36975198103) ^ 48144789 = (3 : ZMod 36975198103) ^ (24072394 + 24072394 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 24072394 * (3 : ZMod 36975198103) ^ 24072394) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 12345252319 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 36975198103) ^ 96289578 = 15297193297 := by
        calc
          (3 : ZMod 36975198103) ^ 96289578 = (3 : ZMod 36975198103) ^ (48144789 + 48144789) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 48144789 * (3 : ZMod 36975198103) ^ 48144789 := by rw [pow_add]
          _ = 15297193297 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 36975198103) ^ 192579156 = 22659094312 := by
        calc
          (3 : ZMod 36975198103) ^ 192579156 = (3 : ZMod 36975198103) ^ (96289578 + 96289578) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 96289578 * (3 : ZMod 36975198103) ^ 96289578 := by rw [pow_add]
          _ = 22659094312 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 36975198103) ^ 385158313 = 4414265804 := by
        calc
          (3 : ZMod 36975198103) ^ 385158313 = (3 : ZMod 36975198103) ^ (192579156 + 192579156 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 192579156 * (3 : ZMod 36975198103) ^ 192579156) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 4414265804 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 36975198103) ^ 770316627 = 34301144522 := by
        calc
          (3 : ZMod 36975198103) ^ 770316627 = (3 : ZMod 36975198103) ^ (385158313 + 385158313 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 385158313 * (3 : ZMod 36975198103) ^ 385158313) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 34301144522 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 36975198103) ^ 1540633254 = 22275309424 := by
        calc
          (3 : ZMod 36975198103) ^ 1540633254 = (3 : ZMod 36975198103) ^ (770316627 + 770316627) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 770316627 * (3 : ZMod 36975198103) ^ 770316627 := by rw [pow_add]
          _ = 22275309424 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 36975198103) ^ 3081266508 = 5425425218 := by
        calc
          (3 : ZMod 36975198103) ^ 3081266508 = (3 : ZMod 36975198103) ^ (1540633254 + 1540633254) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1540633254 * (3 : ZMod 36975198103) ^ 1540633254 := by rw [pow_add]
          _ = 5425425218 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 36975198103) ^ 6162533017 = 16276275653 := by
        calc
          (3 : ZMod 36975198103) ^ 6162533017 = (3 : ZMod 36975198103) ^ (3081266508 + 3081266508 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 3081266508 * (3 : ZMod 36975198103) ^ 3081266508) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 16276275653 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 36975198103) ^ 12325066034 = 16276275652 := by
        calc
          (3 : ZMod 36975198103) ^ 12325066034 = (3 : ZMod 36975198103) ^ (6162533017 + 6162533017) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 6162533017 * (3 : ZMod 36975198103) ^ 6162533017 := by rw [pow_add]
          _ = 16276275652 := by rw [factor_1_32]; decide
      change (3 : ZMod 36975198103) ^ 12325066034 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (3 : ZMod 36975198103) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 36975198103) ^ 3 = 27 := by
        calc
          (3 : ZMod 36975198103) ^ 3 = (3 : ZMod 36975198103) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1 * (3 : ZMod 36975198103) ^ 1) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 36975198103) ^ 7 = 2187 := by
        calc
          (3 : ZMod 36975198103) ^ 7 = (3 : ZMod 36975198103) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 3 * (3 : ZMod 36975198103) ^ 3) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 36975198103) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 36975198103) ^ 14 = (3 : ZMod 36975198103) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 7 * (3 : ZMod 36975198103) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 36975198103) ^ 28 = 26120027307 := by
        calc
          (3 : ZMod 36975198103) ^ 28 = (3 : ZMod 36975198103) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 14 * (3 : ZMod 36975198103) ^ 14 := by rw [pow_add]
          _ = 26120027307 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 36975198103) ^ 57 = 20191674145 := by
        calc
          (3 : ZMod 36975198103) ^ 57 = (3 : ZMod 36975198103) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 28 * (3 : ZMod 36975198103) ^ 28) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 20191674145 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 36975198103) ^ 115 = 5337393980 := by
        calc
          (3 : ZMod 36975198103) ^ 115 = (3 : ZMod 36975198103) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 57 * (3 : ZMod 36975198103) ^ 57) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 5337393980 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 36975198103) ^ 231 = 8954751058 := by
        calc
          (3 : ZMod 36975198103) ^ 231 = (3 : ZMod 36975198103) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 115 * (3 : ZMod 36975198103) ^ 115) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 8954751058 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 36975198103) ^ 463 = 9372879799 := by
        calc
          (3 : ZMod 36975198103) ^ 463 = (3 : ZMod 36975198103) ^ (231 + 231 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 231 * (3 : ZMod 36975198103) ^ 231) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 9372879799 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 36975198103) ^ 927 = 14353004473 := by
        calc
          (3 : ZMod 36975198103) ^ 927 = (3 : ZMod 36975198103) ^ (463 + 463 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 463 * (3 : ZMod 36975198103) ^ 463) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 14353004473 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 36975198103) ^ 1855 = 14112860566 := by
        calc
          (3 : ZMod 36975198103) ^ 1855 = (3 : ZMod 36975198103) ^ (927 + 927 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 927 * (3 : ZMod 36975198103) ^ 927) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 14112860566 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 36975198103) ^ 3711 = 30175940669 := by
        calc
          (3 : ZMod 36975198103) ^ 3711 = (3 : ZMod 36975198103) ^ (1855 + 1855 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1855 * (3 : ZMod 36975198103) ^ 1855) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 30175940669 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 36975198103) ^ 7423 = 6475474659 := by
        calc
          (3 : ZMod 36975198103) ^ 7423 = (3 : ZMod 36975198103) ^ (3711 + 3711 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 3711 * (3 : ZMod 36975198103) ^ 3711) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 6475474659 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 36975198103) ^ 14847 = 10825136302 := by
        calc
          (3 : ZMod 36975198103) ^ 14847 = (3 : ZMod 36975198103) ^ (7423 + 7423 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 7423 * (3 : ZMod 36975198103) ^ 7423) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 10825136302 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 36975198103) ^ 29694 = 28549060037 := by
        calc
          (3 : ZMod 36975198103) ^ 29694 = (3 : ZMod 36975198103) ^ (14847 + 14847) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 14847 * (3 : ZMod 36975198103) ^ 14847 := by rw [pow_add]
          _ = 28549060037 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 36975198103) ^ 59389 = 29677062923 := by
        calc
          (3 : ZMod 36975198103) ^ 59389 = (3 : ZMod 36975198103) ^ (29694 + 29694 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 29694 * (3 : ZMod 36975198103) ^ 29694) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 29677062923 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 36975198103) ^ 118778 = 23009548658 := by
        calc
          (3 : ZMod 36975198103) ^ 118778 = (3 : ZMod 36975198103) ^ (59389 + 59389) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 59389 * (3 : ZMod 36975198103) ^ 59389 := by rw [pow_add]
          _ = 23009548658 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 36975198103) ^ 237556 = 19850858729 := by
        calc
          (3 : ZMod 36975198103) ^ 237556 = (3 : ZMod 36975198103) ^ (118778 + 118778) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 118778 * (3 : ZMod 36975198103) ^ 118778 := by rw [pow_add]
          _ = 19850858729 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 36975198103) ^ 475113 = 21914799705 := by
        calc
          (3 : ZMod 36975198103) ^ 475113 = (3 : ZMod 36975198103) ^ (237556 + 237556 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 237556 * (3 : ZMod 36975198103) ^ 237556) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 21914799705 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 36975198103) ^ 950226 = 23448002873 := by
        calc
          (3 : ZMod 36975198103) ^ 950226 = (3 : ZMod 36975198103) ^ (475113 + 475113) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 475113 * (3 : ZMod 36975198103) ^ 475113 := by rw [pow_add]
          _ = 23448002873 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 36975198103) ^ 1900452 = 14837078626 := by
        calc
          (3 : ZMod 36975198103) ^ 1900452 = (3 : ZMod 36975198103) ^ (950226 + 950226) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 950226 * (3 : ZMod 36975198103) ^ 950226 := by rw [pow_add]
          _ = 14837078626 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 36975198103) ^ 3800904 = 18693770541 := by
        calc
          (3 : ZMod 36975198103) ^ 3800904 = (3 : ZMod 36975198103) ^ (1900452 + 1900452) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1900452 * (3 : ZMod 36975198103) ^ 1900452 := by rw [pow_add]
          _ = 18693770541 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 36975198103) ^ 7601808 = 4587239336 := by
        calc
          (3 : ZMod 36975198103) ^ 7601808 = (3 : ZMod 36975198103) ^ (3800904 + 3800904) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 3800904 * (3 : ZMod 36975198103) ^ 3800904 := by rw [pow_add]
          _ = 4587239336 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 36975198103) ^ 15203617 = 23150486802 := by
        calc
          (3 : ZMod 36975198103) ^ 15203617 = (3 : ZMod 36975198103) ^ (7601808 + 7601808 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 7601808 * (3 : ZMod 36975198103) ^ 7601808) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 23150486802 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 36975198103) ^ 30407235 = 13331231095 := by
        calc
          (3 : ZMod 36975198103) ^ 30407235 = (3 : ZMod 36975198103) ^ (15203617 + 15203617 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 15203617 * (3 : ZMod 36975198103) ^ 15203617) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 13331231095 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 36975198103) ^ 60814470 = 31531603410 := by
        calc
          (3 : ZMod 36975198103) ^ 60814470 = (3 : ZMod 36975198103) ^ (30407235 + 30407235) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 30407235 * (3 : ZMod 36975198103) ^ 30407235 := by rw [pow_add]
          _ = 31531603410 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 36975198103) ^ 121628941 = 17416534064 := by
        calc
          (3 : ZMod 36975198103) ^ 121628941 = (3 : ZMod 36975198103) ^ (60814470 + 60814470 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 60814470 * (3 : ZMod 36975198103) ^ 60814470) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 17416534064 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 36975198103) ^ 243257882 = 33089464981 := by
        calc
          (3 : ZMod 36975198103) ^ 243257882 = (3 : ZMod 36975198103) ^ (121628941 + 121628941) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 121628941 * (3 : ZMod 36975198103) ^ 121628941 := by rw [pow_add]
          _ = 33089464981 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 36975198103) ^ 486515764 = 27938533093 := by
        calc
          (3 : ZMod 36975198103) ^ 486515764 = (3 : ZMod 36975198103) ^ (243257882 + 243257882) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 243257882 * (3 : ZMod 36975198103) ^ 243257882 := by rw [pow_add]
          _ = 27938533093 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 36975198103) ^ 973031529 = 8000245008 := by
        calc
          (3 : ZMod 36975198103) ^ 973031529 = (3 : ZMod 36975198103) ^ (486515764 + 486515764 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 486515764 * (3 : ZMod 36975198103) ^ 486515764) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 8000245008 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 36975198103) ^ 1946063058 = 24627539652 := by
        calc
          (3 : ZMod 36975198103) ^ 1946063058 = (3 : ZMod 36975198103) ^ (973031529 + 973031529) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 973031529 * (3 : ZMod 36975198103) ^ 973031529 := by rw [pow_add]
          _ = 24627539652 := by rw [factor_2_29]; decide
      change (3 : ZMod 36975198103) ^ 1946063058 ≠ 1
      rw [factor_2_30]
      decide
    ·
      have factor_3_0 : (3 : ZMod 36975198103) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 36975198103) ^ 2 = 9 := by
        calc
          (3 : ZMod 36975198103) ^ 2 = (3 : ZMod 36975198103) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1 * (3 : ZMod 36975198103) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 36975198103) ^ 5 = 243 := by
        calc
          (3 : ZMod 36975198103) ^ 5 = (3 : ZMod 36975198103) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2 * (3 : ZMod 36975198103) ^ 2) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 36975198103) ^ 11 = 177147 := by
        calc
          (3 : ZMod 36975198103) ^ 11 = (3 : ZMod 36975198103) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 5 * (3 : ZMod 36975198103) ^ 5) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 36975198103) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 36975198103) ^ 22 = (3 : ZMod 36975198103) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 11 * (3 : ZMod 36975198103) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 36975198103) ^ 45 = 15129269278 := by
        calc
          (3 : ZMod 36975198103) ^ 45 = (3 : ZMod 36975198103) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 22 * (3 : ZMod 36975198103) ^ 22) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 15129269278 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 36975198103) ^ 91 = 25726892143 := by
        calc
          (3 : ZMod 36975198103) ^ 91 = (3 : ZMod 36975198103) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 45 * (3 : ZMod 36975198103) ^ 45) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 25726892143 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 36975198103) ^ 182 = 21206288260 := by
        calc
          (3 : ZMod 36975198103) ^ 182 = (3 : ZMod 36975198103) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 91 * (3 : ZMod 36975198103) ^ 91 := by rw [pow_add]
          _ = 21206288260 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 36975198103) ^ 364 = 24174408067 := by
        calc
          (3 : ZMod 36975198103) ^ 364 = (3 : ZMod 36975198103) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 182 * (3 : ZMod 36975198103) ^ 182 := by rw [pow_add]
          _ = 24174408067 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 36975198103) ^ 729 = 9310558163 := by
        calc
          (3 : ZMod 36975198103) ^ 729 = (3 : ZMod 36975198103) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 364 * (3 : ZMod 36975198103) ^ 364) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 9310558163 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 36975198103) ^ 1459 = 33166830416 := by
        calc
          (3 : ZMod 36975198103) ^ 1459 = (3 : ZMod 36975198103) ^ (729 + 729 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 729 * (3 : ZMod 36975198103) ^ 729) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 33166830416 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 36975198103) ^ 2919 = 1178747004 := by
        calc
          (3 : ZMod 36975198103) ^ 2919 = (3 : ZMod 36975198103) ^ (1459 + 1459 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1459 * (3 : ZMod 36975198103) ^ 1459) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 1178747004 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 36975198103) ^ 5839 = 23251063461 := by
        calc
          (3 : ZMod 36975198103) ^ 5839 = (3 : ZMod 36975198103) ^ (2919 + 2919 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2919 * (3 : ZMod 36975198103) ^ 2919) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 23251063461 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 36975198103) ^ 11678 = 1623772120 := by
        calc
          (3 : ZMod 36975198103) ^ 11678 = (3 : ZMod 36975198103) ^ (5839 + 5839) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 5839 * (3 : ZMod 36975198103) ^ 5839 := by rw [pow_add]
          _ = 1623772120 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 36975198103) ^ 23356 = 4040204813 := by
        calc
          (3 : ZMod 36975198103) ^ 23356 = (3 : ZMod 36975198103) ^ (11678 + 11678) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 11678 * (3 : ZMod 36975198103) ^ 11678 := by rw [pow_add]
          _ = 4040204813 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 36975198103) ^ 46712 = 24827422544 := by
        calc
          (3 : ZMod 36975198103) ^ 46712 = (3 : ZMod 36975198103) ^ (23356 + 23356) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 23356 * (3 : ZMod 36975198103) ^ 23356 := by rw [pow_add]
          _ = 24827422544 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 36975198103) ^ 93424 = 19807099656 := by
        calc
          (3 : ZMod 36975198103) ^ 93424 = (3 : ZMod 36975198103) ^ (46712 + 46712) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 46712 * (3 : ZMod 36975198103) ^ 46712 := by rw [pow_add]
          _ = 19807099656 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 36975198103) ^ 186849 = 36087835368 := by
        calc
          (3 : ZMod 36975198103) ^ 186849 = (3 : ZMod 36975198103) ^ (93424 + 93424 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 93424 * (3 : ZMod 36975198103) ^ 93424) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 36087835368 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 36975198103) ^ 373698 = 8150217434 := by
        calc
          (3 : ZMod 36975198103) ^ 373698 = (3 : ZMod 36975198103) ^ (186849 + 186849) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 186849 * (3 : ZMod 36975198103) ^ 186849 := by rw [pow_add]
          _ = 8150217434 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 36975198103) ^ 747396 = 35048015578 := by
        calc
          (3 : ZMod 36975198103) ^ 747396 = (3 : ZMod 36975198103) ^ (373698 + 373698) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 373698 * (3 : ZMod 36975198103) ^ 373698 := by rw [pow_add]
          _ = 35048015578 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 36975198103) ^ 1494792 = 31570151164 := by
        calc
          (3 : ZMod 36975198103) ^ 1494792 = (3 : ZMod 36975198103) ^ (747396 + 747396) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 747396 * (3 : ZMod 36975198103) ^ 747396 := by rw [pow_add]
          _ = 31570151164 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 36975198103) ^ 2989585 = 27878443192 := by
        calc
          (3 : ZMod 36975198103) ^ 2989585 = (3 : ZMod 36975198103) ^ (1494792 + 1494792 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1494792 * (3 : ZMod 36975198103) ^ 1494792) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 27878443192 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 36975198103) ^ 5979171 = 33577722437 := by
        calc
          (3 : ZMod 36975198103) ^ 5979171 = (3 : ZMod 36975198103) ^ (2989585 + 2989585 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2989585 * (3 : ZMod 36975198103) ^ 2989585) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 33577722437 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 36975198103) ^ 11958343 = 28956643577 := by
        calc
          (3 : ZMod 36975198103) ^ 11958343 = (3 : ZMod 36975198103) ^ (5979171 + 5979171 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 5979171 * (3 : ZMod 36975198103) ^ 5979171) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 28956643577 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 36975198103) ^ 23916687 = 23643547542 := by
        calc
          (3 : ZMod 36975198103) ^ 23916687 = (3 : ZMod 36975198103) ^ (11958343 + 11958343 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 11958343 * (3 : ZMod 36975198103) ^ 11958343) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 23643547542 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 36975198103) ^ 47833374 = 19876519872 := by
        calc
          (3 : ZMod 36975198103) ^ 47833374 = (3 : ZMod 36975198103) ^ (23916687 + 23916687) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 23916687 * (3 : ZMod 36975198103) ^ 23916687 := by rw [pow_add]
          _ = 19876519872 := by rw [factor_3_24]; decide
      change (3 : ZMod 36975198103) ^ 47833374 ≠ 1
      rw [factor_3_25]
      decide
    ·
      have factor_4_0 : (3 : ZMod 36975198103) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 36975198103) ^ 2 = 9 := by
        calc
          (3 : ZMod 36975198103) ^ 2 = (3 : ZMod 36975198103) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 1 * (3 : ZMod 36975198103) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 36975198103) ^ 5 = 243 := by
        calc
          (3 : ZMod 36975198103) ^ 5 = (3 : ZMod 36975198103) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2 * (3 : ZMod 36975198103) ^ 2) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 36975198103) ^ 10 = 59049 := by
        calc
          (3 : ZMod 36975198103) ^ 10 = (3 : ZMod 36975198103) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 5 * (3 : ZMod 36975198103) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 36975198103) ^ 21 = 10460353203 := by
        calc
          (3 : ZMod 36975198103) ^ 21 = (3 : ZMod 36975198103) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 10 * (3 : ZMod 36975198103) ^ 10) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 10460353203 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 36975198103) ^ 43 = 34547872678 := by
        calc
          (3 : ZMod 36975198103) ^ 43 = (3 : ZMod 36975198103) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 21 * (3 : ZMod 36975198103) ^ 21) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 34547872678 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 36975198103) ^ 86 = 11365808855 := by
        calc
          (3 : ZMod 36975198103) ^ 86 = (3 : ZMod 36975198103) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 43 * (3 : ZMod 36975198103) ^ 43 := by rw [pow_add]
          _ = 11365808855 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 36975198103) ^ 172 = 76752874 := by
        calc
          (3 : ZMod 36975198103) ^ 172 = (3 : ZMod 36975198103) ^ (86 + 86) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 86 * (3 : ZMod 36975198103) ^ 86 := by rw [pow_add]
          _ = 76752874 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 36975198103) ^ 344 = 4179895607 := by
        calc
          (3 : ZMod 36975198103) ^ 344 = (3 : ZMod 36975198103) ^ (172 + 172) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 172 * (3 : ZMod 36975198103) ^ 172 := by rw [pow_add]
          _ = 4179895607 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 36975198103) ^ 688 = 22252679909 := by
        calc
          (3 : ZMod 36975198103) ^ 688 = (3 : ZMod 36975198103) ^ (344 + 344) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 344 * (3 : ZMod 36975198103) ^ 344 := by rw [pow_add]
          _ = 22252679909 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 36975198103) ^ 1376 = 7465484118 := by
        calc
          (3 : ZMod 36975198103) ^ 1376 = (3 : ZMod 36975198103) ^ (688 + 688) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 688 * (3 : ZMod 36975198103) ^ 688 := by rw [pow_add]
          _ = 7465484118 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 36975198103) ^ 2753 = 3478850578 := by
        calc
          (3 : ZMod 36975198103) ^ 2753 = (3 : ZMod 36975198103) ^ (1376 + 1376 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 1376 * (3 : ZMod 36975198103) ^ 1376) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 3478850578 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 36975198103) ^ 5507 = 5982392664 := by
        calc
          (3 : ZMod 36975198103) ^ 5507 = (3 : ZMod 36975198103) ^ (2753 + 2753 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 2753 * (3 : ZMod 36975198103) ^ 2753) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 5982392664 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 36975198103) ^ 11015 = 26589959053 := by
        calc
          (3 : ZMod 36975198103) ^ 11015 = (3 : ZMod 36975198103) ^ (5507 + 5507 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 5507 * (3 : ZMod 36975198103) ^ 5507) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 26589959053 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 36975198103) ^ 22030 = 23471446553 := by
        calc
          (3 : ZMod 36975198103) ^ 22030 = (3 : ZMod 36975198103) ^ (11015 + 11015) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 11015 * (3 : ZMod 36975198103) ^ 11015 := by rw [pow_add]
          _ = 23471446553 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 36975198103) ^ 44061 = 12441146498 := by
        calc
          (3 : ZMod 36975198103) ^ 44061 = (3 : ZMod 36975198103) ^ (22030 + 22030 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = ((3 : ZMod 36975198103) ^ 22030 * (3 : ZMod 36975198103) ^ 22030) * (3 : ZMod 36975198103) := by rw [pow_succ, pow_add]
          _ = 12441146498 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 36975198103) ^ 88122 = 8018159269 := by
        calc
          (3 : ZMod 36975198103) ^ 88122 = (3 : ZMod 36975198103) ^ (44061 + 44061) :=
            congrArg (fun n : ℕ => (3 : ZMod 36975198103) ^ n) (by norm_num)
          _ = (3 : ZMod 36975198103) ^ 44061 * (3 : ZMod 36975198103) ^ 44061 := by rw [pow_add]
          _ = 8018159269 := by rw [factor_4_15]; decide
      change (3 : ZMod 36975198103) ^ 88122 ≠ 1
      rw [factor_4_16]
      decide

#print axioms prime_lucas_36975198103

end TotientTailPeriodKiller
end Erdos249257
