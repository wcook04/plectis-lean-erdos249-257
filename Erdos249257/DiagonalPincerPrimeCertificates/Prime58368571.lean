import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_58368571 : Nat.Prime 58368571 := by
  apply lucas_primality 58368571 (10 : ZMod 58368571)
  ·
      have fermat_0 : (10 : ZMod 58368571) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 58368571) ^ 3 = 1000 := by
        calc
          (10 : ZMod 58368571) ^ 3 = (10 : ZMod 58368571) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 1 * (10 : ZMod 58368571) ^ 1) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 58368571) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 58368571) ^ 6 = (10 : ZMod 58368571) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 3 * (10 : ZMod 58368571) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 58368571) ^ 13 = 4573425 := by
        calc
          (10 : ZMod 58368571) ^ 13 = (10 : ZMod 58368571) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 6 * (10 : ZMod 58368571) ^ 6) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 4573425 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 58368571) ^ 27 = 22447738 := by
        calc
          (10 : ZMod 58368571) ^ 27 = (10 : ZMod 58368571) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 13 * (10 : ZMod 58368571) ^ 13) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 22447738 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 58368571) ^ 55 = 14816812 := by
        calc
          (10 : ZMod 58368571) ^ 55 = (10 : ZMod 58368571) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 27 * (10 : ZMod 58368571) ^ 27) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 14816812 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 58368571) ^ 111 = 56981590 := by
        calc
          (10 : ZMod 58368571) ^ 111 = (10 : ZMod 58368571) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 55 * (10 : ZMod 58368571) ^ 55) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 56981590 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 58368571) ^ 222 = 4931343 := by
        calc
          (10 : ZMod 58368571) ^ 222 = (10 : ZMod 58368571) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 111 * (10 : ZMod 58368571) ^ 111 := by rw [pow_add]
          _ = 4931343 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 58368571) ^ 445 = 51899193 := by
        calc
          (10 : ZMod 58368571) ^ 445 = (10 : ZMod 58368571) ^ (222 + 222 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 222 * (10 : ZMod 58368571) ^ 222) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 51899193 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 58368571) ^ 890 = 18082760 := by
        calc
          (10 : ZMod 58368571) ^ 890 = (10 : ZMod 58368571) ^ (445 + 445) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 445 * (10 : ZMod 58368571) ^ 445 := by rw [pow_add]
          _ = 18082760 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 58368571) ^ 1781 = 53404973 := by
        calc
          (10 : ZMod 58368571) ^ 1781 = (10 : ZMod 58368571) ^ (890 + 890 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 890 * (10 : ZMod 58368571) ^ 890) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 53404973 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 58368571) ^ 3562 = 48023646 := by
        calc
          (10 : ZMod 58368571) ^ 3562 = (10 : ZMod 58368571) ^ (1781 + 1781) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1781 * (10 : ZMod 58368571) ^ 1781 := by rw [pow_add]
          _ = 48023646 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 58368571) ^ 7125 = 57831154 := by
        calc
          (10 : ZMod 58368571) ^ 7125 = (10 : ZMod 58368571) ^ (3562 + 3562 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 3562 * (10 : ZMod 58368571) ^ 3562) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 57831154 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 58368571) ^ 14250 = 9342581 := by
        calc
          (10 : ZMod 58368571) ^ 14250 = (10 : ZMod 58368571) ^ (7125 + 7125) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 7125 * (10 : ZMod 58368571) ^ 7125 := by rw [pow_add]
          _ = 9342581 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 58368571) ^ 28500 = 42353871 := by
        calc
          (10 : ZMod 58368571) ^ 28500 = (10 : ZMod 58368571) ^ (14250 + 14250) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 14250 * (10 : ZMod 58368571) ^ 14250 := by rw [pow_add]
          _ = 42353871 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 58368571) ^ 57000 = 49013136 := by
        calc
          (10 : ZMod 58368571) ^ 57000 = (10 : ZMod 58368571) ^ (28500 + 28500) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 28500 * (10 : ZMod 58368571) ^ 28500 := by rw [pow_add]
          _ = 49013136 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 58368571) ^ 114001 = 15287286 := by
        calc
          (10 : ZMod 58368571) ^ 114001 = (10 : ZMod 58368571) ^ (57000 + 57000 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 57000 * (10 : ZMod 58368571) ^ 57000) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 15287286 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 58368571) ^ 228002 = 8978890 := by
        calc
          (10 : ZMod 58368571) ^ 228002 = (10 : ZMod 58368571) ^ (114001 + 114001) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 114001 * (10 : ZMod 58368571) ^ 114001 := by rw [pow_add]
          _ = 8978890 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 58368571) ^ 456004 = 44309770 := by
        calc
          (10 : ZMod 58368571) ^ 456004 = (10 : ZMod 58368571) ^ (228002 + 228002) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 228002 * (10 : ZMod 58368571) ^ 228002 := by rw [pow_add]
          _ = 44309770 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 58368571) ^ 912008 = 12431703 := by
        calc
          (10 : ZMod 58368571) ^ 912008 = (10 : ZMod 58368571) ^ (456004 + 456004) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 456004 * (10 : ZMod 58368571) ^ 456004 := by rw [pow_add]
          _ = 12431703 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 58368571) ^ 1824017 = 53312583 := by
        calc
          (10 : ZMod 58368571) ^ 1824017 = (10 : ZMod 58368571) ^ (912008 + 912008 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 912008 * (10 : ZMod 58368571) ^ 912008) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 53312583 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 58368571) ^ 3648035 = 28538405 := by
        calc
          (10 : ZMod 58368571) ^ 3648035 = (10 : ZMod 58368571) ^ (1824017 + 1824017 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 1824017 * (10 : ZMod 58368571) ^ 1824017) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 28538405 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 58368571) ^ 7296071 = 43617718 := by
        calc
          (10 : ZMod 58368571) ^ 7296071 = (10 : ZMod 58368571) ^ (3648035 + 3648035 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 3648035 * (10 : ZMod 58368571) ^ 3648035) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 43617718 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 58368571) ^ 14592142 = 21145247 := by
        calc
          (10 : ZMod 58368571) ^ 14592142 = (10 : ZMod 58368571) ^ (7296071 + 7296071) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 7296071 * (10 : ZMod 58368571) ^ 7296071 := by rw [pow_add]
          _ = 21145247 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 58368571) ^ 29184285 = 58368570 := by
        calc
          (10 : ZMod 58368571) ^ 29184285 = (10 : ZMod 58368571) ^ (14592142 + 14592142 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 14592142 * (10 : ZMod 58368571) ^ 14592142) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 58368570 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 58368571) ^ 58368570 = 1 := by
        calc
          (10 : ZMod 58368571) ^ 58368570 = (10 : ZMod 58368571) ^ (29184285 + 29184285) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 29184285 * (10 : ZMod 58368571) ^ 29184285 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 1), (19, 1), (7877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 1), (19, 1), (7877, 1)] : List FactorBlock).map factorBlockValue).prod = 58368571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 58368571) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 58368571) ^ 3 = 1000 := by
        calc
          (10 : ZMod 58368571) ^ 3 = (10 : ZMod 58368571) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 1 * (10 : ZMod 58368571) ^ 1) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 58368571) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 58368571) ^ 6 = (10 : ZMod 58368571) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 3 * (10 : ZMod 58368571) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 58368571) ^ 13 = 4573425 := by
        calc
          (10 : ZMod 58368571) ^ 13 = (10 : ZMod 58368571) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 6 * (10 : ZMod 58368571) ^ 6) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 4573425 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 58368571) ^ 27 = 22447738 := by
        calc
          (10 : ZMod 58368571) ^ 27 = (10 : ZMod 58368571) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 13 * (10 : ZMod 58368571) ^ 13) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 22447738 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 58368571) ^ 55 = 14816812 := by
        calc
          (10 : ZMod 58368571) ^ 55 = (10 : ZMod 58368571) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 27 * (10 : ZMod 58368571) ^ 27) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 14816812 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 58368571) ^ 111 = 56981590 := by
        calc
          (10 : ZMod 58368571) ^ 111 = (10 : ZMod 58368571) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 55 * (10 : ZMod 58368571) ^ 55) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 56981590 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 58368571) ^ 222 = 4931343 := by
        calc
          (10 : ZMod 58368571) ^ 222 = (10 : ZMod 58368571) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 111 * (10 : ZMod 58368571) ^ 111 := by rw [pow_add]
          _ = 4931343 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 58368571) ^ 445 = 51899193 := by
        calc
          (10 : ZMod 58368571) ^ 445 = (10 : ZMod 58368571) ^ (222 + 222 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 222 * (10 : ZMod 58368571) ^ 222) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 51899193 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 58368571) ^ 890 = 18082760 := by
        calc
          (10 : ZMod 58368571) ^ 890 = (10 : ZMod 58368571) ^ (445 + 445) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 445 * (10 : ZMod 58368571) ^ 445 := by rw [pow_add]
          _ = 18082760 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 58368571) ^ 1781 = 53404973 := by
        calc
          (10 : ZMod 58368571) ^ 1781 = (10 : ZMod 58368571) ^ (890 + 890 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 890 * (10 : ZMod 58368571) ^ 890) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 53404973 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 58368571) ^ 3562 = 48023646 := by
        calc
          (10 : ZMod 58368571) ^ 3562 = (10 : ZMod 58368571) ^ (1781 + 1781) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1781 * (10 : ZMod 58368571) ^ 1781 := by rw [pow_add]
          _ = 48023646 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 58368571) ^ 7125 = 57831154 := by
        calc
          (10 : ZMod 58368571) ^ 7125 = (10 : ZMod 58368571) ^ (3562 + 3562 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 3562 * (10 : ZMod 58368571) ^ 3562) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 57831154 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 58368571) ^ 14250 = 9342581 := by
        calc
          (10 : ZMod 58368571) ^ 14250 = (10 : ZMod 58368571) ^ (7125 + 7125) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 7125 * (10 : ZMod 58368571) ^ 7125 := by rw [pow_add]
          _ = 9342581 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 58368571) ^ 28500 = 42353871 := by
        calc
          (10 : ZMod 58368571) ^ 28500 = (10 : ZMod 58368571) ^ (14250 + 14250) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 14250 * (10 : ZMod 58368571) ^ 14250 := by rw [pow_add]
          _ = 42353871 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 58368571) ^ 57000 = 49013136 := by
        calc
          (10 : ZMod 58368571) ^ 57000 = (10 : ZMod 58368571) ^ (28500 + 28500) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 28500 * (10 : ZMod 58368571) ^ 28500 := by rw [pow_add]
          _ = 49013136 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 58368571) ^ 114001 = 15287286 := by
        calc
          (10 : ZMod 58368571) ^ 114001 = (10 : ZMod 58368571) ^ (57000 + 57000 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 57000 * (10 : ZMod 58368571) ^ 57000) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 15287286 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 58368571) ^ 228002 = 8978890 := by
        calc
          (10 : ZMod 58368571) ^ 228002 = (10 : ZMod 58368571) ^ (114001 + 114001) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 114001 * (10 : ZMod 58368571) ^ 114001 := by rw [pow_add]
          _ = 8978890 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 58368571) ^ 456004 = 44309770 := by
        calc
          (10 : ZMod 58368571) ^ 456004 = (10 : ZMod 58368571) ^ (228002 + 228002) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 228002 * (10 : ZMod 58368571) ^ 228002 := by rw [pow_add]
          _ = 44309770 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 58368571) ^ 912008 = 12431703 := by
        calc
          (10 : ZMod 58368571) ^ 912008 = (10 : ZMod 58368571) ^ (456004 + 456004) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 456004 * (10 : ZMod 58368571) ^ 456004 := by rw [pow_add]
          _ = 12431703 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 58368571) ^ 1824017 = 53312583 := by
        calc
          (10 : ZMod 58368571) ^ 1824017 = (10 : ZMod 58368571) ^ (912008 + 912008 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 912008 * (10 : ZMod 58368571) ^ 912008) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 53312583 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 58368571) ^ 3648035 = 28538405 := by
        calc
          (10 : ZMod 58368571) ^ 3648035 = (10 : ZMod 58368571) ^ (1824017 + 1824017 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 1824017 * (10 : ZMod 58368571) ^ 1824017) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 28538405 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 58368571) ^ 7296071 = 43617718 := by
        calc
          (10 : ZMod 58368571) ^ 7296071 = (10 : ZMod 58368571) ^ (3648035 + 3648035 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 3648035 * (10 : ZMod 58368571) ^ 3648035) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 43617718 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 58368571) ^ 14592142 = 21145247 := by
        calc
          (10 : ZMod 58368571) ^ 14592142 = (10 : ZMod 58368571) ^ (7296071 + 7296071) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 7296071 * (10 : ZMod 58368571) ^ 7296071 := by rw [pow_add]
          _ = 21145247 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 58368571) ^ 29184285 = 58368570 := by
        calc
          (10 : ZMod 58368571) ^ 29184285 = (10 : ZMod 58368571) ^ (14592142 + 14592142 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 14592142 * (10 : ZMod 58368571) ^ 14592142) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 58368570 := by rw [factor_0_23]; decide
      change (10 : ZMod 58368571) ^ 29184285 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (10 : ZMod 58368571) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 58368571) ^ 2 = 100 := by
        calc
          (10 : ZMod 58368571) ^ 2 = (10 : ZMod 58368571) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1 * (10 : ZMod 58368571) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 58368571) ^ 4 = 10000 := by
        calc
          (10 : ZMod 58368571) ^ 4 = (10 : ZMod 58368571) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 2 * (10 : ZMod 58368571) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 58368571) ^ 9 = 7734293 := by
        calc
          (10 : ZMod 58368571) ^ 9 = (10 : ZMod 58368571) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 4 * (10 : ZMod 58368571) ^ 4) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 7734293 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 58368571) ^ 18 = 24746215 := by
        calc
          (10 : ZMod 58368571) ^ 18 = (10 : ZMod 58368571) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 9 * (10 : ZMod 58368571) ^ 9 := by rw [pow_add]
          _ = 24746215 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 58368571) ^ 37 = 42343059 := by
        calc
          (10 : ZMod 58368571) ^ 37 = (10 : ZMod 58368571) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 18 * (10 : ZMod 58368571) ^ 18) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 42343059 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 58368571) ^ 74 = 50316395 := by
        calc
          (10 : ZMod 58368571) ^ 74 = (10 : ZMod 58368571) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 37 * (10 : ZMod 58368571) ^ 37 := by rw [pow_add]
          _ = 50316395 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 58368571) ^ 148 = 36979617 := by
        calc
          (10 : ZMod 58368571) ^ 148 = (10 : ZMod 58368571) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 74 * (10 : ZMod 58368571) ^ 74 := by rw [pow_add]
          _ = 36979617 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 58368571) ^ 296 = 38730361 := by
        calc
          (10 : ZMod 58368571) ^ 296 = (10 : ZMod 58368571) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 148 * (10 : ZMod 58368571) ^ 148 := by rw [pow_add]
          _ = 38730361 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 58368571) ^ 593 = 24552332 := by
        calc
          (10 : ZMod 58368571) ^ 593 = (10 : ZMod 58368571) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 296 * (10 : ZMod 58368571) ^ 296) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 24552332 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 58368571) ^ 1187 = 52272670 := by
        calc
          (10 : ZMod 58368571) ^ 1187 = (10 : ZMod 58368571) ^ (593 + 593 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 593 * (10 : ZMod 58368571) ^ 593) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 52272670 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 58368571) ^ 2375 = 26492199 := by
        calc
          (10 : ZMod 58368571) ^ 2375 = (10 : ZMod 58368571) ^ (1187 + 1187 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 1187 * (10 : ZMod 58368571) ^ 1187) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 26492199 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 58368571) ^ 4750 = 10697410 := by
        calc
          (10 : ZMod 58368571) ^ 4750 = (10 : ZMod 58368571) ^ (2375 + 2375) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 2375 * (10 : ZMod 58368571) ^ 2375 := by rw [pow_add]
          _ = 10697410 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 58368571) ^ 9500 = 20465479 := by
        calc
          (10 : ZMod 58368571) ^ 9500 = (10 : ZMod 58368571) ^ (4750 + 4750) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 4750 * (10 : ZMod 58368571) ^ 4750 := by rw [pow_add]
          _ = 20465479 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 58368571) ^ 19000 = 8826173 := by
        calc
          (10 : ZMod 58368571) ^ 19000 = (10 : ZMod 58368571) ^ (9500 + 9500) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 9500 * (10 : ZMod 58368571) ^ 9500 := by rw [pow_add]
          _ = 8826173 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 58368571) ^ 38000 = 8383634 := by
        calc
          (10 : ZMod 58368571) ^ 38000 = (10 : ZMod 58368571) ^ (19000 + 19000) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 19000 * (10 : ZMod 58368571) ^ 19000 := by rw [pow_add]
          _ = 8383634 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 58368571) ^ 76000 = 45484883 := by
        calc
          (10 : ZMod 58368571) ^ 76000 = (10 : ZMod 58368571) ^ (38000 + 38000) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 38000 * (10 : ZMod 58368571) ^ 38000 := by rw [pow_add]
          _ = 45484883 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 58368571) ^ 152001 = 45798361 := by
        calc
          (10 : ZMod 58368571) ^ 152001 = (10 : ZMod 58368571) ^ (76000 + 76000 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 76000 * (10 : ZMod 58368571) ^ 76000) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 45798361 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 58368571) ^ 304002 = 37204290 := by
        calc
          (10 : ZMod 58368571) ^ 304002 = (10 : ZMod 58368571) ^ (152001 + 152001) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 152001 * (10 : ZMod 58368571) ^ 152001 := by rw [pow_add]
          _ = 37204290 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 58368571) ^ 608005 = 25450078 := by
        calc
          (10 : ZMod 58368571) ^ 608005 = (10 : ZMod 58368571) ^ (304002 + 304002 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 304002 * (10 : ZMod 58368571) ^ 304002) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 25450078 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 58368571) ^ 1216011 = 44278709 := by
        calc
          (10 : ZMod 58368571) ^ 1216011 = (10 : ZMod 58368571) ^ (608005 + 608005 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 608005 * (10 : ZMod 58368571) ^ 608005) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 44278709 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 58368571) ^ 2432023 = 2069944 := by
        calc
          (10 : ZMod 58368571) ^ 2432023 = (10 : ZMod 58368571) ^ (1216011 + 1216011 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 1216011 * (10 : ZMod 58368571) ^ 1216011) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 2069944 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 58368571) ^ 4864047 = 6348819 := by
        calc
          (10 : ZMod 58368571) ^ 4864047 = (10 : ZMod 58368571) ^ (2432023 + 2432023 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 2432023 * (10 : ZMod 58368571) ^ 2432023) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 6348819 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 58368571) ^ 9728095 = 3352904 := by
        calc
          (10 : ZMod 58368571) ^ 9728095 = (10 : ZMod 58368571) ^ (4864047 + 4864047 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 4864047 * (10 : ZMod 58368571) ^ 4864047) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 3352904 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 58368571) ^ 19456190 = 3352903 := by
        calc
          (10 : ZMod 58368571) ^ 19456190 = (10 : ZMod 58368571) ^ (9728095 + 9728095) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 9728095 * (10 : ZMod 58368571) ^ 9728095 := by rw [pow_add]
          _ = 3352903 := by rw [factor_1_23]; decide
      change (10 : ZMod 58368571) ^ 19456190 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (10 : ZMod 58368571) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 58368571) ^ 2 = 100 := by
        calc
          (10 : ZMod 58368571) ^ 2 = (10 : ZMod 58368571) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1 * (10 : ZMod 58368571) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 58368571) ^ 5 = 100000 := by
        calc
          (10 : ZMod 58368571) ^ 5 = (10 : ZMod 58368571) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 2 * (10 : ZMod 58368571) ^ 2) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 58368571) ^ 11 = 14637877 := by
        calc
          (10 : ZMod 58368571) ^ 11 = (10 : ZMod 58368571) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 5 * (10 : ZMod 58368571) ^ 5) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 14637877 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 58368571) ^ 22 = 37777531 := by
        calc
          (10 : ZMod 58368571) ^ 22 = (10 : ZMod 58368571) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 11 * (10 : ZMod 58368571) ^ 11 := by rw [pow_add]
          _ = 37777531 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 58368571) ^ 44 = 52586183 := by
        calc
          (10 : ZMod 58368571) ^ 44 = (10 : ZMod 58368571) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 22 * (10 : ZMod 58368571) ^ 22 := by rw [pow_add]
          _ = 52586183 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 58368571) ^ 89 = 11757623 := by
        calc
          (10 : ZMod 58368571) ^ 89 = (10 : ZMod 58368571) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 44 * (10 : ZMod 58368571) ^ 44) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 11757623 := by rw [factor_2_5]; decide
      have factor_2_7 : (10 : ZMod 58368571) ^ 178 = 57470883 := by
        calc
          (10 : ZMod 58368571) ^ 178 = (10 : ZMod 58368571) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 89 * (10 : ZMod 58368571) ^ 89 := by rw [pow_add]
          _ = 57470883 := by rw [factor_2_6]; decide
      have factor_2_8 : (10 : ZMod 58368571) ^ 356 = 7254118 := by
        calc
          (10 : ZMod 58368571) ^ 356 = (10 : ZMod 58368571) ^ (178 + 178) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 178 * (10 : ZMod 58368571) ^ 178 := by rw [pow_add]
          _ = 7254118 := by rw [factor_2_7]; decide
      have factor_2_9 : (10 : ZMod 58368571) ^ 712 = 42772874 := by
        calc
          (10 : ZMod 58368571) ^ 712 = (10 : ZMod 58368571) ^ (356 + 356) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 356 * (10 : ZMod 58368571) ^ 356 := by rw [pow_add]
          _ = 42772874 := by rw [factor_2_8]; decide
      have factor_2_10 : (10 : ZMod 58368571) ^ 1425 = 13539807 := by
        calc
          (10 : ZMod 58368571) ^ 1425 = (10 : ZMod 58368571) ^ (712 + 712 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 712 * (10 : ZMod 58368571) ^ 712) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 13539807 := by rw [factor_2_9]; decide
      have factor_2_11 : (10 : ZMod 58368571) ^ 2850 = 31057609 := by
        calc
          (10 : ZMod 58368571) ^ 2850 = (10 : ZMod 58368571) ^ (1425 + 1425) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1425 * (10 : ZMod 58368571) ^ 1425 := by rw [pow_add]
          _ = 31057609 := by rw [factor_2_10]; decide
      have factor_2_12 : (10 : ZMod 58368571) ^ 5700 = 3564991 := by
        calc
          (10 : ZMod 58368571) ^ 5700 = (10 : ZMod 58368571) ^ (2850 + 2850) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 2850 * (10 : ZMod 58368571) ^ 2850 := by rw [pow_add]
          _ = 3564991 := by rw [factor_2_11]; decide
      have factor_2_13 : (10 : ZMod 58368571) ^ 11400 = 46549112 := by
        calc
          (10 : ZMod 58368571) ^ 11400 = (10 : ZMod 58368571) ^ (5700 + 5700) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 5700 * (10 : ZMod 58368571) ^ 5700 := by rw [pow_add]
          _ = 46549112 := by rw [factor_2_12]; decide
      have factor_2_14 : (10 : ZMod 58368571) ^ 22800 = 39746997 := by
        calc
          (10 : ZMod 58368571) ^ 22800 = (10 : ZMod 58368571) ^ (11400 + 11400) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 11400 * (10 : ZMod 58368571) ^ 11400 := by rw [pow_add]
          _ = 39746997 := by rw [factor_2_13]; decide
      have factor_2_15 : (10 : ZMod 58368571) ^ 45600 = 7412156 := by
        calc
          (10 : ZMod 58368571) ^ 45600 = (10 : ZMod 58368571) ^ (22800 + 22800) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 22800 * (10 : ZMod 58368571) ^ 22800 := by rw [pow_add]
          _ = 7412156 := by rw [factor_2_14]; decide
      have factor_2_16 : (10 : ZMod 58368571) ^ 91200 = 55428876 := by
        calc
          (10 : ZMod 58368571) ^ 91200 = (10 : ZMod 58368571) ^ (45600 + 45600) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 45600 * (10 : ZMod 58368571) ^ 45600 := by rw [pow_add]
          _ = 55428876 := by rw [factor_2_15]; decide
      have factor_2_17 : (10 : ZMod 58368571) ^ 182401 = 12187632 := by
        calc
          (10 : ZMod 58368571) ^ 182401 = (10 : ZMod 58368571) ^ (91200 + 91200 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 91200 * (10 : ZMod 58368571) ^ 91200) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 12187632 := by rw [factor_2_16]; decide
      have factor_2_18 : (10 : ZMod 58368571) ^ 364803 = 30603532 := by
        calc
          (10 : ZMod 58368571) ^ 364803 = (10 : ZMod 58368571) ^ (182401 + 182401 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 182401 * (10 : ZMod 58368571) ^ 182401) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 30603532 := by rw [factor_2_17]; decide
      have factor_2_19 : (10 : ZMod 58368571) ^ 729607 = 50189805 := by
        calc
          (10 : ZMod 58368571) ^ 729607 = (10 : ZMod 58368571) ^ (364803 + 364803 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 364803 * (10 : ZMod 58368571) ^ 364803) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 50189805 := by rw [factor_2_18]; decide
      have factor_2_20 : (10 : ZMod 58368571) ^ 1459214 = 21491055 := by
        calc
          (10 : ZMod 58368571) ^ 1459214 = (10 : ZMod 58368571) ^ (729607 + 729607) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 729607 * (10 : ZMod 58368571) ^ 729607 := by rw [pow_add]
          _ = 21491055 := by rw [factor_2_19]; decide
      have factor_2_21 : (10 : ZMod 58368571) ^ 2918428 = 20755702 := by
        calc
          (10 : ZMod 58368571) ^ 2918428 = (10 : ZMod 58368571) ^ (1459214 + 1459214) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1459214 * (10 : ZMod 58368571) ^ 1459214 := by rw [pow_add]
          _ = 20755702 := by rw [factor_2_20]; decide
      have factor_2_22 : (10 : ZMod 58368571) ^ 5836857 = 45902340 := by
        calc
          (10 : ZMod 58368571) ^ 5836857 = (10 : ZMod 58368571) ^ (2918428 + 2918428 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 2918428 * (10 : ZMod 58368571) ^ 2918428) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 45902340 := by rw [factor_2_21]; decide
      have factor_2_23 : (10 : ZMod 58368571) ^ 11673714 = 11372151 := by
        calc
          (10 : ZMod 58368571) ^ 11673714 = (10 : ZMod 58368571) ^ (5836857 + 5836857) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 5836857 * (10 : ZMod 58368571) ^ 5836857 := by rw [pow_add]
          _ = 11372151 := by rw [factor_2_22]; decide
      change (10 : ZMod 58368571) ^ 11673714 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (10 : ZMod 58368571) ^ 1 = 10 := by norm_num
      have factor_3_1 : (10 : ZMod 58368571) ^ 2 = 100 := by
        calc
          (10 : ZMod 58368571) ^ 2 = (10 : ZMod 58368571) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1 * (10 : ZMod 58368571) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_3_0]; decide
      have factor_3_2 : (10 : ZMod 58368571) ^ 4 = 10000 := by
        calc
          (10 : ZMod 58368571) ^ 4 = (10 : ZMod 58368571) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 2 * (10 : ZMod 58368571) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_3_1]; decide
      have factor_3_3 : (10 : ZMod 58368571) ^ 8 = 41631429 := by
        calc
          (10 : ZMod 58368571) ^ 8 = (10 : ZMod 58368571) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 4 * (10 : ZMod 58368571) ^ 4 := by rw [pow_add]
          _ = 41631429 := by rw [factor_3_2]; decide
      have factor_3_4 : (10 : ZMod 58368571) ^ 17 = 31658907 := by
        calc
          (10 : ZMod 58368571) ^ 17 = (10 : ZMod 58368571) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 8 * (10 : ZMod 58368571) ^ 8) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 31658907 := by rw [factor_3_3]; decide
      have factor_3_5 : (10 : ZMod 58368571) ^ 34 = 27533940 := by
        calc
          (10 : ZMod 58368571) ^ 34 = (10 : ZMod 58368571) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 17 * (10 : ZMod 58368571) ^ 17 := by rw [pow_add]
          _ = 27533940 := by rw [factor_3_4]; decide
      have factor_3_6 : (10 : ZMod 58368571) ^ 68 = 2232940 := by
        calc
          (10 : ZMod 58368571) ^ 68 = (10 : ZMod 58368571) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 34 * (10 : ZMod 58368571) ^ 34 := by rw [pow_add]
          _ = 2232940 := by rw [factor_3_5]; decide
      have factor_3_7 : (10 : ZMod 58368571) ^ 137 = 26030670 := by
        calc
          (10 : ZMod 58368571) ^ 137 = (10 : ZMod 58368571) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 68 * (10 : ZMod 58368571) ^ 68) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 26030670 := by rw [factor_3_6]; decide
      have factor_3_8 : (10 : ZMod 58368571) ^ 274 = 1238435 := by
        calc
          (10 : ZMod 58368571) ^ 274 = (10 : ZMod 58368571) ^ (137 + 137) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 137 * (10 : ZMod 58368571) ^ 137 := by rw [pow_add]
          _ = 1238435 := by rw [factor_3_7]; decide
      have factor_3_9 : (10 : ZMod 58368571) ^ 548 = 28677629 := by
        calc
          (10 : ZMod 58368571) ^ 548 = (10 : ZMod 58368571) ^ (274 + 274) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 274 * (10 : ZMod 58368571) ^ 274 := by rw [pow_add]
          _ = 28677629 := by rw [factor_3_8]; decide
      have factor_3_10 : (10 : ZMod 58368571) ^ 1096 = 10425877 := by
        calc
          (10 : ZMod 58368571) ^ 1096 = (10 : ZMod 58368571) ^ (548 + 548) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 548 * (10 : ZMod 58368571) ^ 548 := by rw [pow_add]
          _ = 10425877 := by rw [factor_3_9]; decide
      have factor_3_11 : (10 : ZMod 58368571) ^ 2192 = 55342965 := by
        calc
          (10 : ZMod 58368571) ^ 2192 = (10 : ZMod 58368571) ^ (1096 + 1096) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1096 * (10 : ZMod 58368571) ^ 1096 := by rw [pow_add]
          _ = 55342965 := by rw [factor_3_10]; decide
      have factor_3_12 : (10 : ZMod 58368571) ^ 4384 = 56834451 := by
        calc
          (10 : ZMod 58368571) ^ 4384 = (10 : ZMod 58368571) ^ (2192 + 2192) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 2192 * (10 : ZMod 58368571) ^ 2192 := by rw [pow_add]
          _ = 56834451 := by rw [factor_3_11]; decide
      have factor_3_13 : (10 : ZMod 58368571) ^ 8769 = 41651093 := by
        calc
          (10 : ZMod 58368571) ^ 8769 = (10 : ZMod 58368571) ^ (4384 + 4384 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 4384 * (10 : ZMod 58368571) ^ 4384) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 41651093 := by rw [factor_3_12]; decide
      have factor_3_14 : (10 : ZMod 58368571) ^ 17538 = 41192523 := by
        calc
          (10 : ZMod 58368571) ^ 17538 = (10 : ZMod 58368571) ^ (8769 + 8769) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 8769 * (10 : ZMod 58368571) ^ 8769 := by rw [pow_add]
          _ = 41192523 := by rw [factor_3_13]; decide
      have factor_3_15 : (10 : ZMod 58368571) ^ 35077 = 21976074 := by
        calc
          (10 : ZMod 58368571) ^ 35077 = (10 : ZMod 58368571) ^ (17538 + 17538 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 17538 * (10 : ZMod 58368571) ^ 17538) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 21976074 := by rw [factor_3_14]; decide
      have factor_3_16 : (10 : ZMod 58368571) ^ 70154 = 26562379 := by
        calc
          (10 : ZMod 58368571) ^ 70154 = (10 : ZMod 58368571) ^ (35077 + 35077) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 35077 * (10 : ZMod 58368571) ^ 35077 := by rw [pow_add]
          _ = 26562379 := by rw [factor_3_15]; decide
      have factor_3_17 : (10 : ZMod 58368571) ^ 140309 = 31425032 := by
        calc
          (10 : ZMod 58368571) ^ 140309 = (10 : ZMod 58368571) ^ (70154 + 70154 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 70154 * (10 : ZMod 58368571) ^ 70154) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 31425032 := by rw [factor_3_16]; decide
      have factor_3_18 : (10 : ZMod 58368571) ^ 280618 = 36623414 := by
        calc
          (10 : ZMod 58368571) ^ 280618 = (10 : ZMod 58368571) ^ (140309 + 140309) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 140309 * (10 : ZMod 58368571) ^ 140309 := by rw [pow_add]
          _ = 36623414 := by rw [factor_3_17]; decide
      have factor_3_19 : (10 : ZMod 58368571) ^ 561236 = 4420851 := by
        calc
          (10 : ZMod 58368571) ^ 561236 = (10 : ZMod 58368571) ^ (280618 + 280618) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 280618 * (10 : ZMod 58368571) ^ 280618 := by rw [pow_add]
          _ = 4420851 := by rw [factor_3_18]; decide
      have factor_3_20 : (10 : ZMod 58368571) ^ 1122472 = 24724845 := by
        calc
          (10 : ZMod 58368571) ^ 1122472 = (10 : ZMod 58368571) ^ (561236 + 561236) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 561236 * (10 : ZMod 58368571) ^ 561236 := by rw [pow_add]
          _ = 24724845 := by rw [factor_3_19]; decide
      have factor_3_21 : (10 : ZMod 58368571) ^ 2244945 = 25874863 := by
        calc
          (10 : ZMod 58368571) ^ 2244945 = (10 : ZMod 58368571) ^ (1122472 + 1122472 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 1122472 * (10 : ZMod 58368571) ^ 1122472) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 25874863 := by rw [factor_3_20]; decide
      have factor_3_22 : (10 : ZMod 58368571) ^ 4489890 = 13213209 := by
        calc
          (10 : ZMod 58368571) ^ 4489890 = (10 : ZMod 58368571) ^ (2244945 + 2244945) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 2244945 * (10 : ZMod 58368571) ^ 2244945 := by rw [pow_add]
          _ = 13213209 := by rw [factor_3_21]; decide
      change (10 : ZMod 58368571) ^ 4489890 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (10 : ZMod 58368571) ^ 1 = 10 := by norm_num
      have factor_4_1 : (10 : ZMod 58368571) ^ 2 = 100 := by
        calc
          (10 : ZMod 58368571) ^ 2 = (10 : ZMod 58368571) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1 * (10 : ZMod 58368571) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_4_0]; decide
      have factor_4_2 : (10 : ZMod 58368571) ^ 5 = 100000 := by
        calc
          (10 : ZMod 58368571) ^ 5 = (10 : ZMod 58368571) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 2 * (10 : ZMod 58368571) ^ 2) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_4_1]; decide
      have factor_4_3 : (10 : ZMod 58368571) ^ 11 = 14637877 := by
        calc
          (10 : ZMod 58368571) ^ 11 = (10 : ZMod 58368571) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 5 * (10 : ZMod 58368571) ^ 5) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 14637877 := by rw [factor_4_2]; decide
      have factor_4_4 : (10 : ZMod 58368571) ^ 23 = 27563884 := by
        calc
          (10 : ZMod 58368571) ^ 23 = (10 : ZMod 58368571) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 11 * (10 : ZMod 58368571) ^ 11) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 27563884 := by rw [factor_4_3]; decide
      have factor_4_5 : (10 : ZMod 58368571) ^ 46 = 5446910 := by
        calc
          (10 : ZMod 58368571) ^ 46 = (10 : ZMod 58368571) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 23 * (10 : ZMod 58368571) ^ 23 := by rw [pow_add]
          _ = 5446910 := by rw [factor_4_4]; decide
      have factor_4_6 : (10 : ZMod 58368571) ^ 93 = 21928006 := by
        calc
          (10 : ZMod 58368571) ^ 93 = (10 : ZMod 58368571) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 46 * (10 : ZMod 58368571) ^ 46) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 21928006 := by rw [factor_4_5]; decide
      have factor_4_7 : (10 : ZMod 58368571) ^ 187 = 17874437 := by
        calc
          (10 : ZMod 58368571) ^ 187 = (10 : ZMod 58368571) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 93 * (10 : ZMod 58368571) ^ 93) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 17874437 := by rw [factor_4_6]; decide
      have factor_4_8 : (10 : ZMod 58368571) ^ 375 = 14017229 := by
        calc
          (10 : ZMod 58368571) ^ 375 = (10 : ZMod 58368571) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 187 * (10 : ZMod 58368571) ^ 187) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 14017229 := by rw [factor_4_7]; decide
      have factor_4_9 : (10 : ZMod 58368571) ^ 750 = 32026830 := by
        calc
          (10 : ZMod 58368571) ^ 750 = (10 : ZMod 58368571) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 375 * (10 : ZMod 58368571) ^ 375 := by rw [pow_add]
          _ = 32026830 := by rw [factor_4_8]; decide
      have factor_4_10 : (10 : ZMod 58368571) ^ 1500 = 54174522 := by
        calc
          (10 : ZMod 58368571) ^ 1500 = (10 : ZMod 58368571) ^ (750 + 750) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 750 * (10 : ZMod 58368571) ^ 750 := by rw [pow_add]
          _ = 54174522 := by rw [factor_4_9]; decide
      have factor_4_11 : (10 : ZMod 58368571) ^ 3000 = 36089270 := by
        calc
          (10 : ZMod 58368571) ^ 3000 = (10 : ZMod 58368571) ^ (1500 + 1500) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1500 * (10 : ZMod 58368571) ^ 1500 := by rw [pow_add]
          _ = 36089270 := by rw [factor_4_10]; decide
      have factor_4_12 : (10 : ZMod 58368571) ^ 6000 = 49736036 := by
        calc
          (10 : ZMod 58368571) ^ 6000 = (10 : ZMod 58368571) ^ (3000 + 3000) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 3000 * (10 : ZMod 58368571) ^ 3000 := by rw [pow_add]
          _ = 49736036 := by rw [factor_4_11]; decide
      have factor_4_13 : (10 : ZMod 58368571) ^ 12000 = 46716250 := by
        calc
          (10 : ZMod 58368571) ^ 12000 = (10 : ZMod 58368571) ^ (6000 + 6000) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 6000 * (10 : ZMod 58368571) ^ 6000 := by rw [pow_add]
          _ = 46716250 := by rw [factor_4_12]; decide
      have factor_4_14 : (10 : ZMod 58368571) ^ 24000 = 23406838 := by
        calc
          (10 : ZMod 58368571) ^ 24000 = (10 : ZMod 58368571) ^ (12000 + 12000) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 12000 * (10 : ZMod 58368571) ^ 12000 := by rw [pow_add]
          _ = 23406838 := by rw [factor_4_13]; decide
      have factor_4_15 : (10 : ZMod 58368571) ^ 48000 = 29721055 := by
        calc
          (10 : ZMod 58368571) ^ 48000 = (10 : ZMod 58368571) ^ (24000 + 24000) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 24000 * (10 : ZMod 58368571) ^ 24000 := by rw [pow_add]
          _ = 29721055 := by rw [factor_4_14]; decide
      have factor_4_16 : (10 : ZMod 58368571) ^ 96000 = 28821817 := by
        calc
          (10 : ZMod 58368571) ^ 96000 = (10 : ZMod 58368571) ^ (48000 + 48000) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 48000 * (10 : ZMod 58368571) ^ 48000 := by rw [pow_add]
          _ = 28821817 := by rw [factor_4_15]; decide
      have factor_4_17 : (10 : ZMod 58368571) ^ 192001 = 45154569 := by
        calc
          (10 : ZMod 58368571) ^ 192001 = (10 : ZMod 58368571) ^ (96000 + 96000 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 96000 * (10 : ZMod 58368571) ^ 96000) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 45154569 := by rw [factor_4_16]; decide
      have factor_4_18 : (10 : ZMod 58368571) ^ 384003 = 2140774 := by
        calc
          (10 : ZMod 58368571) ^ 384003 = (10 : ZMod 58368571) ^ (192001 + 192001 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 192001 * (10 : ZMod 58368571) ^ 192001) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 2140774 := by rw [factor_4_17]; decide
      have factor_4_19 : (10 : ZMod 58368571) ^ 768007 = 57404403 := by
        calc
          (10 : ZMod 58368571) ^ 768007 = (10 : ZMod 58368571) ^ (384003 + 384003 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 384003 * (10 : ZMod 58368571) ^ 384003) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 57404403 := by rw [factor_4_18]; decide
      have factor_4_20 : (10 : ZMod 58368571) ^ 1536015 = 12124783 := by
        calc
          (10 : ZMod 58368571) ^ 1536015 = (10 : ZMod 58368571) ^ (768007 + 768007 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 768007 * (10 : ZMod 58368571) ^ 768007) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 12124783 := by rw [factor_4_19]; decide
      have factor_4_21 : (10 : ZMod 58368571) ^ 3072030 = 11236513 := by
        calc
          (10 : ZMod 58368571) ^ 3072030 = (10 : ZMod 58368571) ^ (1536015 + 1536015) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 1536015 * (10 : ZMod 58368571) ^ 1536015 := by rw [pow_add]
          _ = 11236513 := by rw [factor_4_20]; decide
      change (10 : ZMod 58368571) ^ 3072030 ≠ 1
      rw [factor_4_21]
      decide
    ·
      have factor_5_0 : (10 : ZMod 58368571) ^ 1 = 10 := by norm_num
      have factor_5_1 : (10 : ZMod 58368571) ^ 3 = 1000 := by
        calc
          (10 : ZMod 58368571) ^ 3 = (10 : ZMod 58368571) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 1 * (10 : ZMod 58368571) ^ 1) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_5_0]; decide
      have factor_5_2 : (10 : ZMod 58368571) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 58368571) ^ 7 = (10 : ZMod 58368571) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 3 * (10 : ZMod 58368571) ^ 3) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_5_1]; decide
      have factor_5_3 : (10 : ZMod 58368571) ^ 14 = 45734250 := by
        calc
          (10 : ZMod 58368571) ^ 14 = (10 : ZMod 58368571) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 7 * (10 : ZMod 58368571) ^ 7 := by rw [pow_add]
          _ = 45734250 := by rw [factor_5_2]; decide
      have factor_5_4 : (10 : ZMod 58368571) ^ 28 = 49371667 := by
        calc
          (10 : ZMod 58368571) ^ 28 = (10 : ZMod 58368571) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 14 * (10 : ZMod 58368571) ^ 14 := by rw [pow_add]
          _ = 49371667 := by rw [factor_5_3]; decide
      have factor_5_5 : (10 : ZMod 58368571) ^ 57 = 22466925 := by
        calc
          (10 : ZMod 58368571) ^ 57 = (10 : ZMod 58368571) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 28 * (10 : ZMod 58368571) ^ 28) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 22466925 := by rw [factor_5_4]; decide
      have factor_5_6 : (10 : ZMod 58368571) ^ 115 = 21909898 := by
        calc
          (10 : ZMod 58368571) ^ 115 = (10 : ZMod 58368571) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 57 * (10 : ZMod 58368571) ^ 57) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 21909898 := by rw [factor_5_5]; decide
      have factor_5_7 : (10 : ZMod 58368571) ^ 231 = 34242688 := by
        calc
          (10 : ZMod 58368571) ^ 231 = (10 : ZMod 58368571) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 115 * (10 : ZMod 58368571) ^ 115) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 34242688 := by rw [factor_5_6]; decide
      have factor_5_8 : (10 : ZMod 58368571) ^ 463 = 55580249 := by
        calc
          (10 : ZMod 58368571) ^ 463 = (10 : ZMod 58368571) ^ (231 + 231 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 231 * (10 : ZMod 58368571) ^ 231) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 55580249 := by rw [factor_5_7]; decide
      have factor_5_9 : (10 : ZMod 58368571) ^ 926 = 45918484 := by
        calc
          (10 : ZMod 58368571) ^ 926 = (10 : ZMod 58368571) ^ (463 + 463) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 463 * (10 : ZMod 58368571) ^ 463 := by rw [pow_add]
          _ = 45918484 := by rw [factor_5_8]; decide
      have factor_5_10 : (10 : ZMod 58368571) ^ 1852 = 38525691 := by
        calc
          (10 : ZMod 58368571) ^ 1852 = (10 : ZMod 58368571) ^ (926 + 926) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 926 * (10 : ZMod 58368571) ^ 926 := by rw [pow_add]
          _ = 38525691 := by rw [factor_5_9]; decide
      have factor_5_11 : (10 : ZMod 58368571) ^ 3705 = 54814364 := by
        calc
          (10 : ZMod 58368571) ^ 3705 = (10 : ZMod 58368571) ^ (1852 + 1852 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = ((10 : ZMod 58368571) ^ 1852 * (10 : ZMod 58368571) ^ 1852) * (10 : ZMod 58368571) := by rw [pow_succ, pow_add]
          _ = 54814364 := by rw [factor_5_10]; decide
      have factor_5_12 : (10 : ZMod 58368571) ^ 7410 = 27788745 := by
        calc
          (10 : ZMod 58368571) ^ 7410 = (10 : ZMod 58368571) ^ (3705 + 3705) :=
            congrArg (fun n : ℕ => (10 : ZMod 58368571) ^ n) (by norm_num)
          _ = (10 : ZMod 58368571) ^ 3705 * (10 : ZMod 58368571) ^ 3705 := by rw [pow_add]
          _ = 27788745 := by rw [factor_5_11]; decide
      change (10 : ZMod 58368571) ^ 7410 ≠ 1
      rw [factor_5_12]
      decide

#print axioms prime_lucas_58368571

end TotientTailPeriodKiller
end Erdos249257
