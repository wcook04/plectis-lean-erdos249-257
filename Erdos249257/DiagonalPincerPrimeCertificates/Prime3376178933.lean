import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3376178933 : Nat.Prime 3376178933 := by
  apply lucas_primality 3376178933 (2 : ZMod 3376178933)
  ·
      have fermat_0 : (2 : ZMod 3376178933) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 3376178933) ^ 3 = 8 := by
        calc
          (2 : ZMod 3376178933) ^ 3 = (2 : ZMod 3376178933) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 1 * (2 : ZMod 3376178933) ^ 1) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 3376178933) ^ 6 = 64 := by
        calc
          (2 : ZMod 3376178933) ^ 6 = (2 : ZMod 3376178933) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 3 * (2 : ZMod 3376178933) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 3376178933) ^ 12 = 4096 := by
        calc
          (2 : ZMod 3376178933) ^ 12 = (2 : ZMod 3376178933) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 6 * (2 : ZMod 3376178933) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 3376178933) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 3376178933) ^ 25 = (2 : ZMod 3376178933) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 12 * (2 : ZMod 3376178933) ^ 12) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 3376178933) ^ 50 = 1627728985 := by
        calc
          (2 : ZMod 3376178933) ^ 50 = (2 : ZMod 3376178933) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 25 * (2 : ZMod 3376178933) ^ 25 := by rw [pow_add]
          _ = 1627728985 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 3376178933) ^ 100 = 268214824 := by
        calc
          (2 : ZMod 3376178933) ^ 100 = (2 : ZMod 3376178933) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 50 * (2 : ZMod 3376178933) ^ 50 := by rw [pow_add]
          _ = 268214824 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 3376178933) ^ 201 = 3143601867 := by
        calc
          (2 : ZMod 3376178933) ^ 201 = (2 : ZMod 3376178933) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 100 * (2 : ZMod 3376178933) ^ 100) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 3143601867 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 3376178933) ^ 402 = 2756290519 := by
        calc
          (2 : ZMod 3376178933) ^ 402 = (2 : ZMod 3376178933) ^ (201 + 201) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 201 * (2 : ZMod 3376178933) ^ 201 := by rw [pow_add]
          _ = 2756290519 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 3376178933) ^ 804 = 534521911 := by
        calc
          (2 : ZMod 3376178933) ^ 804 = (2 : ZMod 3376178933) ^ (402 + 402) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 402 * (2 : ZMod 3376178933) ^ 402 := by rw [pow_add]
          _ = 534521911 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 3376178933) ^ 1609 = 603677670 := by
        calc
          (2 : ZMod 3376178933) ^ 1609 = (2 : ZMod 3376178933) ^ (804 + 804 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 804 * (2 : ZMod 3376178933) ^ 804) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 603677670 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 3376178933) ^ 3219 = 327866190 := by
        calc
          (2 : ZMod 3376178933) ^ 3219 = (2 : ZMod 3376178933) ^ (1609 + 1609 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 1609 * (2 : ZMod 3376178933) ^ 1609) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 327866190 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 3376178933) ^ 6439 = 2294570610 := by
        calc
          (2 : ZMod 3376178933) ^ 6439 = (2 : ZMod 3376178933) ^ (3219 + 3219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 3219 * (2 : ZMod 3376178933) ^ 3219) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2294570610 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 3376178933) ^ 12879 = 2477162693 := by
        calc
          (2 : ZMod 3376178933) ^ 12879 = (2 : ZMod 3376178933) ^ (6439 + 6439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 6439 * (2 : ZMod 3376178933) ^ 6439) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2477162693 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 3376178933) ^ 25758 = 3040611997 := by
        calc
          (2 : ZMod 3376178933) ^ 25758 = (2 : ZMod 3376178933) ^ (12879 + 12879) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 12879 * (2 : ZMod 3376178933) ^ 12879 := by rw [pow_add]
          _ = 3040611997 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 3376178933) ^ 51516 = 2644171577 := by
        calc
          (2 : ZMod 3376178933) ^ 51516 = (2 : ZMod 3376178933) ^ (25758 + 25758) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 25758 * (2 : ZMod 3376178933) ^ 25758 := by rw [pow_add]
          _ = 2644171577 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 3376178933) ^ 103032 = 2915065675 := by
        calc
          (2 : ZMod 3376178933) ^ 103032 = (2 : ZMod 3376178933) ^ (51516 + 51516) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 51516 * (2 : ZMod 3376178933) ^ 51516 := by rw [pow_add]
          _ = 2915065675 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 3376178933) ^ 206065 = 1915278548 := by
        calc
          (2 : ZMod 3376178933) ^ 206065 = (2 : ZMod 3376178933) ^ (103032 + 103032 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 103032 * (2 : ZMod 3376178933) ^ 103032) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1915278548 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 3376178933) ^ 412131 = 2489696989 := by
        calc
          (2 : ZMod 3376178933) ^ 412131 = (2 : ZMod 3376178933) ^ (206065 + 206065 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 206065 * (2 : ZMod 3376178933) ^ 206065) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2489696989 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 3376178933) ^ 824262 = 1187101005 := by
        calc
          (2 : ZMod 3376178933) ^ 824262 = (2 : ZMod 3376178933) ^ (412131 + 412131) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 412131 * (2 : ZMod 3376178933) ^ 412131 := by rw [pow_add]
          _ = 1187101005 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 3376178933) ^ 1648524 = 1333269473 := by
        calc
          (2 : ZMod 3376178933) ^ 1648524 = (2 : ZMod 3376178933) ^ (824262 + 824262) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 824262 * (2 : ZMod 3376178933) ^ 824262 := by rw [pow_add]
          _ = 1333269473 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 3376178933) ^ 3297049 = 1402983322 := by
        calc
          (2 : ZMod 3376178933) ^ 3297049 = (2 : ZMod 3376178933) ^ (1648524 + 1648524 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 1648524 * (2 : ZMod 3376178933) ^ 1648524) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1402983322 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 3376178933) ^ 6594099 = 1654841218 := by
        calc
          (2 : ZMod 3376178933) ^ 6594099 = (2 : ZMod 3376178933) ^ (3297049 + 3297049 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 3297049 * (2 : ZMod 3376178933) ^ 3297049) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1654841218 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 3376178933) ^ 13188198 = 3173314427 := by
        calc
          (2 : ZMod 3376178933) ^ 13188198 = (2 : ZMod 3376178933) ^ (6594099 + 6594099) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 6594099 * (2 : ZMod 3376178933) ^ 6594099 := by rw [pow_add]
          _ = 3173314427 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 3376178933) ^ 26376397 = 829768020 := by
        calc
          (2 : ZMod 3376178933) ^ 26376397 = (2 : ZMod 3376178933) ^ (13188198 + 13188198 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 13188198 * (2 : ZMod 3376178933) ^ 13188198) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 829768020 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 3376178933) ^ 52752795 = 375605332 := by
        calc
          (2 : ZMod 3376178933) ^ 52752795 = (2 : ZMod 3376178933) ^ (26376397 + 26376397 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 26376397 * (2 : ZMod 3376178933) ^ 26376397) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 375605332 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 3376178933) ^ 105505591 = 2047730779 := by
        calc
          (2 : ZMod 3376178933) ^ 105505591 = (2 : ZMod 3376178933) ^ (52752795 + 52752795 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 52752795 * (2 : ZMod 3376178933) ^ 52752795) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2047730779 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 3376178933) ^ 211011183 = 834405003 := by
        calc
          (2 : ZMod 3376178933) ^ 211011183 = (2 : ZMod 3376178933) ^ (105505591 + 105505591 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 105505591 * (2 : ZMod 3376178933) ^ 105505591) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 834405003 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 3376178933) ^ 422022366 = 2459553356 := by
        calc
          (2 : ZMod 3376178933) ^ 422022366 = (2 : ZMod 3376178933) ^ (211011183 + 211011183) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 211011183 * (2 : ZMod 3376178933) ^ 211011183 := by rw [pow_add]
          _ = 2459553356 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 3376178933) ^ 844044733 = 1833251153 := by
        calc
          (2 : ZMod 3376178933) ^ 844044733 = (2 : ZMod 3376178933) ^ (422022366 + 422022366 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 422022366 * (2 : ZMod 3376178933) ^ 422022366) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1833251153 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 3376178933) ^ 1688089466 = 3376178932 := by
        calc
          (2 : ZMod 3376178933) ^ 1688089466 = (2 : ZMod 3376178933) ^ (844044733 + 844044733) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 844044733 * (2 : ZMod 3376178933) ^ 844044733 := by rw [pow_add]
          _ = 3376178932 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 3376178933) ^ 3376178932 = 1 := by
        calc
          (2 : ZMod 3376178933) ^ 3376178932 = (2 : ZMod 3376178933) ^ (1688089466 + 1688089466) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 1688089466 * (2 : ZMod 3376178933) ^ 1688089466 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (19, 1), (6346201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (19, 1), (6346201, 1)] : List FactorBlock).map factorBlockValue).prod = 3376178933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 3376178933) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 3376178933) ^ 3 = 8 := by
        calc
          (2 : ZMod 3376178933) ^ 3 = (2 : ZMod 3376178933) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 1 * (2 : ZMod 3376178933) ^ 1) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 3376178933) ^ 6 = 64 := by
        calc
          (2 : ZMod 3376178933) ^ 6 = (2 : ZMod 3376178933) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 3 * (2 : ZMod 3376178933) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 3376178933) ^ 12 = 4096 := by
        calc
          (2 : ZMod 3376178933) ^ 12 = (2 : ZMod 3376178933) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 6 * (2 : ZMod 3376178933) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 3376178933) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 3376178933) ^ 25 = (2 : ZMod 3376178933) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 12 * (2 : ZMod 3376178933) ^ 12) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 3376178933) ^ 50 = 1627728985 := by
        calc
          (2 : ZMod 3376178933) ^ 50 = (2 : ZMod 3376178933) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 25 * (2 : ZMod 3376178933) ^ 25 := by rw [pow_add]
          _ = 1627728985 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 3376178933) ^ 100 = 268214824 := by
        calc
          (2 : ZMod 3376178933) ^ 100 = (2 : ZMod 3376178933) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 50 * (2 : ZMod 3376178933) ^ 50 := by rw [pow_add]
          _ = 268214824 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 3376178933) ^ 201 = 3143601867 := by
        calc
          (2 : ZMod 3376178933) ^ 201 = (2 : ZMod 3376178933) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 100 * (2 : ZMod 3376178933) ^ 100) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 3143601867 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 3376178933) ^ 402 = 2756290519 := by
        calc
          (2 : ZMod 3376178933) ^ 402 = (2 : ZMod 3376178933) ^ (201 + 201) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 201 * (2 : ZMod 3376178933) ^ 201 := by rw [pow_add]
          _ = 2756290519 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 3376178933) ^ 804 = 534521911 := by
        calc
          (2 : ZMod 3376178933) ^ 804 = (2 : ZMod 3376178933) ^ (402 + 402) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 402 * (2 : ZMod 3376178933) ^ 402 := by rw [pow_add]
          _ = 534521911 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 3376178933) ^ 1609 = 603677670 := by
        calc
          (2 : ZMod 3376178933) ^ 1609 = (2 : ZMod 3376178933) ^ (804 + 804 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 804 * (2 : ZMod 3376178933) ^ 804) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 603677670 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 3376178933) ^ 3219 = 327866190 := by
        calc
          (2 : ZMod 3376178933) ^ 3219 = (2 : ZMod 3376178933) ^ (1609 + 1609 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 1609 * (2 : ZMod 3376178933) ^ 1609) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 327866190 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 3376178933) ^ 6439 = 2294570610 := by
        calc
          (2 : ZMod 3376178933) ^ 6439 = (2 : ZMod 3376178933) ^ (3219 + 3219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 3219 * (2 : ZMod 3376178933) ^ 3219) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2294570610 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 3376178933) ^ 12879 = 2477162693 := by
        calc
          (2 : ZMod 3376178933) ^ 12879 = (2 : ZMod 3376178933) ^ (6439 + 6439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 6439 * (2 : ZMod 3376178933) ^ 6439) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2477162693 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 3376178933) ^ 25758 = 3040611997 := by
        calc
          (2 : ZMod 3376178933) ^ 25758 = (2 : ZMod 3376178933) ^ (12879 + 12879) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 12879 * (2 : ZMod 3376178933) ^ 12879 := by rw [pow_add]
          _ = 3040611997 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 3376178933) ^ 51516 = 2644171577 := by
        calc
          (2 : ZMod 3376178933) ^ 51516 = (2 : ZMod 3376178933) ^ (25758 + 25758) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 25758 * (2 : ZMod 3376178933) ^ 25758 := by rw [pow_add]
          _ = 2644171577 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 3376178933) ^ 103032 = 2915065675 := by
        calc
          (2 : ZMod 3376178933) ^ 103032 = (2 : ZMod 3376178933) ^ (51516 + 51516) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 51516 * (2 : ZMod 3376178933) ^ 51516 := by rw [pow_add]
          _ = 2915065675 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 3376178933) ^ 206065 = 1915278548 := by
        calc
          (2 : ZMod 3376178933) ^ 206065 = (2 : ZMod 3376178933) ^ (103032 + 103032 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 103032 * (2 : ZMod 3376178933) ^ 103032) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1915278548 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 3376178933) ^ 412131 = 2489696989 := by
        calc
          (2 : ZMod 3376178933) ^ 412131 = (2 : ZMod 3376178933) ^ (206065 + 206065 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 206065 * (2 : ZMod 3376178933) ^ 206065) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2489696989 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 3376178933) ^ 824262 = 1187101005 := by
        calc
          (2 : ZMod 3376178933) ^ 824262 = (2 : ZMod 3376178933) ^ (412131 + 412131) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 412131 * (2 : ZMod 3376178933) ^ 412131 := by rw [pow_add]
          _ = 1187101005 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 3376178933) ^ 1648524 = 1333269473 := by
        calc
          (2 : ZMod 3376178933) ^ 1648524 = (2 : ZMod 3376178933) ^ (824262 + 824262) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 824262 * (2 : ZMod 3376178933) ^ 824262 := by rw [pow_add]
          _ = 1333269473 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 3376178933) ^ 3297049 = 1402983322 := by
        calc
          (2 : ZMod 3376178933) ^ 3297049 = (2 : ZMod 3376178933) ^ (1648524 + 1648524 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 1648524 * (2 : ZMod 3376178933) ^ 1648524) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1402983322 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 3376178933) ^ 6594099 = 1654841218 := by
        calc
          (2 : ZMod 3376178933) ^ 6594099 = (2 : ZMod 3376178933) ^ (3297049 + 3297049 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 3297049 * (2 : ZMod 3376178933) ^ 3297049) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1654841218 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 3376178933) ^ 13188198 = 3173314427 := by
        calc
          (2 : ZMod 3376178933) ^ 13188198 = (2 : ZMod 3376178933) ^ (6594099 + 6594099) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 6594099 * (2 : ZMod 3376178933) ^ 6594099 := by rw [pow_add]
          _ = 3173314427 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 3376178933) ^ 26376397 = 829768020 := by
        calc
          (2 : ZMod 3376178933) ^ 26376397 = (2 : ZMod 3376178933) ^ (13188198 + 13188198 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 13188198 * (2 : ZMod 3376178933) ^ 13188198) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 829768020 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 3376178933) ^ 52752795 = 375605332 := by
        calc
          (2 : ZMod 3376178933) ^ 52752795 = (2 : ZMod 3376178933) ^ (26376397 + 26376397 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 26376397 * (2 : ZMod 3376178933) ^ 26376397) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 375605332 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 3376178933) ^ 105505591 = 2047730779 := by
        calc
          (2 : ZMod 3376178933) ^ 105505591 = (2 : ZMod 3376178933) ^ (52752795 + 52752795 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 52752795 * (2 : ZMod 3376178933) ^ 52752795) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2047730779 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 3376178933) ^ 211011183 = 834405003 := by
        calc
          (2 : ZMod 3376178933) ^ 211011183 = (2 : ZMod 3376178933) ^ (105505591 + 105505591 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 105505591 * (2 : ZMod 3376178933) ^ 105505591) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 834405003 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 3376178933) ^ 422022366 = 2459553356 := by
        calc
          (2 : ZMod 3376178933) ^ 422022366 = (2 : ZMod 3376178933) ^ (211011183 + 211011183) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 211011183 * (2 : ZMod 3376178933) ^ 211011183 := by rw [pow_add]
          _ = 2459553356 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 3376178933) ^ 844044733 = 1833251153 := by
        calc
          (2 : ZMod 3376178933) ^ 844044733 = (2 : ZMod 3376178933) ^ (422022366 + 422022366 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 422022366 * (2 : ZMod 3376178933) ^ 422022366) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1833251153 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 3376178933) ^ 1688089466 = 3376178932 := by
        calc
          (2 : ZMod 3376178933) ^ 1688089466 = (2 : ZMod 3376178933) ^ (844044733 + 844044733) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 844044733 * (2 : ZMod 3376178933) ^ 844044733 := by rw [pow_add]
          _ = 3376178932 := by rw [factor_0_29]; decide
      change (2 : ZMod 3376178933) ^ 1688089466 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (2 : ZMod 3376178933) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 3376178933) ^ 3 = 8 := by
        calc
          (2 : ZMod 3376178933) ^ 3 = (2 : ZMod 3376178933) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 1 * (2 : ZMod 3376178933) ^ 1) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 3376178933) ^ 7 = 128 := by
        calc
          (2 : ZMod 3376178933) ^ 7 = (2 : ZMod 3376178933) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 3 * (2 : ZMod 3376178933) ^ 3) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 3376178933) ^ 14 = 16384 := by
        calc
          (2 : ZMod 3376178933) ^ 14 = (2 : ZMod 3376178933) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 7 * (2 : ZMod 3376178933) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 3376178933) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 3376178933) ^ 28 = (2 : ZMod 3376178933) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 14 * (2 : ZMod 3376178933) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 3376178933) ^ 57 = 2402395167 := by
        calc
          (2 : ZMod 3376178933) ^ 57 = (2 : ZMod 3376178933) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 28 * (2 : ZMod 3376178933) ^ 28) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2402395167 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 3376178933) ^ 114 = 2022884583 := by
        calc
          (2 : ZMod 3376178933) ^ 114 = (2 : ZMod 3376178933) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 57 * (2 : ZMod 3376178933) ^ 57 := by rw [pow_add]
          _ = 2022884583 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 3376178933) ^ 229 = 2058680207 := by
        calc
          (2 : ZMod 3376178933) ^ 229 = (2 : ZMod 3376178933) ^ (114 + 114 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 114 * (2 : ZMod 3376178933) ^ 114) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2058680207 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 3376178933) ^ 459 = 2902913335 := by
        calc
          (2 : ZMod 3376178933) ^ 459 = (2 : ZMod 3376178933) ^ (229 + 229 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 229 * (2 : ZMod 3376178933) ^ 229) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2902913335 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 3376178933) ^ 919 = 1196952386 := by
        calc
          (2 : ZMod 3376178933) ^ 919 = (2 : ZMod 3376178933) ^ (459 + 459 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 459 * (2 : ZMod 3376178933) ^ 459) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1196952386 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 3376178933) ^ 1839 = 2723948121 := by
        calc
          (2 : ZMod 3376178933) ^ 1839 = (2 : ZMod 3376178933) ^ (919 + 919 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 919 * (2 : ZMod 3376178933) ^ 919) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2723948121 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 3376178933) ^ 3679 = 1848898102 := by
        calc
          (2 : ZMod 3376178933) ^ 3679 = (2 : ZMod 3376178933) ^ (1839 + 1839 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 1839 * (2 : ZMod 3376178933) ^ 1839) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1848898102 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 3376178933) ^ 7359 = 1913297303 := by
        calc
          (2 : ZMod 3376178933) ^ 7359 = (2 : ZMod 3376178933) ^ (3679 + 3679 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 3679 * (2 : ZMod 3376178933) ^ 3679) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1913297303 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 3376178933) ^ 14718 = 1784267891 := by
        calc
          (2 : ZMod 3376178933) ^ 14718 = (2 : ZMod 3376178933) ^ (7359 + 7359) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 7359 * (2 : ZMod 3376178933) ^ 7359 := by rw [pow_add]
          _ = 1784267891 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 3376178933) ^ 29437 = 996555380 := by
        calc
          (2 : ZMod 3376178933) ^ 29437 = (2 : ZMod 3376178933) ^ (14718 + 14718 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 14718 * (2 : ZMod 3376178933) ^ 14718) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 996555380 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 3376178933) ^ 58875 = 597292402 := by
        calc
          (2 : ZMod 3376178933) ^ 58875 = (2 : ZMod 3376178933) ^ (29437 + 29437 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 29437 * (2 : ZMod 3376178933) ^ 29437) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 597292402 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 3376178933) ^ 117751 = 974806425 := by
        calc
          (2 : ZMod 3376178933) ^ 117751 = (2 : ZMod 3376178933) ^ (58875 + 58875 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 58875 * (2 : ZMod 3376178933) ^ 58875) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 974806425 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 3376178933) ^ 235503 = 2564469595 := by
        calc
          (2 : ZMod 3376178933) ^ 235503 = (2 : ZMod 3376178933) ^ (117751 + 117751 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 117751 * (2 : ZMod 3376178933) ^ 117751) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2564469595 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 3376178933) ^ 471007 = 2249598340 := by
        calc
          (2 : ZMod 3376178933) ^ 471007 = (2 : ZMod 3376178933) ^ (235503 + 235503 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 235503 * (2 : ZMod 3376178933) ^ 235503) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2249598340 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 3376178933) ^ 942014 = 2938695900 := by
        calc
          (2 : ZMod 3376178933) ^ 942014 = (2 : ZMod 3376178933) ^ (471007 + 471007) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 471007 * (2 : ZMod 3376178933) ^ 471007 := by rw [pow_add]
          _ = 2938695900 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 3376178933) ^ 1884028 = 160628143 := by
        calc
          (2 : ZMod 3376178933) ^ 1884028 = (2 : ZMod 3376178933) ^ (942014 + 942014) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 942014 * (2 : ZMod 3376178933) ^ 942014 := by rw [pow_add]
          _ = 160628143 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 3376178933) ^ 3768056 = 2819824112 := by
        calc
          (2 : ZMod 3376178933) ^ 3768056 = (2 : ZMod 3376178933) ^ (1884028 + 1884028) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 1884028 * (2 : ZMod 3376178933) ^ 1884028 := by rw [pow_add]
          _ = 2819824112 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 3376178933) ^ 7536113 = 1853268329 := by
        calc
          (2 : ZMod 3376178933) ^ 7536113 = (2 : ZMod 3376178933) ^ (3768056 + 3768056 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 3768056 * (2 : ZMod 3376178933) ^ 3768056) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1853268329 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 3376178933) ^ 15072227 = 1700141107 := by
        calc
          (2 : ZMod 3376178933) ^ 15072227 = (2 : ZMod 3376178933) ^ (7536113 + 7536113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 7536113 * (2 : ZMod 3376178933) ^ 7536113) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1700141107 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 3376178933) ^ 30144454 = 1353177780 := by
        calc
          (2 : ZMod 3376178933) ^ 30144454 = (2 : ZMod 3376178933) ^ (15072227 + 15072227) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 15072227 * (2 : ZMod 3376178933) ^ 15072227 := by rw [pow_add]
          _ = 1353177780 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 3376178933) ^ 60288909 = 2731796109 := by
        calc
          (2 : ZMod 3376178933) ^ 60288909 = (2 : ZMod 3376178933) ^ (30144454 + 30144454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 30144454 * (2 : ZMod 3376178933) ^ 30144454) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2731796109 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 3376178933) ^ 120577819 = 2073630165 := by
        calc
          (2 : ZMod 3376178933) ^ 120577819 = (2 : ZMod 3376178933) ^ (60288909 + 60288909 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 60288909 * (2 : ZMod 3376178933) ^ 60288909) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2073630165 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 3376178933) ^ 241155638 = 586889364 := by
        calc
          (2 : ZMod 3376178933) ^ 241155638 = (2 : ZMod 3376178933) ^ (120577819 + 120577819) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 120577819 * (2 : ZMod 3376178933) ^ 120577819 := by rw [pow_add]
          _ = 586889364 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 3376178933) ^ 482311276 = 360091296 := by
        calc
          (2 : ZMod 3376178933) ^ 482311276 = (2 : ZMod 3376178933) ^ (241155638 + 241155638) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 241155638 * (2 : ZMod 3376178933) ^ 241155638 := by rw [pow_add]
          _ = 360091296 := by rw [factor_1_27]; decide
      change (2 : ZMod 3376178933) ^ 482311276 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (2 : ZMod 3376178933) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 3376178933) ^ 2 = 4 := by
        calc
          (2 : ZMod 3376178933) ^ 2 = (2 : ZMod 3376178933) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 1 * (2 : ZMod 3376178933) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 3376178933) ^ 5 = 32 := by
        calc
          (2 : ZMod 3376178933) ^ 5 = (2 : ZMod 3376178933) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 2 * (2 : ZMod 3376178933) ^ 2) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 3376178933) ^ 10 = 1024 := by
        calc
          (2 : ZMod 3376178933) ^ 10 = (2 : ZMod 3376178933) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 5 * (2 : ZMod 3376178933) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 3376178933) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 3376178933) ^ 21 = (2 : ZMod 3376178933) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 10 * (2 : ZMod 3376178933) ^ 10) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 3376178933) ^ 42 = 2261540338 := by
        calc
          (2 : ZMod 3376178933) ^ 42 = (2 : ZMod 3376178933) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 21 * (2 : ZMod 3376178933) ^ 21 := by rw [pow_add]
          _ = 2261540338 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 3376178933) ^ 84 = 2736143245 := by
        calc
          (2 : ZMod 3376178933) ^ 84 = (2 : ZMod 3376178933) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 42 * (2 : ZMod 3376178933) ^ 42 := by rw [pow_add]
          _ = 2736143245 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 3376178933) ^ 169 = 1369047031 := by
        calc
          (2 : ZMod 3376178933) ^ 169 = (2 : ZMod 3376178933) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 84 * (2 : ZMod 3376178933) ^ 84) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1369047031 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 3376178933) ^ 338 = 524961093 := by
        calc
          (2 : ZMod 3376178933) ^ 338 = (2 : ZMod 3376178933) ^ (169 + 169) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 169 * (2 : ZMod 3376178933) ^ 169 := by rw [pow_add]
          _ = 524961093 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 3376178933) ^ 677 = 915678931 := by
        calc
          (2 : ZMod 3376178933) ^ 677 = (2 : ZMod 3376178933) ^ (338 + 338 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 338 * (2 : ZMod 3376178933) ^ 338) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 915678931 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 3376178933) ^ 1355 = 2367748044 := by
        calc
          (2 : ZMod 3376178933) ^ 1355 = (2 : ZMod 3376178933) ^ (677 + 677 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 677 * (2 : ZMod 3376178933) ^ 677) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 2367748044 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 3376178933) ^ 2711 = 1900728524 := by
        calc
          (2 : ZMod 3376178933) ^ 2711 = (2 : ZMod 3376178933) ^ (1355 + 1355 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 1355 * (2 : ZMod 3376178933) ^ 1355) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1900728524 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 3376178933) ^ 5422 = 2984145862 := by
        calc
          (2 : ZMod 3376178933) ^ 5422 = (2 : ZMod 3376178933) ^ (2711 + 2711) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 2711 * (2 : ZMod 3376178933) ^ 2711 := by rw [pow_add]
          _ = 2984145862 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 3376178933) ^ 10845 = 1831220652 := by
        calc
          (2 : ZMod 3376178933) ^ 10845 = (2 : ZMod 3376178933) ^ (5422 + 5422 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 5422 * (2 : ZMod 3376178933) ^ 5422) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1831220652 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 3376178933) ^ 21691 = 3014997597 := by
        calc
          (2 : ZMod 3376178933) ^ 21691 = (2 : ZMod 3376178933) ^ (10845 + 10845 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 10845 * (2 : ZMod 3376178933) ^ 10845) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 3014997597 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 3376178933) ^ 43382 = 2510367474 := by
        calc
          (2 : ZMod 3376178933) ^ 43382 = (2 : ZMod 3376178933) ^ (21691 + 21691) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 21691 * (2 : ZMod 3376178933) ^ 21691 := by rw [pow_add]
          _ = 2510367474 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 3376178933) ^ 86764 = 1664704574 := by
        calc
          (2 : ZMod 3376178933) ^ 86764 = (2 : ZMod 3376178933) ^ (43382 + 43382) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 43382 * (2 : ZMod 3376178933) ^ 43382 := by rw [pow_add]
          _ = 1664704574 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 3376178933) ^ 173528 = 2522877014 := by
        calc
          (2 : ZMod 3376178933) ^ 173528 = (2 : ZMod 3376178933) ^ (86764 + 86764) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 86764 * (2 : ZMod 3376178933) ^ 86764 := by rw [pow_add]
          _ = 2522877014 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 3376178933) ^ 347057 = 518553361 := by
        calc
          (2 : ZMod 3376178933) ^ 347057 = (2 : ZMod 3376178933) ^ (173528 + 173528 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 173528 * (2 : ZMod 3376178933) ^ 173528) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 518553361 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 3376178933) ^ 694115 = 1402690734 := by
        calc
          (2 : ZMod 3376178933) ^ 694115 = (2 : ZMod 3376178933) ^ (347057 + 347057 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 347057 * (2 : ZMod 3376178933) ^ 347057) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1402690734 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 3376178933) ^ 1388231 = 715312731 := by
        calc
          (2 : ZMod 3376178933) ^ 1388231 = (2 : ZMod 3376178933) ^ (694115 + 694115 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 694115 * (2 : ZMod 3376178933) ^ 694115) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 715312731 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 3376178933) ^ 2776462 = 2010202117 := by
        calc
          (2 : ZMod 3376178933) ^ 2776462 = (2 : ZMod 3376178933) ^ (1388231 + 1388231) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 1388231 * (2 : ZMod 3376178933) ^ 1388231 := by rw [pow_add]
          _ = 2010202117 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 3376178933) ^ 5552925 = 3344698933 := by
        calc
          (2 : ZMod 3376178933) ^ 5552925 = (2 : ZMod 3376178933) ^ (2776462 + 2776462 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 2776462 * (2 : ZMod 3376178933) ^ 2776462) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 3344698933 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 3376178933) ^ 11105851 = 1709740216 := by
        calc
          (2 : ZMod 3376178933) ^ 11105851 = (2 : ZMod 3376178933) ^ (5552925 + 5552925 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 5552925 * (2 : ZMod 3376178933) ^ 5552925) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1709740216 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 3376178933) ^ 22211703 = 725081795 := by
        calc
          (2 : ZMod 3376178933) ^ 22211703 = (2 : ZMod 3376178933) ^ (11105851 + 11105851 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 11105851 * (2 : ZMod 3376178933) ^ 11105851) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 725081795 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 3376178933) ^ 44423407 = 1102640509 := by
        calc
          (2 : ZMod 3376178933) ^ 44423407 = (2 : ZMod 3376178933) ^ (22211703 + 22211703 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 22211703 * (2 : ZMod 3376178933) ^ 22211703) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1102640509 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 3376178933) ^ 88846814 = 2313582818 := by
        calc
          (2 : ZMod 3376178933) ^ 88846814 = (2 : ZMod 3376178933) ^ (44423407 + 44423407) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 44423407 * (2 : ZMod 3376178933) ^ 44423407 := by rw [pow_add]
          _ = 2313582818 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 3376178933) ^ 177693628 = 2943977504 := by
        calc
          (2 : ZMod 3376178933) ^ 177693628 = (2 : ZMod 3376178933) ^ (88846814 + 88846814) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 88846814 * (2 : ZMod 3376178933) ^ 88846814 := by rw [pow_add]
          _ = 2943977504 := by rw [factor_2_26]; decide
      change (2 : ZMod 3376178933) ^ 177693628 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (2 : ZMod 3376178933) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 3376178933) ^ 2 = 4 := by
        calc
          (2 : ZMod 3376178933) ^ 2 = (2 : ZMod 3376178933) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 1 * (2 : ZMod 3376178933) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 3376178933) ^ 4 = 16 := by
        calc
          (2 : ZMod 3376178933) ^ 4 = (2 : ZMod 3376178933) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 2 * (2 : ZMod 3376178933) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 3376178933) ^ 8 = 256 := by
        calc
          (2 : ZMod 3376178933) ^ 8 = (2 : ZMod 3376178933) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 4 * (2 : ZMod 3376178933) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 3376178933) ^ 16 = 65536 := by
        calc
          (2 : ZMod 3376178933) ^ 16 = (2 : ZMod 3376178933) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 8 * (2 : ZMod 3376178933) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 3376178933) ^ 33 = 1837576726 := by
        calc
          (2 : ZMod 3376178933) ^ 33 = (2 : ZMod 3376178933) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 16 * (2 : ZMod 3376178933) ^ 16) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1837576726 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 3376178933) ^ 66 = 1097193892 := by
        calc
          (2 : ZMod 3376178933) ^ 66 = (2 : ZMod 3376178933) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 33 * (2 : ZMod 3376178933) ^ 33 := by rw [pow_add]
          _ = 1097193892 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 3376178933) ^ 133 = 1519312882 := by
        calc
          (2 : ZMod 3376178933) ^ 133 = (2 : ZMod 3376178933) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = ((2 : ZMod 3376178933) ^ 66 * (2 : ZMod 3376178933) ^ 66) * (2 : ZMod 3376178933) := by rw [pow_succ, pow_add]
          _ = 1519312882 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 3376178933) ^ 266 = 599965044 := by
        calc
          (2 : ZMod 3376178933) ^ 266 = (2 : ZMod 3376178933) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 133 * (2 : ZMod 3376178933) ^ 133 := by rw [pow_add]
          _ = 599965044 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 3376178933) ^ 532 = 1603155601 := by
        calc
          (2 : ZMod 3376178933) ^ 532 = (2 : ZMod 3376178933) ^ (266 + 266) :=
            congrArg (fun n : ℕ => (2 : ZMod 3376178933) ^ n) (by norm_num)
          _ = (2 : ZMod 3376178933) ^ 266 * (2 : ZMod 3376178933) ^ 266 := by rw [pow_add]
          _ = 1603155601 := by rw [factor_3_8]; decide
      change (2 : ZMod 3376178933) ^ 532 ≠ 1
      rw [factor_3_9]
      decide

#print axioms prime_lucas_3376178933

end TotientTailPeriodKiller
end Erdos249257
