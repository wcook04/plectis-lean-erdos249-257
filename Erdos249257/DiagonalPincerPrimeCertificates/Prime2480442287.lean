import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2480442287 : Nat.Prime 2480442287 := by
  apply lucas_primality 2480442287 (5 : ZMod 2480442287)
  ·
      have fermat_0 : (5 : ZMod 2480442287) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 2480442287) ^ 2 = 25 := by
        calc
          (5 : ZMod 2480442287) ^ 2 = (5 : ZMod 2480442287) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1 * (5 : ZMod 2480442287) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 2480442287) ^ 4 = 625 := by
        calc
          (5 : ZMod 2480442287) ^ 4 = (5 : ZMod 2480442287) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 2 * (5 : ZMod 2480442287) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 2480442287) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 2480442287) ^ 9 = (5 : ZMod 2480442287) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 4 * (5 : ZMod 2480442287) ^ 4) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 2480442287) ^ 18 = 2257470506 := by
        calc
          (5 : ZMod 2480442287) ^ 18 = (5 : ZMod 2480442287) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 9 * (5 : ZMod 2480442287) ^ 9 := by rw [pow_add]
          _ = 2257470506 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 2480442287) ^ 36 = 41651632 := by
        calc
          (5 : ZMod 2480442287) ^ 36 = (5 : ZMod 2480442287) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 18 * (5 : ZMod 2480442287) ^ 18 := by rw [pow_add]
          _ = 41651632 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 2480442287) ^ 73 = 2010948882 := by
        calc
          (5 : ZMod 2480442287) ^ 73 = (5 : ZMod 2480442287) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 36 * (5 : ZMod 2480442287) ^ 36) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2010948882 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 2480442287) ^ 147 = 2399695712 := by
        calc
          (5 : ZMod 2480442287) ^ 147 = (5 : ZMod 2480442287) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 73 * (5 : ZMod 2480442287) ^ 73) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2399695712 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 2480442287) ^ 295 = 685647193 := by
        calc
          (5 : ZMod 2480442287) ^ 295 = (5 : ZMod 2480442287) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 147 * (5 : ZMod 2480442287) ^ 147) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 685647193 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 2480442287) ^ 591 = 474474193 := by
        calc
          (5 : ZMod 2480442287) ^ 591 = (5 : ZMod 2480442287) ^ (295 + 295 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 295 * (5 : ZMod 2480442287) ^ 295) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 474474193 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 2480442287) ^ 1182 = 1789368826 := by
        calc
          (5 : ZMod 2480442287) ^ 1182 = (5 : ZMod 2480442287) ^ (591 + 591) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 591 * (5 : ZMod 2480442287) ^ 591 := by rw [pow_add]
          _ = 1789368826 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 2480442287) ^ 2365 = 668847061 := by
        calc
          (5 : ZMod 2480442287) ^ 2365 = (5 : ZMod 2480442287) ^ (1182 + 1182 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 1182 * (5 : ZMod 2480442287) ^ 1182) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 668847061 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 2480442287) ^ 4731 = 250279110 := by
        calc
          (5 : ZMod 2480442287) ^ 4731 = (5 : ZMod 2480442287) ^ (2365 + 2365 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 2365 * (5 : ZMod 2480442287) ^ 2365) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 250279110 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 2480442287) ^ 9462 = 1886558856 := by
        calc
          (5 : ZMod 2480442287) ^ 9462 = (5 : ZMod 2480442287) ^ (4731 + 4731) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 4731 * (5 : ZMod 2480442287) ^ 4731 := by rw [pow_add]
          _ = 1886558856 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 2480442287) ^ 18924 = 454349692 := by
        calc
          (5 : ZMod 2480442287) ^ 18924 = (5 : ZMod 2480442287) ^ (9462 + 9462) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 9462 * (5 : ZMod 2480442287) ^ 9462 := by rw [pow_add]
          _ = 454349692 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 2480442287) ^ 37848 = 1573237041 := by
        calc
          (5 : ZMod 2480442287) ^ 37848 = (5 : ZMod 2480442287) ^ (18924 + 18924) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 18924 * (5 : ZMod 2480442287) ^ 18924 := by rw [pow_add]
          _ = 1573237041 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 2480442287) ^ 75697 = 899621946 := by
        calc
          (5 : ZMod 2480442287) ^ 75697 = (5 : ZMod 2480442287) ^ (37848 + 37848 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 37848 * (5 : ZMod 2480442287) ^ 37848) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 899621946 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 2480442287) ^ 151394 = 1195724717 := by
        calc
          (5 : ZMod 2480442287) ^ 151394 = (5 : ZMod 2480442287) ^ (75697 + 75697) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 75697 * (5 : ZMod 2480442287) ^ 75697 := by rw [pow_add]
          _ = 1195724717 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 2480442287) ^ 302788 = 1390378195 := by
        calc
          (5 : ZMod 2480442287) ^ 302788 = (5 : ZMod 2480442287) ^ (151394 + 151394) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 151394 * (5 : ZMod 2480442287) ^ 151394 := by rw [pow_add]
          _ = 1390378195 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 2480442287) ^ 605576 = 2201049695 := by
        calc
          (5 : ZMod 2480442287) ^ 605576 = (5 : ZMod 2480442287) ^ (302788 + 302788) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 302788 * (5 : ZMod 2480442287) ^ 302788 := by rw [pow_add]
          _ = 2201049695 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 2480442287) ^ 1211153 = 1117548502 := by
        calc
          (5 : ZMod 2480442287) ^ 1211153 = (5 : ZMod 2480442287) ^ (605576 + 605576 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 605576 * (5 : ZMod 2480442287) ^ 605576) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1117548502 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 2480442287) ^ 2422306 = 2125236090 := by
        calc
          (5 : ZMod 2480442287) ^ 2422306 = (5 : ZMod 2480442287) ^ (1211153 + 1211153) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1211153 * (5 : ZMod 2480442287) ^ 1211153 := by rw [pow_add]
          _ = 2125236090 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 2480442287) ^ 4844613 = 2435914482 := by
        calc
          (5 : ZMod 2480442287) ^ 4844613 = (5 : ZMod 2480442287) ^ (2422306 + 2422306 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 2422306 * (5 : ZMod 2480442287) ^ 2422306) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2435914482 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 2480442287) ^ 9689227 = 1234618346 := by
        calc
          (5 : ZMod 2480442287) ^ 9689227 = (5 : ZMod 2480442287) ^ (4844613 + 4844613 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 4844613 * (5 : ZMod 2480442287) ^ 4844613) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1234618346 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 2480442287) ^ 19378455 = 2372646104 := by
        calc
          (5 : ZMod 2480442287) ^ 19378455 = (5 : ZMod 2480442287) ^ (9689227 + 9689227 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 9689227 * (5 : ZMod 2480442287) ^ 9689227) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2372646104 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 2480442287) ^ 38756910 = 707363504 := by
        calc
          (5 : ZMod 2480442287) ^ 38756910 = (5 : ZMod 2480442287) ^ (19378455 + 19378455) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 19378455 * (5 : ZMod 2480442287) ^ 19378455 := by rw [pow_add]
          _ = 707363504 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 2480442287) ^ 77513821 = 840167404 := by
        calc
          (5 : ZMod 2480442287) ^ 77513821 = (5 : ZMod 2480442287) ^ (38756910 + 38756910 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 38756910 * (5 : ZMod 2480442287) ^ 38756910) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 840167404 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 2480442287) ^ 155027642 = 2044806486 := by
        calc
          (5 : ZMod 2480442287) ^ 155027642 = (5 : ZMod 2480442287) ^ (77513821 + 77513821) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 77513821 * (5 : ZMod 2480442287) ^ 77513821 := by rw [pow_add]
          _ = 2044806486 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 2480442287) ^ 310055285 = 191435091 := by
        calc
          (5 : ZMod 2480442287) ^ 310055285 = (5 : ZMod 2480442287) ^ (155027642 + 155027642 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 155027642 * (5 : ZMod 2480442287) ^ 155027642) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 191435091 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 2480442287) ^ 620110571 = 1396026505 := by
        calc
          (5 : ZMod 2480442287) ^ 620110571 = (5 : ZMod 2480442287) ^ (310055285 + 310055285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 310055285 * (5 : ZMod 2480442287) ^ 310055285) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1396026505 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 2480442287) ^ 1240221143 = 2480442286 := by
        calc
          (5 : ZMod 2480442287) ^ 1240221143 = (5 : ZMod 2480442287) ^ (620110571 + 620110571 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 620110571 * (5 : ZMod 2480442287) ^ 620110571) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2480442286 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 2480442287) ^ 2480442286 = 1 := by
        calc
          (5 : ZMod 2480442287) ^ 2480442286 = (5 : ZMod 2480442287) ^ (1240221143 + 1240221143) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1240221143 * (5 : ZMod 2480442287) ^ 1240221143 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (19, 1), (2377, 1), (3923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (19, 1), (2377, 1), (3923, 1)] : List FactorBlock).map factorBlockValue).prod = 2480442287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 2480442287) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 2480442287) ^ 2 = 25 := by
        calc
          (5 : ZMod 2480442287) ^ 2 = (5 : ZMod 2480442287) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1 * (5 : ZMod 2480442287) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 2480442287) ^ 4 = 625 := by
        calc
          (5 : ZMod 2480442287) ^ 4 = (5 : ZMod 2480442287) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 2 * (5 : ZMod 2480442287) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 2480442287) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 2480442287) ^ 9 = (5 : ZMod 2480442287) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 4 * (5 : ZMod 2480442287) ^ 4) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 2480442287) ^ 18 = 2257470506 := by
        calc
          (5 : ZMod 2480442287) ^ 18 = (5 : ZMod 2480442287) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 9 * (5 : ZMod 2480442287) ^ 9 := by rw [pow_add]
          _ = 2257470506 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 2480442287) ^ 36 = 41651632 := by
        calc
          (5 : ZMod 2480442287) ^ 36 = (5 : ZMod 2480442287) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 18 * (5 : ZMod 2480442287) ^ 18 := by rw [pow_add]
          _ = 41651632 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 2480442287) ^ 73 = 2010948882 := by
        calc
          (5 : ZMod 2480442287) ^ 73 = (5 : ZMod 2480442287) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 36 * (5 : ZMod 2480442287) ^ 36) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2010948882 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 2480442287) ^ 147 = 2399695712 := by
        calc
          (5 : ZMod 2480442287) ^ 147 = (5 : ZMod 2480442287) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 73 * (5 : ZMod 2480442287) ^ 73) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2399695712 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 2480442287) ^ 295 = 685647193 := by
        calc
          (5 : ZMod 2480442287) ^ 295 = (5 : ZMod 2480442287) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 147 * (5 : ZMod 2480442287) ^ 147) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 685647193 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 2480442287) ^ 591 = 474474193 := by
        calc
          (5 : ZMod 2480442287) ^ 591 = (5 : ZMod 2480442287) ^ (295 + 295 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 295 * (5 : ZMod 2480442287) ^ 295) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 474474193 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 2480442287) ^ 1182 = 1789368826 := by
        calc
          (5 : ZMod 2480442287) ^ 1182 = (5 : ZMod 2480442287) ^ (591 + 591) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 591 * (5 : ZMod 2480442287) ^ 591 := by rw [pow_add]
          _ = 1789368826 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 2480442287) ^ 2365 = 668847061 := by
        calc
          (5 : ZMod 2480442287) ^ 2365 = (5 : ZMod 2480442287) ^ (1182 + 1182 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 1182 * (5 : ZMod 2480442287) ^ 1182) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 668847061 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 2480442287) ^ 4731 = 250279110 := by
        calc
          (5 : ZMod 2480442287) ^ 4731 = (5 : ZMod 2480442287) ^ (2365 + 2365 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 2365 * (5 : ZMod 2480442287) ^ 2365) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 250279110 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 2480442287) ^ 9462 = 1886558856 := by
        calc
          (5 : ZMod 2480442287) ^ 9462 = (5 : ZMod 2480442287) ^ (4731 + 4731) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 4731 * (5 : ZMod 2480442287) ^ 4731 := by rw [pow_add]
          _ = 1886558856 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 2480442287) ^ 18924 = 454349692 := by
        calc
          (5 : ZMod 2480442287) ^ 18924 = (5 : ZMod 2480442287) ^ (9462 + 9462) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 9462 * (5 : ZMod 2480442287) ^ 9462 := by rw [pow_add]
          _ = 454349692 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 2480442287) ^ 37848 = 1573237041 := by
        calc
          (5 : ZMod 2480442287) ^ 37848 = (5 : ZMod 2480442287) ^ (18924 + 18924) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 18924 * (5 : ZMod 2480442287) ^ 18924 := by rw [pow_add]
          _ = 1573237041 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 2480442287) ^ 75697 = 899621946 := by
        calc
          (5 : ZMod 2480442287) ^ 75697 = (5 : ZMod 2480442287) ^ (37848 + 37848 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 37848 * (5 : ZMod 2480442287) ^ 37848) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 899621946 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 2480442287) ^ 151394 = 1195724717 := by
        calc
          (5 : ZMod 2480442287) ^ 151394 = (5 : ZMod 2480442287) ^ (75697 + 75697) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 75697 * (5 : ZMod 2480442287) ^ 75697 := by rw [pow_add]
          _ = 1195724717 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 2480442287) ^ 302788 = 1390378195 := by
        calc
          (5 : ZMod 2480442287) ^ 302788 = (5 : ZMod 2480442287) ^ (151394 + 151394) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 151394 * (5 : ZMod 2480442287) ^ 151394 := by rw [pow_add]
          _ = 1390378195 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 2480442287) ^ 605576 = 2201049695 := by
        calc
          (5 : ZMod 2480442287) ^ 605576 = (5 : ZMod 2480442287) ^ (302788 + 302788) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 302788 * (5 : ZMod 2480442287) ^ 302788 := by rw [pow_add]
          _ = 2201049695 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 2480442287) ^ 1211153 = 1117548502 := by
        calc
          (5 : ZMod 2480442287) ^ 1211153 = (5 : ZMod 2480442287) ^ (605576 + 605576 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 605576 * (5 : ZMod 2480442287) ^ 605576) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1117548502 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 2480442287) ^ 2422306 = 2125236090 := by
        calc
          (5 : ZMod 2480442287) ^ 2422306 = (5 : ZMod 2480442287) ^ (1211153 + 1211153) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1211153 * (5 : ZMod 2480442287) ^ 1211153 := by rw [pow_add]
          _ = 2125236090 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 2480442287) ^ 4844613 = 2435914482 := by
        calc
          (5 : ZMod 2480442287) ^ 4844613 = (5 : ZMod 2480442287) ^ (2422306 + 2422306 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 2422306 * (5 : ZMod 2480442287) ^ 2422306) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2435914482 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 2480442287) ^ 9689227 = 1234618346 := by
        calc
          (5 : ZMod 2480442287) ^ 9689227 = (5 : ZMod 2480442287) ^ (4844613 + 4844613 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 4844613 * (5 : ZMod 2480442287) ^ 4844613) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1234618346 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 2480442287) ^ 19378455 = 2372646104 := by
        calc
          (5 : ZMod 2480442287) ^ 19378455 = (5 : ZMod 2480442287) ^ (9689227 + 9689227 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 9689227 * (5 : ZMod 2480442287) ^ 9689227) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2372646104 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 2480442287) ^ 38756910 = 707363504 := by
        calc
          (5 : ZMod 2480442287) ^ 38756910 = (5 : ZMod 2480442287) ^ (19378455 + 19378455) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 19378455 * (5 : ZMod 2480442287) ^ 19378455 := by rw [pow_add]
          _ = 707363504 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 2480442287) ^ 77513821 = 840167404 := by
        calc
          (5 : ZMod 2480442287) ^ 77513821 = (5 : ZMod 2480442287) ^ (38756910 + 38756910 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 38756910 * (5 : ZMod 2480442287) ^ 38756910) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 840167404 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 2480442287) ^ 155027642 = 2044806486 := by
        calc
          (5 : ZMod 2480442287) ^ 155027642 = (5 : ZMod 2480442287) ^ (77513821 + 77513821) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 77513821 * (5 : ZMod 2480442287) ^ 77513821 := by rw [pow_add]
          _ = 2044806486 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 2480442287) ^ 310055285 = 191435091 := by
        calc
          (5 : ZMod 2480442287) ^ 310055285 = (5 : ZMod 2480442287) ^ (155027642 + 155027642 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 155027642 * (5 : ZMod 2480442287) ^ 155027642) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 191435091 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 2480442287) ^ 620110571 = 1396026505 := by
        calc
          (5 : ZMod 2480442287) ^ 620110571 = (5 : ZMod 2480442287) ^ (310055285 + 310055285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 310055285 * (5 : ZMod 2480442287) ^ 310055285) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1396026505 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 2480442287) ^ 1240221143 = 2480442286 := by
        calc
          (5 : ZMod 2480442287) ^ 1240221143 = (5 : ZMod 2480442287) ^ (620110571 + 620110571 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 620110571 * (5 : ZMod 2480442287) ^ 620110571) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2480442286 := by rw [factor_0_29]; decide
      change (5 : ZMod 2480442287) ^ 1240221143 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (5 : ZMod 2480442287) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 2480442287) ^ 2 = 25 := by
        calc
          (5 : ZMod 2480442287) ^ 2 = (5 : ZMod 2480442287) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1 * (5 : ZMod 2480442287) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 2480442287) ^ 5 = 3125 := by
        calc
          (5 : ZMod 2480442287) ^ 5 = (5 : ZMod 2480442287) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 2 * (5 : ZMod 2480442287) ^ 2) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 2480442287) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 2480442287) ^ 10 = (5 : ZMod 2480442287) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 5 * (5 : ZMod 2480442287) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 2480442287) ^ 21 = 1893834819 := by
        calc
          (5 : ZMod 2480442287) ^ 21 = (5 : ZMod 2480442287) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 10 * (5 : ZMod 2480442287) ^ 10) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1893834819 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 2480442287) ^ 42 = 930870806 := by
        calc
          (5 : ZMod 2480442287) ^ 42 = (5 : ZMod 2480442287) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 21 * (5 : ZMod 2480442287) ^ 21 := by rw [pow_add]
          _ = 930870806 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 2480442287) ^ 84 = 592455640 := by
        calc
          (5 : ZMod 2480442287) ^ 84 = (5 : ZMod 2480442287) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 42 * (5 : ZMod 2480442287) ^ 42 := by rw [pow_add]
          _ = 592455640 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 2480442287) ^ 168 = 634774091 := by
        calc
          (5 : ZMod 2480442287) ^ 168 = (5 : ZMod 2480442287) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 84 * (5 : ZMod 2480442287) ^ 84 := by rw [pow_add]
          _ = 634774091 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 2480442287) ^ 337 = 379322838 := by
        calc
          (5 : ZMod 2480442287) ^ 337 = (5 : ZMod 2480442287) ^ (168 + 168 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 168 * (5 : ZMod 2480442287) ^ 168) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 379322838 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 2480442287) ^ 675 = 1296000679 := by
        calc
          (5 : ZMod 2480442287) ^ 675 = (5 : ZMod 2480442287) ^ (337 + 337 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 337 * (5 : ZMod 2480442287) ^ 337) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1296000679 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 2480442287) ^ 1351 = 157213087 := by
        calc
          (5 : ZMod 2480442287) ^ 1351 = (5 : ZMod 2480442287) ^ (675 + 675 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 675 * (5 : ZMod 2480442287) ^ 675) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 157213087 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 2480442287) ^ 2703 = 1504273129 := by
        calc
          (5 : ZMod 2480442287) ^ 2703 = (5 : ZMod 2480442287) ^ (1351 + 1351 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 1351 * (5 : ZMod 2480442287) ^ 1351) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1504273129 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 2480442287) ^ 5406 = 2417037135 := by
        calc
          (5 : ZMod 2480442287) ^ 5406 = (5 : ZMod 2480442287) ^ (2703 + 2703) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 2703 * (5 : ZMod 2480442287) ^ 2703 := by rw [pow_add]
          _ = 2417037135 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 2480442287) ^ 10813 = 1245152319 := by
        calc
          (5 : ZMod 2480442287) ^ 10813 = (5 : ZMod 2480442287) ^ (5406 + 5406 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 5406 * (5 : ZMod 2480442287) ^ 5406) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1245152319 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 2480442287) ^ 21627 = 1720029981 := by
        calc
          (5 : ZMod 2480442287) ^ 21627 = (5 : ZMod 2480442287) ^ (10813 + 10813 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 10813 * (5 : ZMod 2480442287) ^ 10813) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1720029981 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 2480442287) ^ 43255 = 584949740 := by
        calc
          (5 : ZMod 2480442287) ^ 43255 = (5 : ZMod 2480442287) ^ (21627 + 21627 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 21627 * (5 : ZMod 2480442287) ^ 21627) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 584949740 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 2480442287) ^ 86510 = 2043231207 := by
        calc
          (5 : ZMod 2480442287) ^ 86510 = (5 : ZMod 2480442287) ^ (43255 + 43255) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 43255 * (5 : ZMod 2480442287) ^ 43255 := by rw [pow_add]
          _ = 2043231207 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 2480442287) ^ 173021 = 1381695267 := by
        calc
          (5 : ZMod 2480442287) ^ 173021 = (5 : ZMod 2480442287) ^ (86510 + 86510 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 86510 * (5 : ZMod 2480442287) ^ 86510) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1381695267 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 2480442287) ^ 346043 = 1558821786 := by
        calc
          (5 : ZMod 2480442287) ^ 346043 = (5 : ZMod 2480442287) ^ (173021 + 173021 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 173021 * (5 : ZMod 2480442287) ^ 173021) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1558821786 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 2480442287) ^ 692087 = 1199541314 := by
        calc
          (5 : ZMod 2480442287) ^ 692087 = (5 : ZMod 2480442287) ^ (346043 + 346043 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 346043 * (5 : ZMod 2480442287) ^ 346043) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1199541314 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 2480442287) ^ 1384175 = 1242977332 := by
        calc
          (5 : ZMod 2480442287) ^ 1384175 = (5 : ZMod 2480442287) ^ (692087 + 692087 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 692087 * (5 : ZMod 2480442287) ^ 692087) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1242977332 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 2480442287) ^ 2768350 = 2080875310 := by
        calc
          (5 : ZMod 2480442287) ^ 2768350 = (5 : ZMod 2480442287) ^ (1384175 + 1384175) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1384175 * (5 : ZMod 2480442287) ^ 1384175 := by rw [pow_add]
          _ = 2080875310 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 2480442287) ^ 5536701 = 520591097 := by
        calc
          (5 : ZMod 2480442287) ^ 5536701 = (5 : ZMod 2480442287) ^ (2768350 + 2768350 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 2768350 * (5 : ZMod 2480442287) ^ 2768350) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 520591097 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 2480442287) ^ 11073403 = 2477875951 := by
        calc
          (5 : ZMod 2480442287) ^ 11073403 = (5 : ZMod 2480442287) ^ (5536701 + 5536701 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 5536701 * (5 : ZMod 2480442287) ^ 5536701) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2477875951 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 2480442287) ^ 22146806 = 506192911 := by
        calc
          (5 : ZMod 2480442287) ^ 22146806 = (5 : ZMod 2480442287) ^ (11073403 + 11073403) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 11073403 * (5 : ZMod 2480442287) ^ 11073403 := by rw [pow_add]
          _ = 506192911 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 2480442287) ^ 44293612 = 2299143963 := by
        calc
          (5 : ZMod 2480442287) ^ 44293612 = (5 : ZMod 2480442287) ^ (22146806 + 22146806) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 22146806 * (5 : ZMod 2480442287) ^ 22146806 := by rw [pow_add]
          _ = 2299143963 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 2480442287) ^ 88587224 = 2368370450 := by
        calc
          (5 : ZMod 2480442287) ^ 88587224 = (5 : ZMod 2480442287) ^ (44293612 + 44293612) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 44293612 * (5 : ZMod 2480442287) ^ 44293612 := by rw [pow_add]
          _ = 2368370450 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 2480442287) ^ 177174449 = 505512225 := by
        calc
          (5 : ZMod 2480442287) ^ 177174449 = (5 : ZMod 2480442287) ^ (88587224 + 88587224 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 88587224 * (5 : ZMod 2480442287) ^ 88587224) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 505512225 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 2480442287) ^ 354348898 = 1410407338 := by
        calc
          (5 : ZMod 2480442287) ^ 354348898 = (5 : ZMod 2480442287) ^ (177174449 + 177174449) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 177174449 * (5 : ZMod 2480442287) ^ 177174449 := by rw [pow_add]
          _ = 1410407338 := by rw [factor_1_27]; decide
      change (5 : ZMod 2480442287) ^ 354348898 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (5 : ZMod 2480442287) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 2480442287) ^ 3 = 125 := by
        calc
          (5 : ZMod 2480442287) ^ 3 = (5 : ZMod 2480442287) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 1 * (5 : ZMod 2480442287) ^ 1) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 2480442287) ^ 7 = 78125 := by
        calc
          (5 : ZMod 2480442287) ^ 7 = (5 : ZMod 2480442287) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 3 * (5 : ZMod 2480442287) ^ 3) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 2480442287) ^ 15 = 752270681 := by
        calc
          (5 : ZMod 2480442287) ^ 15 = (5 : ZMod 2480442287) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 7 * (5 : ZMod 2480442287) ^ 7) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 752270681 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 2480442287) ^ 31 = 348465861 := by
        calc
          (5 : ZMod 2480442287) ^ 31 = (5 : ZMod 2480442287) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 15 * (5 : ZMod 2480442287) ^ 15) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 348465861 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 2480442287) ^ 62 = 1527219149 := by
        calc
          (5 : ZMod 2480442287) ^ 62 = (5 : ZMod 2480442287) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 31 * (5 : ZMod 2480442287) ^ 31 := by rw [pow_add]
          _ = 1527219149 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 2480442287) ^ 124 = 2231177988 := by
        calc
          (5 : ZMod 2480442287) ^ 124 = (5 : ZMod 2480442287) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 62 * (5 : ZMod 2480442287) ^ 62 := by rw [pow_add]
          _ = 2231177988 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 2480442287) ^ 249 = 662668910 := by
        calc
          (5 : ZMod 2480442287) ^ 249 = (5 : ZMod 2480442287) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 124 * (5 : ZMod 2480442287) ^ 124) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 662668910 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 2480442287) ^ 498 = 792988517 := by
        calc
          (5 : ZMod 2480442287) ^ 498 = (5 : ZMod 2480442287) ^ (249 + 249) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 249 * (5 : ZMod 2480442287) ^ 249 := by rw [pow_add]
          _ = 792988517 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 2480442287) ^ 996 = 724547246 := by
        calc
          (5 : ZMod 2480442287) ^ 996 = (5 : ZMod 2480442287) ^ (498 + 498) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 498 * (5 : ZMod 2480442287) ^ 498 := by rw [pow_add]
          _ = 724547246 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 2480442287) ^ 1992 = 895935847 := by
        calc
          (5 : ZMod 2480442287) ^ 1992 = (5 : ZMod 2480442287) ^ (996 + 996) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 996 * (5 : ZMod 2480442287) ^ 996 := by rw [pow_add]
          _ = 895935847 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 2480442287) ^ 3984 = 1251983902 := by
        calc
          (5 : ZMod 2480442287) ^ 3984 = (5 : ZMod 2480442287) ^ (1992 + 1992) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1992 * (5 : ZMod 2480442287) ^ 1992 := by rw [pow_add]
          _ = 1251983902 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 2480442287) ^ 7968 = 1556428747 := by
        calc
          (5 : ZMod 2480442287) ^ 7968 = (5 : ZMod 2480442287) ^ (3984 + 3984) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 3984 * (5 : ZMod 2480442287) ^ 3984 := by rw [pow_add]
          _ = 1556428747 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 2480442287) ^ 15936 = 431782034 := by
        calc
          (5 : ZMod 2480442287) ^ 15936 = (5 : ZMod 2480442287) ^ (7968 + 7968) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 7968 * (5 : ZMod 2480442287) ^ 7968 := by rw [pow_add]
          _ = 431782034 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 2480442287) ^ 31872 = 2381419926 := by
        calc
          (5 : ZMod 2480442287) ^ 31872 = (5 : ZMod 2480442287) ^ (15936 + 15936) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 15936 * (5 : ZMod 2480442287) ^ 15936 := by rw [pow_add]
          _ = 2381419926 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 2480442287) ^ 63744 = 1495043769 := by
        calc
          (5 : ZMod 2480442287) ^ 63744 = (5 : ZMod 2480442287) ^ (31872 + 31872) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 31872 * (5 : ZMod 2480442287) ^ 31872 := by rw [pow_add]
          _ = 1495043769 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 2480442287) ^ 127489 = 704330800 := by
        calc
          (5 : ZMod 2480442287) ^ 127489 = (5 : ZMod 2480442287) ^ (63744 + 63744 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 63744 * (5 : ZMod 2480442287) ^ 63744) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 704330800 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 2480442287) ^ 254979 = 171021629 := by
        calc
          (5 : ZMod 2480442287) ^ 254979 = (5 : ZMod 2480442287) ^ (127489 + 127489 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 127489 * (5 : ZMod 2480442287) ^ 127489) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 171021629 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 2480442287) ^ 509959 = 2119738169 := by
        calc
          (5 : ZMod 2480442287) ^ 509959 = (5 : ZMod 2480442287) ^ (254979 + 254979 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 254979 * (5 : ZMod 2480442287) ^ 254979) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2119738169 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 2480442287) ^ 1019918 = 435749927 := by
        calc
          (5 : ZMod 2480442287) ^ 1019918 = (5 : ZMod 2480442287) ^ (509959 + 509959) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 509959 * (5 : ZMod 2480442287) ^ 509959 := by rw [pow_add]
          _ = 435749927 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 2480442287) ^ 2039837 = 2127224850 := by
        calc
          (5 : ZMod 2480442287) ^ 2039837 = (5 : ZMod 2480442287) ^ (1019918 + 1019918 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 1019918 * (5 : ZMod 2480442287) ^ 1019918) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2127224850 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 2480442287) ^ 4079674 = 1662872025 := by
        calc
          (5 : ZMod 2480442287) ^ 4079674 = (5 : ZMod 2480442287) ^ (2039837 + 2039837) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 2039837 * (5 : ZMod 2480442287) ^ 2039837 := by rw [pow_add]
          _ = 1662872025 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 2480442287) ^ 8159349 = 727398274 := by
        calc
          (5 : ZMod 2480442287) ^ 8159349 = (5 : ZMod 2480442287) ^ (4079674 + 4079674 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 4079674 * (5 : ZMod 2480442287) ^ 4079674) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 727398274 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 2480442287) ^ 16318699 = 139912150 := by
        calc
          (5 : ZMod 2480442287) ^ 16318699 = (5 : ZMod 2480442287) ^ (8159349 + 8159349 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 8159349 * (5 : ZMod 2480442287) ^ 8159349) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 139912150 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 2480442287) ^ 32637398 = 2271962626 := by
        calc
          (5 : ZMod 2480442287) ^ 32637398 = (5 : ZMod 2480442287) ^ (16318699 + 16318699) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 16318699 * (5 : ZMod 2480442287) ^ 16318699 := by rw [pow_add]
          _ = 2271962626 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 2480442287) ^ 65274797 = 1508538538 := by
        calc
          (5 : ZMod 2480442287) ^ 65274797 = (5 : ZMod 2480442287) ^ (32637398 + 32637398 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 32637398 * (5 : ZMod 2480442287) ^ 32637398) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1508538538 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 2480442287) ^ 130549594 = 100449091 := by
        calc
          (5 : ZMod 2480442287) ^ 130549594 = (5 : ZMod 2480442287) ^ (65274797 + 65274797) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 65274797 * (5 : ZMod 2480442287) ^ 65274797 := by rw [pow_add]
          _ = 100449091 := by rw [factor_2_25]; decide
      change (5 : ZMod 2480442287) ^ 130549594 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (5 : ZMod 2480442287) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 2480442287) ^ 3 = 125 := by
        calc
          (5 : ZMod 2480442287) ^ 3 = (5 : ZMod 2480442287) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 1 * (5 : ZMod 2480442287) ^ 1) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 2480442287) ^ 7 = 78125 := by
        calc
          (5 : ZMod 2480442287) ^ 7 = (5 : ZMod 2480442287) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 3 * (5 : ZMod 2480442287) ^ 3) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 2480442287) ^ 15 = 752270681 := by
        calc
          (5 : ZMod 2480442287) ^ 15 = (5 : ZMod 2480442287) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 7 * (5 : ZMod 2480442287) ^ 7) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 752270681 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 2480442287) ^ 31 = 348465861 := by
        calc
          (5 : ZMod 2480442287) ^ 31 = (5 : ZMod 2480442287) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 15 * (5 : ZMod 2480442287) ^ 15) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 348465861 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 2480442287) ^ 63 = 194768884 := by
        calc
          (5 : ZMod 2480442287) ^ 63 = (5 : ZMod 2480442287) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 31 * (5 : ZMod 2480442287) ^ 31) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 194768884 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 2480442287) ^ 127 = 1087712356 := by
        calc
          (5 : ZMod 2480442287) ^ 127 = (5 : ZMod 2480442287) ^ (63 + 63 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 63 * (5 : ZMod 2480442287) ^ 63) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1087712356 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 2480442287) ^ 254 = 2151476392 := by
        calc
          (5 : ZMod 2480442287) ^ 254 = (5 : ZMod 2480442287) ^ (127 + 127) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 127 * (5 : ZMod 2480442287) ^ 127 := by rw [pow_add]
          _ = 2151476392 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 2480442287) ^ 509 = 1773728113 := by
        calc
          (5 : ZMod 2480442287) ^ 509 = (5 : ZMod 2480442287) ^ (254 + 254 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 254 * (5 : ZMod 2480442287) ^ 254) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1773728113 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 2480442287) ^ 1019 = 1449704986 := by
        calc
          (5 : ZMod 2480442287) ^ 1019 = (5 : ZMod 2480442287) ^ (509 + 509 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 509 * (5 : ZMod 2480442287) ^ 509) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1449704986 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 2480442287) ^ 2038 = 1957297926 := by
        calc
          (5 : ZMod 2480442287) ^ 2038 = (5 : ZMod 2480442287) ^ (1019 + 1019) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1019 * (5 : ZMod 2480442287) ^ 1019 := by rw [pow_add]
          _ = 1957297926 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 2480442287) ^ 4076 = 1034764531 := by
        calc
          (5 : ZMod 2480442287) ^ 4076 = (5 : ZMod 2480442287) ^ (2038 + 2038) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 2038 * (5 : ZMod 2480442287) ^ 2038 := by rw [pow_add]
          _ = 1034764531 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 2480442287) ^ 8152 = 394806454 := by
        calc
          (5 : ZMod 2480442287) ^ 8152 = (5 : ZMod 2480442287) ^ (4076 + 4076) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 4076 * (5 : ZMod 2480442287) ^ 4076 := by rw [pow_add]
          _ = 394806454 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 2480442287) ^ 16304 = 1801522096 := by
        calc
          (5 : ZMod 2480442287) ^ 16304 = (5 : ZMod 2480442287) ^ (8152 + 8152) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 8152 * (5 : ZMod 2480442287) ^ 8152 := by rw [pow_add]
          _ = 1801522096 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 2480442287) ^ 32609 = 1272250190 := by
        calc
          (5 : ZMod 2480442287) ^ 32609 = (5 : ZMod 2480442287) ^ (16304 + 16304 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 16304 * (5 : ZMod 2480442287) ^ 16304) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1272250190 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 2480442287) ^ 65219 = 554645944 := by
        calc
          (5 : ZMod 2480442287) ^ 65219 = (5 : ZMod 2480442287) ^ (32609 + 32609 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 32609 * (5 : ZMod 2480442287) ^ 32609) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 554645944 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 2480442287) ^ 130439 = 1210914086 := by
        calc
          (5 : ZMod 2480442287) ^ 130439 = (5 : ZMod 2480442287) ^ (65219 + 65219 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 65219 * (5 : ZMod 2480442287) ^ 65219) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1210914086 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 2480442287) ^ 260879 = 2170079 := by
        calc
          (5 : ZMod 2480442287) ^ 260879 = (5 : ZMod 2480442287) ^ (130439 + 130439 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 130439 * (5 : ZMod 2480442287) ^ 130439) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2170079 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 2480442287) ^ 521759 = 1856143001 := by
        calc
          (5 : ZMod 2480442287) ^ 521759 = (5 : ZMod 2480442287) ^ (260879 + 260879 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 260879 * (5 : ZMod 2480442287) ^ 260879) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1856143001 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 2480442287) ^ 1043518 = 1313799845 := by
        calc
          (5 : ZMod 2480442287) ^ 1043518 = (5 : ZMod 2480442287) ^ (521759 + 521759) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 521759 * (5 : ZMod 2480442287) ^ 521759 := by rw [pow_add]
          _ = 1313799845 := by rw [factor_3_18]; decide
      change (5 : ZMod 2480442287) ^ 1043518 ≠ 1
      rw [factor_3_19]
      decide
    ·
      have factor_4_0 : (5 : ZMod 2480442287) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 2480442287) ^ 2 = 25 := by
        calc
          (5 : ZMod 2480442287) ^ 2 = (5 : ZMod 2480442287) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 1 * (5 : ZMod 2480442287) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 2480442287) ^ 4 = 625 := by
        calc
          (5 : ZMod 2480442287) ^ 4 = (5 : ZMod 2480442287) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 2 * (5 : ZMod 2480442287) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 2480442287) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 2480442287) ^ 9 = (5 : ZMod 2480442287) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 4 * (5 : ZMod 2480442287) ^ 4) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 2480442287) ^ 19 = 1365583382 := by
        calc
          (5 : ZMod 2480442287) ^ 19 = (5 : ZMod 2480442287) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 9 * (5 : ZMod 2480442287) ^ 9) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1365583382 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 2480442287) ^ 38 = 1041290800 := by
        calc
          (5 : ZMod 2480442287) ^ 38 = (5 : ZMod 2480442287) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 19 * (5 : ZMod 2480442287) ^ 19 := by rw [pow_add]
          _ = 1041290800 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 2480442287) ^ 77 = 1739254028 := by
        calc
          (5 : ZMod 2480442287) ^ 77 = (5 : ZMod 2480442287) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 38 * (5 : ZMod 2480442287) ^ 38) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1739254028 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 2480442287) ^ 154 = 1919006253 := by
        calc
          (5 : ZMod 2480442287) ^ 154 = (5 : ZMod 2480442287) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 77 * (5 : ZMod 2480442287) ^ 77 := by rw [pow_add]
          _ = 1919006253 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 2480442287) ^ 308 = 1428269612 := by
        calc
          (5 : ZMod 2480442287) ^ 308 = (5 : ZMod 2480442287) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 154 * (5 : ZMod 2480442287) ^ 154 := by rw [pow_add]
          _ = 1428269612 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 2480442287) ^ 617 = 480367620 := by
        calc
          (5 : ZMod 2480442287) ^ 617 = (5 : ZMod 2480442287) ^ (308 + 308 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 308 * (5 : ZMod 2480442287) ^ 308) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 480367620 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 2480442287) ^ 1234 = 2190237409 := by
        calc
          (5 : ZMod 2480442287) ^ 1234 = (5 : ZMod 2480442287) ^ (617 + 617) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 617 * (5 : ZMod 2480442287) ^ 617 := by rw [pow_add]
          _ = 2190237409 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 2480442287) ^ 2469 = 53109775 := by
        calc
          (5 : ZMod 2480442287) ^ 2469 = (5 : ZMod 2480442287) ^ (1234 + 1234 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 1234 * (5 : ZMod 2480442287) ^ 1234) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 53109775 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 2480442287) ^ 4939 = 1777943413 := by
        calc
          (5 : ZMod 2480442287) ^ 4939 = (5 : ZMod 2480442287) ^ (2469 + 2469 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 2469 * (5 : ZMod 2480442287) ^ 2469) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1777943413 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 2480442287) ^ 9879 = 2430778655 := by
        calc
          (5 : ZMod 2480442287) ^ 9879 = (5 : ZMod 2480442287) ^ (4939 + 4939 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 4939 * (5 : ZMod 2480442287) ^ 4939) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 2430778655 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 2480442287) ^ 19758 = 1426949521 := by
        calc
          (5 : ZMod 2480442287) ^ 19758 = (5 : ZMod 2480442287) ^ (9879 + 9879) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 9879 * (5 : ZMod 2480442287) ^ 9879 := by rw [pow_add]
          _ = 1426949521 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 2480442287) ^ 39517 = 737724337 := by
        calc
          (5 : ZMod 2480442287) ^ 39517 = (5 : ZMod 2480442287) ^ (19758 + 19758 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 19758 * (5 : ZMod 2480442287) ^ 19758) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 737724337 := by rw [factor_4_14]; decide
      have factor_4_16 : (5 : ZMod 2480442287) ^ 79035 = 825910864 := by
        calc
          (5 : ZMod 2480442287) ^ 79035 = (5 : ZMod 2480442287) ^ (39517 + 39517 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 39517 * (5 : ZMod 2480442287) ^ 39517) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 825910864 := by rw [factor_4_15]; decide
      have factor_4_17 : (5 : ZMod 2480442287) ^ 158070 = 37535945 := by
        calc
          (5 : ZMod 2480442287) ^ 158070 = (5 : ZMod 2480442287) ^ (79035 + 79035) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 79035 * (5 : ZMod 2480442287) ^ 79035 := by rw [pow_add]
          _ = 37535945 := by rw [factor_4_16]; decide
      have factor_4_18 : (5 : ZMod 2480442287) ^ 316141 = 1930598981 := by
        calc
          (5 : ZMod 2480442287) ^ 316141 = (5 : ZMod 2480442287) ^ (158070 + 158070 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = ((5 : ZMod 2480442287) ^ 158070 * (5 : ZMod 2480442287) ^ 158070) * (5 : ZMod 2480442287) := by rw [pow_succ, pow_add]
          _ = 1930598981 := by rw [factor_4_17]; decide
      have factor_4_19 : (5 : ZMod 2480442287) ^ 632282 = 2229102037 := by
        calc
          (5 : ZMod 2480442287) ^ 632282 = (5 : ZMod 2480442287) ^ (316141 + 316141) :=
            congrArg (fun n : ℕ => (5 : ZMod 2480442287) ^ n) (by norm_num)
          _ = (5 : ZMod 2480442287) ^ 316141 * (5 : ZMod 2480442287) ^ 316141 := by rw [pow_add]
          _ = 2229102037 := by rw [factor_4_18]; decide
      change (5 : ZMod 2480442287) ^ 632282 ≠ 1
      rw [factor_4_19]
      decide

#print axioms prime_lucas_2480442287

end TotientTailPeriodKiller
end Erdos249257
