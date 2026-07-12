import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_30218149543 : Nat.Prime 30218149543 := by
  apply lucas_primality 30218149543 (6 : ZMod 30218149543)
  ·
      have fermat_0 : (6 : ZMod 30218149543) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 30218149543) ^ 3 = 216 := by
        calc
          (6 : ZMod 30218149543) ^ 3 = (6 : ZMod 30218149543) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 1 * (6 : ZMod 30218149543) ^ 1) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 30218149543) ^ 7 = 279936 := by
        calc
          (6 : ZMod 30218149543) ^ 7 = (6 : ZMod 30218149543) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 3 * (6 : ZMod 30218149543) ^ 3) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 30218149543) ^ 14 = 17927865010 := by
        calc
          (6 : ZMod 30218149543) ^ 14 = (6 : ZMod 30218149543) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 7 * (6 : ZMod 30218149543) ^ 7 := by rw [pow_add]
          _ = 17927865010 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 30218149543) ^ 28 = 14273128925 := by
        calc
          (6 : ZMod 30218149543) ^ 28 = (6 : ZMod 30218149543) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 14 * (6 : ZMod 30218149543) ^ 14 := by rw [pow_add]
          _ = 14273128925 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 30218149543) ^ 56 = 30210176183 := by
        calc
          (6 : ZMod 30218149543) ^ 56 = (6 : ZMod 30218149543) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 28 * (6 : ZMod 30218149543) ^ 28 := by rw [pow_add]
          _ = 30210176183 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 30218149543) ^ 112 = 25701200671 := by
        calc
          (6 : ZMod 30218149543) ^ 112 = (6 : ZMod 30218149543) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 56 * (6 : ZMod 30218149543) ^ 56 := by rw [pow_add]
          _ = 25701200671 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 30218149543) ^ 225 = 2956966935 := by
        calc
          (6 : ZMod 30218149543) ^ 225 = (6 : ZMod 30218149543) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 112 * (6 : ZMod 30218149543) ^ 112) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 2956966935 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 30218149543) ^ 450 = 4268476360 := by
        calc
          (6 : ZMod 30218149543) ^ 450 = (6 : ZMod 30218149543) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 225 * (6 : ZMod 30218149543) ^ 225 := by rw [pow_add]
          _ = 4268476360 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 30218149543) ^ 900 = 10119889361 := by
        calc
          (6 : ZMod 30218149543) ^ 900 = (6 : ZMod 30218149543) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 450 * (6 : ZMod 30218149543) ^ 450 := by rw [pow_add]
          _ = 10119889361 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 30218149543) ^ 1801 = 27218159375 := by
        calc
          (6 : ZMod 30218149543) ^ 1801 = (6 : ZMod 30218149543) ^ (900 + 900 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 900 * (6 : ZMod 30218149543) ^ 900) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 27218159375 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 30218149543) ^ 3602 = 27961029324 := by
        calc
          (6 : ZMod 30218149543) ^ 3602 = (6 : ZMod 30218149543) ^ (1801 + 1801) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1801 * (6 : ZMod 30218149543) ^ 1801 := by rw [pow_add]
          _ = 27961029324 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 30218149543) ^ 7204 = 19794909480 := by
        calc
          (6 : ZMod 30218149543) ^ 7204 = (6 : ZMod 30218149543) ^ (3602 + 3602) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 3602 * (6 : ZMod 30218149543) ^ 3602 := by rw [pow_add]
          _ = 19794909480 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 30218149543) ^ 14409 = 3093955246 := by
        calc
          (6 : ZMod 30218149543) ^ 14409 = (6 : ZMod 30218149543) ^ (7204 + 7204 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 7204 * (6 : ZMod 30218149543) ^ 7204) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 3093955246 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 30218149543) ^ 28818 = 14803941691 := by
        calc
          (6 : ZMod 30218149543) ^ 28818 = (6 : ZMod 30218149543) ^ (14409 + 14409) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 14409 * (6 : ZMod 30218149543) ^ 14409 := by rw [pow_add]
          _ = 14803941691 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 30218149543) ^ 57636 = 6177785561 := by
        calc
          (6 : ZMod 30218149543) ^ 57636 = (6 : ZMod 30218149543) ^ (28818 + 28818) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 28818 * (6 : ZMod 30218149543) ^ 28818 := by rw [pow_add]
          _ = 6177785561 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 30218149543) ^ 115273 = 5925487552 := by
        calc
          (6 : ZMod 30218149543) ^ 115273 = (6 : ZMod 30218149543) ^ (57636 + 57636 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 57636 * (6 : ZMod 30218149543) ^ 57636) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 5925487552 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 30218149543) ^ 230546 = 6657289542 := by
        calc
          (6 : ZMod 30218149543) ^ 230546 = (6 : ZMod 30218149543) ^ (115273 + 115273) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 115273 * (6 : ZMod 30218149543) ^ 115273 := by rw [pow_add]
          _ = 6657289542 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 30218149543) ^ 461092 = 21749451504 := by
        calc
          (6 : ZMod 30218149543) ^ 461092 = (6 : ZMod 30218149543) ^ (230546 + 230546) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 230546 * (6 : ZMod 30218149543) ^ 230546 := by rw [pow_add]
          _ = 21749451504 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 30218149543) ^ 922184 = 7361938450 := by
        calc
          (6 : ZMod 30218149543) ^ 922184 = (6 : ZMod 30218149543) ^ (461092 + 461092) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 461092 * (6 : ZMod 30218149543) ^ 461092 := by rw [pow_add]
          _ = 7361938450 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 30218149543) ^ 1844369 = 12197149431 := by
        calc
          (6 : ZMod 30218149543) ^ 1844369 = (6 : ZMod 30218149543) ^ (922184 + 922184 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 922184 * (6 : ZMod 30218149543) ^ 922184) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 12197149431 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 30218149543) ^ 3688738 = 8319586613 := by
        calc
          (6 : ZMod 30218149543) ^ 3688738 = (6 : ZMod 30218149543) ^ (1844369 + 1844369) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1844369 * (6 : ZMod 30218149543) ^ 1844369 := by rw [pow_add]
          _ = 8319586613 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 30218149543) ^ 7377477 = 15286638907 := by
        calc
          (6 : ZMod 30218149543) ^ 7377477 = (6 : ZMod 30218149543) ^ (3688738 + 3688738 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 3688738 * (6 : ZMod 30218149543) ^ 3688738) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 15286638907 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 30218149543) ^ 14754955 = 10746897807 := by
        calc
          (6 : ZMod 30218149543) ^ 14754955 = (6 : ZMod 30218149543) ^ (7377477 + 7377477 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 7377477 * (6 : ZMod 30218149543) ^ 7377477) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 10746897807 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 30218149543) ^ 29509911 = 19055361661 := by
        calc
          (6 : ZMod 30218149543) ^ 29509911 = (6 : ZMod 30218149543) ^ (14754955 + 14754955 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 14754955 * (6 : ZMod 30218149543) ^ 14754955) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 19055361661 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 30218149543) ^ 59019823 = 3227742576 := by
        calc
          (6 : ZMod 30218149543) ^ 59019823 = (6 : ZMod 30218149543) ^ (29509911 + 29509911 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 29509911 * (6 : ZMod 30218149543) ^ 29509911) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 3227742576 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 30218149543) ^ 118039646 = 21758067554 := by
        calc
          (6 : ZMod 30218149543) ^ 118039646 = (6 : ZMod 30218149543) ^ (59019823 + 59019823) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 59019823 * (6 : ZMod 30218149543) ^ 59019823 := by rw [pow_add]
          _ = 21758067554 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 30218149543) ^ 236079293 = 15789744878 := by
        calc
          (6 : ZMod 30218149543) ^ 236079293 = (6 : ZMod 30218149543) ^ (118039646 + 118039646 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 118039646 * (6 : ZMod 30218149543) ^ 118039646) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 15789744878 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 30218149543) ^ 472158586 = 1160690580 := by
        calc
          (6 : ZMod 30218149543) ^ 472158586 = (6 : ZMod 30218149543) ^ (236079293 + 236079293) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 236079293 * (6 : ZMod 30218149543) ^ 236079293 := by rw [pow_add]
          _ = 1160690580 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 30218149543) ^ 944317173 = 7703162087 := by
        calc
          (6 : ZMod 30218149543) ^ 944317173 = (6 : ZMod 30218149543) ^ (472158586 + 472158586 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 472158586 * (6 : ZMod 30218149543) ^ 472158586) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 7703162087 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 30218149543) ^ 1888634346 = 17703250356 := by
        calc
          (6 : ZMod 30218149543) ^ 1888634346 = (6 : ZMod 30218149543) ^ (944317173 + 944317173) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 944317173 * (6 : ZMod 30218149543) ^ 944317173 := by rw [pow_add]
          _ = 17703250356 := by rw [fermat_29]; decide
      have fermat_31 : (6 : ZMod 30218149543) ^ 3777268692 = 16011550160 := by
        calc
          (6 : ZMod 30218149543) ^ 3777268692 = (6 : ZMod 30218149543) ^ (1888634346 + 1888634346) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1888634346 * (6 : ZMod 30218149543) ^ 1888634346 := by rw [pow_add]
          _ = 16011550160 := by rw [fermat_30]; decide
      have fermat_32 : (6 : ZMod 30218149543) ^ 7554537385 = 13079834305 := by
        calc
          (6 : ZMod 30218149543) ^ 7554537385 = (6 : ZMod 30218149543) ^ (3777268692 + 3777268692 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 3777268692 * (6 : ZMod 30218149543) ^ 3777268692) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 13079834305 := by rw [fermat_31]; decide
      have fermat_33 : (6 : ZMod 30218149543) ^ 15109074771 = 30218149542 := by
        calc
          (6 : ZMod 30218149543) ^ 15109074771 = (6 : ZMod 30218149543) ^ (7554537385 + 7554537385 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 7554537385 * (6 : ZMod 30218149543) ^ 7554537385) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 30218149542 := by rw [fermat_32]; decide
      have fermat_34 : (6 : ZMod 30218149543) ^ 30218149542 = 1 := by
        calc
          (6 : ZMod 30218149543) ^ 30218149542 = (6 : ZMod 30218149543) ^ (15109074771 + 15109074771) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 15109074771 * (6 : ZMod 30218149543) ^ 15109074771 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (73, 1), (9855887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (73, 1), (9855887, 1)] : List FactorBlock).map factorBlockValue).prod = 30218149543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 30218149543) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 30218149543) ^ 3 = 216 := by
        calc
          (6 : ZMod 30218149543) ^ 3 = (6 : ZMod 30218149543) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 1 * (6 : ZMod 30218149543) ^ 1) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 30218149543) ^ 7 = 279936 := by
        calc
          (6 : ZMod 30218149543) ^ 7 = (6 : ZMod 30218149543) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 3 * (6 : ZMod 30218149543) ^ 3) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 30218149543) ^ 14 = 17927865010 := by
        calc
          (6 : ZMod 30218149543) ^ 14 = (6 : ZMod 30218149543) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 7 * (6 : ZMod 30218149543) ^ 7 := by rw [pow_add]
          _ = 17927865010 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 30218149543) ^ 28 = 14273128925 := by
        calc
          (6 : ZMod 30218149543) ^ 28 = (6 : ZMod 30218149543) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 14 * (6 : ZMod 30218149543) ^ 14 := by rw [pow_add]
          _ = 14273128925 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 30218149543) ^ 56 = 30210176183 := by
        calc
          (6 : ZMod 30218149543) ^ 56 = (6 : ZMod 30218149543) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 28 * (6 : ZMod 30218149543) ^ 28 := by rw [pow_add]
          _ = 30210176183 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 30218149543) ^ 112 = 25701200671 := by
        calc
          (6 : ZMod 30218149543) ^ 112 = (6 : ZMod 30218149543) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 56 * (6 : ZMod 30218149543) ^ 56 := by rw [pow_add]
          _ = 25701200671 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 30218149543) ^ 225 = 2956966935 := by
        calc
          (6 : ZMod 30218149543) ^ 225 = (6 : ZMod 30218149543) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 112 * (6 : ZMod 30218149543) ^ 112) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 2956966935 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 30218149543) ^ 450 = 4268476360 := by
        calc
          (6 : ZMod 30218149543) ^ 450 = (6 : ZMod 30218149543) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 225 * (6 : ZMod 30218149543) ^ 225 := by rw [pow_add]
          _ = 4268476360 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 30218149543) ^ 900 = 10119889361 := by
        calc
          (6 : ZMod 30218149543) ^ 900 = (6 : ZMod 30218149543) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 450 * (6 : ZMod 30218149543) ^ 450 := by rw [pow_add]
          _ = 10119889361 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 30218149543) ^ 1801 = 27218159375 := by
        calc
          (6 : ZMod 30218149543) ^ 1801 = (6 : ZMod 30218149543) ^ (900 + 900 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 900 * (6 : ZMod 30218149543) ^ 900) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 27218159375 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 30218149543) ^ 3602 = 27961029324 := by
        calc
          (6 : ZMod 30218149543) ^ 3602 = (6 : ZMod 30218149543) ^ (1801 + 1801) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1801 * (6 : ZMod 30218149543) ^ 1801 := by rw [pow_add]
          _ = 27961029324 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 30218149543) ^ 7204 = 19794909480 := by
        calc
          (6 : ZMod 30218149543) ^ 7204 = (6 : ZMod 30218149543) ^ (3602 + 3602) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 3602 * (6 : ZMod 30218149543) ^ 3602 := by rw [pow_add]
          _ = 19794909480 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 30218149543) ^ 14409 = 3093955246 := by
        calc
          (6 : ZMod 30218149543) ^ 14409 = (6 : ZMod 30218149543) ^ (7204 + 7204 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 7204 * (6 : ZMod 30218149543) ^ 7204) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 3093955246 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 30218149543) ^ 28818 = 14803941691 := by
        calc
          (6 : ZMod 30218149543) ^ 28818 = (6 : ZMod 30218149543) ^ (14409 + 14409) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 14409 * (6 : ZMod 30218149543) ^ 14409 := by rw [pow_add]
          _ = 14803941691 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 30218149543) ^ 57636 = 6177785561 := by
        calc
          (6 : ZMod 30218149543) ^ 57636 = (6 : ZMod 30218149543) ^ (28818 + 28818) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 28818 * (6 : ZMod 30218149543) ^ 28818 := by rw [pow_add]
          _ = 6177785561 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 30218149543) ^ 115273 = 5925487552 := by
        calc
          (6 : ZMod 30218149543) ^ 115273 = (6 : ZMod 30218149543) ^ (57636 + 57636 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 57636 * (6 : ZMod 30218149543) ^ 57636) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 5925487552 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 30218149543) ^ 230546 = 6657289542 := by
        calc
          (6 : ZMod 30218149543) ^ 230546 = (6 : ZMod 30218149543) ^ (115273 + 115273) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 115273 * (6 : ZMod 30218149543) ^ 115273 := by rw [pow_add]
          _ = 6657289542 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 30218149543) ^ 461092 = 21749451504 := by
        calc
          (6 : ZMod 30218149543) ^ 461092 = (6 : ZMod 30218149543) ^ (230546 + 230546) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 230546 * (6 : ZMod 30218149543) ^ 230546 := by rw [pow_add]
          _ = 21749451504 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 30218149543) ^ 922184 = 7361938450 := by
        calc
          (6 : ZMod 30218149543) ^ 922184 = (6 : ZMod 30218149543) ^ (461092 + 461092) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 461092 * (6 : ZMod 30218149543) ^ 461092 := by rw [pow_add]
          _ = 7361938450 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 30218149543) ^ 1844369 = 12197149431 := by
        calc
          (6 : ZMod 30218149543) ^ 1844369 = (6 : ZMod 30218149543) ^ (922184 + 922184 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 922184 * (6 : ZMod 30218149543) ^ 922184) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 12197149431 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 30218149543) ^ 3688738 = 8319586613 := by
        calc
          (6 : ZMod 30218149543) ^ 3688738 = (6 : ZMod 30218149543) ^ (1844369 + 1844369) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1844369 * (6 : ZMod 30218149543) ^ 1844369 := by rw [pow_add]
          _ = 8319586613 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 30218149543) ^ 7377477 = 15286638907 := by
        calc
          (6 : ZMod 30218149543) ^ 7377477 = (6 : ZMod 30218149543) ^ (3688738 + 3688738 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 3688738 * (6 : ZMod 30218149543) ^ 3688738) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 15286638907 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 30218149543) ^ 14754955 = 10746897807 := by
        calc
          (6 : ZMod 30218149543) ^ 14754955 = (6 : ZMod 30218149543) ^ (7377477 + 7377477 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 7377477 * (6 : ZMod 30218149543) ^ 7377477) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 10746897807 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 30218149543) ^ 29509911 = 19055361661 := by
        calc
          (6 : ZMod 30218149543) ^ 29509911 = (6 : ZMod 30218149543) ^ (14754955 + 14754955 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 14754955 * (6 : ZMod 30218149543) ^ 14754955) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 19055361661 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 30218149543) ^ 59019823 = 3227742576 := by
        calc
          (6 : ZMod 30218149543) ^ 59019823 = (6 : ZMod 30218149543) ^ (29509911 + 29509911 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 29509911 * (6 : ZMod 30218149543) ^ 29509911) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 3227742576 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 30218149543) ^ 118039646 = 21758067554 := by
        calc
          (6 : ZMod 30218149543) ^ 118039646 = (6 : ZMod 30218149543) ^ (59019823 + 59019823) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 59019823 * (6 : ZMod 30218149543) ^ 59019823 := by rw [pow_add]
          _ = 21758067554 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 30218149543) ^ 236079293 = 15789744878 := by
        calc
          (6 : ZMod 30218149543) ^ 236079293 = (6 : ZMod 30218149543) ^ (118039646 + 118039646 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 118039646 * (6 : ZMod 30218149543) ^ 118039646) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 15789744878 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 30218149543) ^ 472158586 = 1160690580 := by
        calc
          (6 : ZMod 30218149543) ^ 472158586 = (6 : ZMod 30218149543) ^ (236079293 + 236079293) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 236079293 * (6 : ZMod 30218149543) ^ 236079293 := by rw [pow_add]
          _ = 1160690580 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 30218149543) ^ 944317173 = 7703162087 := by
        calc
          (6 : ZMod 30218149543) ^ 944317173 = (6 : ZMod 30218149543) ^ (472158586 + 472158586 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 472158586 * (6 : ZMod 30218149543) ^ 472158586) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 7703162087 := by rw [factor_0_28]; decide
      have factor_0_30 : (6 : ZMod 30218149543) ^ 1888634346 = 17703250356 := by
        calc
          (6 : ZMod 30218149543) ^ 1888634346 = (6 : ZMod 30218149543) ^ (944317173 + 944317173) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 944317173 * (6 : ZMod 30218149543) ^ 944317173 := by rw [pow_add]
          _ = 17703250356 := by rw [factor_0_29]; decide
      have factor_0_31 : (6 : ZMod 30218149543) ^ 3777268692 = 16011550160 := by
        calc
          (6 : ZMod 30218149543) ^ 3777268692 = (6 : ZMod 30218149543) ^ (1888634346 + 1888634346) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1888634346 * (6 : ZMod 30218149543) ^ 1888634346 := by rw [pow_add]
          _ = 16011550160 := by rw [factor_0_30]; decide
      have factor_0_32 : (6 : ZMod 30218149543) ^ 7554537385 = 13079834305 := by
        calc
          (6 : ZMod 30218149543) ^ 7554537385 = (6 : ZMod 30218149543) ^ (3777268692 + 3777268692 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 3777268692 * (6 : ZMod 30218149543) ^ 3777268692) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 13079834305 := by rw [factor_0_31]; decide
      have factor_0_33 : (6 : ZMod 30218149543) ^ 15109074771 = 30218149542 := by
        calc
          (6 : ZMod 30218149543) ^ 15109074771 = (6 : ZMod 30218149543) ^ (7554537385 + 7554537385 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 7554537385 * (6 : ZMod 30218149543) ^ 7554537385) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 30218149542 := by rw [factor_0_32]; decide
      change (6 : ZMod 30218149543) ^ 15109074771 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (6 : ZMod 30218149543) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 30218149543) ^ 2 = 36 := by
        calc
          (6 : ZMod 30218149543) ^ 2 = (6 : ZMod 30218149543) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1 * (6 : ZMod 30218149543) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 30218149543) ^ 4 = 1296 := by
        calc
          (6 : ZMod 30218149543) ^ 4 = (6 : ZMod 30218149543) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 2 * (6 : ZMod 30218149543) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 30218149543) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 30218149543) ^ 9 = (6 : ZMod 30218149543) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 4 * (6 : ZMod 30218149543) ^ 4) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 30218149543) ^ 18 = 26974203936 := by
        calc
          (6 : ZMod 30218149543) ^ 18 = (6 : ZMod 30218149543) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 9 * (6 : ZMod 30218149543) ^ 9 := by rw [pow_add]
          _ = 26974203936 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 30218149543) ^ 37 = 19143154677 := by
        calc
          (6 : ZMod 30218149543) ^ 37 = (6 : ZMod 30218149543) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 18 * (6 : ZMod 30218149543) ^ 18) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 19143154677 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 30218149543) ^ 75 = 9752584708 := by
        calc
          (6 : ZMod 30218149543) ^ 75 = (6 : ZMod 30218149543) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 37 * (6 : ZMod 30218149543) ^ 37) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 9752584708 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 30218149543) ^ 150 = 9456695371 := by
        calc
          (6 : ZMod 30218149543) ^ 150 = (6 : ZMod 30218149543) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 75 * (6 : ZMod 30218149543) ^ 75 := by rw [pow_add]
          _ = 9456695371 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 30218149543) ^ 300 = 25681445485 := by
        calc
          (6 : ZMod 30218149543) ^ 300 = (6 : ZMod 30218149543) ^ (150 + 150) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 150 * (6 : ZMod 30218149543) ^ 150 := by rw [pow_add]
          _ = 25681445485 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 30218149543) ^ 600 = 9445360653 := by
        calc
          (6 : ZMod 30218149543) ^ 600 = (6 : ZMod 30218149543) ^ (300 + 300) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 300 * (6 : ZMod 30218149543) ^ 300 := by rw [pow_add]
          _ = 9445360653 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 30218149543) ^ 1200 = 11358832209 := by
        calc
          (6 : ZMod 30218149543) ^ 1200 = (6 : ZMod 30218149543) ^ (600 + 600) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 600 * (6 : ZMod 30218149543) ^ 600 := by rw [pow_add]
          _ = 11358832209 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 30218149543) ^ 2401 = 10488383073 := by
        calc
          (6 : ZMod 30218149543) ^ 2401 = (6 : ZMod 30218149543) ^ (1200 + 1200 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 1200 * (6 : ZMod 30218149543) ^ 1200) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 10488383073 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 30218149543) ^ 4803 = 20040320383 := by
        calc
          (6 : ZMod 30218149543) ^ 4803 = (6 : ZMod 30218149543) ^ (2401 + 2401 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 2401 * (6 : ZMod 30218149543) ^ 2401) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 20040320383 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 30218149543) ^ 9606 = 23049499986 := by
        calc
          (6 : ZMod 30218149543) ^ 9606 = (6 : ZMod 30218149543) ^ (4803 + 4803) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 4803 * (6 : ZMod 30218149543) ^ 4803 := by rw [pow_add]
          _ = 23049499986 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 30218149543) ^ 19212 = 28112084214 := by
        calc
          (6 : ZMod 30218149543) ^ 19212 = (6 : ZMod 30218149543) ^ (9606 + 9606) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 9606 * (6 : ZMod 30218149543) ^ 9606 := by rw [pow_add]
          _ = 28112084214 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 30218149543) ^ 38424 = 11937167010 := by
        calc
          (6 : ZMod 30218149543) ^ 38424 = (6 : ZMod 30218149543) ^ (19212 + 19212) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 19212 * (6 : ZMod 30218149543) ^ 19212 := by rw [pow_add]
          _ = 11937167010 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 30218149543) ^ 76848 = 12388001016 := by
        calc
          (6 : ZMod 30218149543) ^ 76848 = (6 : ZMod 30218149543) ^ (38424 + 38424) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 38424 * (6 : ZMod 30218149543) ^ 38424 := by rw [pow_add]
          _ = 12388001016 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 30218149543) ^ 153697 = 16496523453 := by
        calc
          (6 : ZMod 30218149543) ^ 153697 = (6 : ZMod 30218149543) ^ (76848 + 76848 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 76848 * (6 : ZMod 30218149543) ^ 76848) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 16496523453 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 30218149543) ^ 307394 = 25769055843 := by
        calc
          (6 : ZMod 30218149543) ^ 307394 = (6 : ZMod 30218149543) ^ (153697 + 153697) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 153697 * (6 : ZMod 30218149543) ^ 153697 := by rw [pow_add]
          _ = 25769055843 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 30218149543) ^ 614789 = 24891596582 := by
        calc
          (6 : ZMod 30218149543) ^ 614789 = (6 : ZMod 30218149543) ^ (307394 + 307394 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 307394 * (6 : ZMod 30218149543) ^ 307394) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 24891596582 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 30218149543) ^ 1229579 = 22598186402 := by
        calc
          (6 : ZMod 30218149543) ^ 1229579 = (6 : ZMod 30218149543) ^ (614789 + 614789 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 614789 * (6 : ZMod 30218149543) ^ 614789) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 22598186402 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 30218149543) ^ 2459159 = 27281669219 := by
        calc
          (6 : ZMod 30218149543) ^ 2459159 = (6 : ZMod 30218149543) ^ (1229579 + 1229579 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 1229579 * (6 : ZMod 30218149543) ^ 1229579) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 27281669219 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 30218149543) ^ 4918318 = 10414131326 := by
        calc
          (6 : ZMod 30218149543) ^ 4918318 = (6 : ZMod 30218149543) ^ (2459159 + 2459159) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 2459159 * (6 : ZMod 30218149543) ^ 2459159 := by rw [pow_add]
          _ = 10414131326 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 30218149543) ^ 9836637 = 6236673143 := by
        calc
          (6 : ZMod 30218149543) ^ 9836637 = (6 : ZMod 30218149543) ^ (4918318 + 4918318 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 4918318 * (6 : ZMod 30218149543) ^ 4918318) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 6236673143 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 30218149543) ^ 19673274 = 18036607578 := by
        calc
          (6 : ZMod 30218149543) ^ 19673274 = (6 : ZMod 30218149543) ^ (9836637 + 9836637) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 9836637 * (6 : ZMod 30218149543) ^ 9836637 := by rw [pow_add]
          _ = 18036607578 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 30218149543) ^ 39346548 = 5059642395 := by
        calc
          (6 : ZMod 30218149543) ^ 39346548 = (6 : ZMod 30218149543) ^ (19673274 + 19673274) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 19673274 * (6 : ZMod 30218149543) ^ 19673274 := by rw [pow_add]
          _ = 5059642395 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 30218149543) ^ 78693097 = 8267636410 := by
        calc
          (6 : ZMod 30218149543) ^ 78693097 = (6 : ZMod 30218149543) ^ (39346548 + 39346548 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 39346548 * (6 : ZMod 30218149543) ^ 39346548) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 8267636410 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 30218149543) ^ 157386195 = 3277771944 := by
        calc
          (6 : ZMod 30218149543) ^ 157386195 = (6 : ZMod 30218149543) ^ (78693097 + 78693097 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 78693097 * (6 : ZMod 30218149543) ^ 78693097) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 3277771944 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 30218149543) ^ 314772391 = 6129708021 := by
        calc
          (6 : ZMod 30218149543) ^ 314772391 = (6 : ZMod 30218149543) ^ (157386195 + 157386195 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 157386195 * (6 : ZMod 30218149543) ^ 157386195) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 6129708021 := by rw [factor_1_27]; decide
      have factor_1_29 : (6 : ZMod 30218149543) ^ 629544782 = 1932894666 := by
        calc
          (6 : ZMod 30218149543) ^ 629544782 = (6 : ZMod 30218149543) ^ (314772391 + 314772391) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 314772391 * (6 : ZMod 30218149543) ^ 314772391 := by rw [pow_add]
          _ = 1932894666 := by rw [factor_1_28]; decide
      have factor_1_30 : (6 : ZMod 30218149543) ^ 1259089564 = 11749266954 := by
        calc
          (6 : ZMod 30218149543) ^ 1259089564 = (6 : ZMod 30218149543) ^ (629544782 + 629544782) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 629544782 * (6 : ZMod 30218149543) ^ 629544782 := by rw [pow_add]
          _ = 11749266954 := by rw [factor_1_29]; decide
      have factor_1_31 : (6 : ZMod 30218149543) ^ 2518179128 = 14823322042 := by
        calc
          (6 : ZMod 30218149543) ^ 2518179128 = (6 : ZMod 30218149543) ^ (1259089564 + 1259089564) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1259089564 * (6 : ZMod 30218149543) ^ 1259089564 := by rw [pow_add]
          _ = 14823322042 := by rw [factor_1_30]; decide
      have factor_1_32 : (6 : ZMod 30218149543) ^ 5036358257 = 14742280046 := by
        calc
          (6 : ZMod 30218149543) ^ 5036358257 = (6 : ZMod 30218149543) ^ (2518179128 + 2518179128 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 2518179128 * (6 : ZMod 30218149543) ^ 2518179128) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 14742280046 := by rw [factor_1_31]; decide
      have factor_1_33 : (6 : ZMod 30218149543) ^ 10072716514 = 14742280045 := by
        calc
          (6 : ZMod 30218149543) ^ 10072716514 = (6 : ZMod 30218149543) ^ (5036358257 + 5036358257) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 5036358257 * (6 : ZMod 30218149543) ^ 5036358257 := by rw [pow_add]
          _ = 14742280045 := by rw [factor_1_32]; decide
      change (6 : ZMod 30218149543) ^ 10072716514 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (6 : ZMod 30218149543) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 30218149543) ^ 2 = 36 := by
        calc
          (6 : ZMod 30218149543) ^ 2 = (6 : ZMod 30218149543) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1 * (6 : ZMod 30218149543) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 30218149543) ^ 4 = 1296 := by
        calc
          (6 : ZMod 30218149543) ^ 4 = (6 : ZMod 30218149543) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 2 * (6 : ZMod 30218149543) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 30218149543) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 30218149543) ^ 8 = (6 : ZMod 30218149543) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 4 * (6 : ZMod 30218149543) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 30218149543) ^ 16 = 10821999957 := by
        calc
          (6 : ZMod 30218149543) ^ 16 = (6 : ZMod 30218149543) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 8 * (6 : ZMod 30218149543) ^ 8 := by rw [pow_add]
          _ = 10821999957 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 30218149543) ^ 32 = 4467566484 := by
        calc
          (6 : ZMod 30218149543) ^ 32 = (6 : ZMod 30218149543) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 16 * (6 : ZMod 30218149543) ^ 16 := by rw [pow_add]
          _ = 4467566484 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 30218149543) ^ 64 = 24675367332 := by
        calc
          (6 : ZMod 30218149543) ^ 64 = (6 : ZMod 30218149543) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 32 * (6 : ZMod 30218149543) ^ 32 := by rw [pow_add]
          _ = 24675367332 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 30218149543) ^ 128 = 22845733985 := by
        calc
          (6 : ZMod 30218149543) ^ 128 = (6 : ZMod 30218149543) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 64 * (6 : ZMod 30218149543) ^ 64 := by rw [pow_add]
          _ = 22845733985 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 30218149543) ^ 257 = 26856212473 := by
        calc
          (6 : ZMod 30218149543) ^ 257 = (6 : ZMod 30218149543) ^ (128 + 128 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 128 * (6 : ZMod 30218149543) ^ 128) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 26856212473 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 30218149543) ^ 514 = 16770506074 := by
        calc
          (6 : ZMod 30218149543) ^ 514 = (6 : ZMod 30218149543) ^ (257 + 257) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 257 * (6 : ZMod 30218149543) ^ 257 := by rw [pow_add]
          _ = 16770506074 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 30218149543) ^ 1029 = 22986790022 := by
        calc
          (6 : ZMod 30218149543) ^ 1029 = (6 : ZMod 30218149543) ^ (514 + 514 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 514 * (6 : ZMod 30218149543) ^ 514) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 22986790022 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 30218149543) ^ 2058 = 7124896906 := by
        calc
          (6 : ZMod 30218149543) ^ 2058 = (6 : ZMod 30218149543) ^ (1029 + 1029) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1029 * (6 : ZMod 30218149543) ^ 1029 := by rw [pow_add]
          _ = 7124896906 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 30218149543) ^ 4116 = 7921354962 := by
        calc
          (6 : ZMod 30218149543) ^ 4116 = (6 : ZMod 30218149543) ^ (2058 + 2058) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 2058 * (6 : ZMod 30218149543) ^ 2058 := by rw [pow_add]
          _ = 7921354962 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 30218149543) ^ 8233 = 9568109127 := by
        calc
          (6 : ZMod 30218149543) ^ 8233 = (6 : ZMod 30218149543) ^ (4116 + 4116 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 4116 * (6 : ZMod 30218149543) ^ 4116) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 9568109127 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 30218149543) ^ 16467 = 19697696151 := by
        calc
          (6 : ZMod 30218149543) ^ 16467 = (6 : ZMod 30218149543) ^ (8233 + 8233 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 8233 * (6 : ZMod 30218149543) ^ 8233) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 19697696151 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 30218149543) ^ 32935 = 7406418847 := by
        calc
          (6 : ZMod 30218149543) ^ 32935 = (6 : ZMod 30218149543) ^ (16467 + 16467 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 16467 * (6 : ZMod 30218149543) ^ 16467) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 7406418847 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 30218149543) ^ 65870 = 1606262566 := by
        calc
          (6 : ZMod 30218149543) ^ 65870 = (6 : ZMod 30218149543) ^ (32935 + 32935) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 32935 * (6 : ZMod 30218149543) ^ 32935 := by rw [pow_add]
          _ = 1606262566 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 30218149543) ^ 131740 = 4427228273 := by
        calc
          (6 : ZMod 30218149543) ^ 131740 = (6 : ZMod 30218149543) ^ (65870 + 65870) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 65870 * (6 : ZMod 30218149543) ^ 65870 := by rw [pow_add]
          _ = 4427228273 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 30218149543) ^ 263481 = 4992765340 := by
        calc
          (6 : ZMod 30218149543) ^ 263481 = (6 : ZMod 30218149543) ^ (131740 + 131740 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 131740 * (6 : ZMod 30218149543) ^ 131740) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 4992765340 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 30218149543) ^ 526962 = 27926470949 := by
        calc
          (6 : ZMod 30218149543) ^ 526962 = (6 : ZMod 30218149543) ^ (263481 + 263481) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 263481 * (6 : ZMod 30218149543) ^ 263481 := by rw [pow_add]
          _ = 27926470949 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 30218149543) ^ 1053925 = 8884408 := by
        calc
          (6 : ZMod 30218149543) ^ 1053925 = (6 : ZMod 30218149543) ^ (526962 + 526962 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 526962 * (6 : ZMod 30218149543) ^ 526962) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 8884408 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 30218149543) ^ 2107850 = 2898904148 := by
        calc
          (6 : ZMod 30218149543) ^ 2107850 = (6 : ZMod 30218149543) ^ (1053925 + 1053925) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1053925 * (6 : ZMod 30218149543) ^ 1053925 := by rw [pow_add]
          _ = 2898904148 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 30218149543) ^ 4215701 = 6848927366 := by
        calc
          (6 : ZMod 30218149543) ^ 4215701 = (6 : ZMod 30218149543) ^ (2107850 + 2107850 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 2107850 * (6 : ZMod 30218149543) ^ 2107850) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 6848927366 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 30218149543) ^ 8431403 = 21938042728 := by
        calc
          (6 : ZMod 30218149543) ^ 8431403 = (6 : ZMod 30218149543) ^ (4215701 + 4215701 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 4215701 * (6 : ZMod 30218149543) ^ 4215701) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 21938042728 := by rw [factor_2_22]; decide
      have factor_2_24 : (6 : ZMod 30218149543) ^ 16862806 = 6584213776 := by
        calc
          (6 : ZMod 30218149543) ^ 16862806 = (6 : ZMod 30218149543) ^ (8431403 + 8431403) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 8431403 * (6 : ZMod 30218149543) ^ 8431403 := by rw [pow_add]
          _ = 6584213776 := by rw [factor_2_23]; decide
      have factor_2_25 : (6 : ZMod 30218149543) ^ 33725613 = 14737729367 := by
        calc
          (6 : ZMod 30218149543) ^ 33725613 = (6 : ZMod 30218149543) ^ (16862806 + 16862806 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 16862806 * (6 : ZMod 30218149543) ^ 16862806) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 14737729367 := by rw [factor_2_24]; decide
      have factor_2_26 : (6 : ZMod 30218149543) ^ 67451226 = 4027728435 := by
        calc
          (6 : ZMod 30218149543) ^ 67451226 = (6 : ZMod 30218149543) ^ (33725613 + 33725613) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 33725613 * (6 : ZMod 30218149543) ^ 33725613 := by rw [pow_add]
          _ = 4027728435 := by rw [factor_2_25]; decide
      have factor_2_27 : (6 : ZMod 30218149543) ^ 134902453 = 20413881039 := by
        calc
          (6 : ZMod 30218149543) ^ 134902453 = (6 : ZMod 30218149543) ^ (67451226 + 67451226 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 67451226 * (6 : ZMod 30218149543) ^ 67451226) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 20413881039 := by rw [factor_2_26]; decide
      have factor_2_28 : (6 : ZMod 30218149543) ^ 269804906 = 7282474754 := by
        calc
          (6 : ZMod 30218149543) ^ 269804906 = (6 : ZMod 30218149543) ^ (134902453 + 134902453) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 134902453 * (6 : ZMod 30218149543) ^ 134902453 := by rw [pow_add]
          _ = 7282474754 := by rw [factor_2_27]; decide
      have factor_2_29 : (6 : ZMod 30218149543) ^ 539609813 = 26694885192 := by
        calc
          (6 : ZMod 30218149543) ^ 539609813 = (6 : ZMod 30218149543) ^ (269804906 + 269804906 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 269804906 * (6 : ZMod 30218149543) ^ 269804906) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 26694885192 := by rw [factor_2_28]; decide
      have factor_2_30 : (6 : ZMod 30218149543) ^ 1079219626 = 12996361175 := by
        calc
          (6 : ZMod 30218149543) ^ 1079219626 = (6 : ZMod 30218149543) ^ (539609813 + 539609813) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 539609813 * (6 : ZMod 30218149543) ^ 539609813 := by rw [pow_add]
          _ = 12996361175 := by rw [factor_2_29]; decide
      have factor_2_31 : (6 : ZMod 30218149543) ^ 2158439253 = 2266488856 := by
        calc
          (6 : ZMod 30218149543) ^ 2158439253 = (6 : ZMod 30218149543) ^ (1079219626 + 1079219626 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 1079219626 * (6 : ZMod 30218149543) ^ 1079219626) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 2266488856 := by rw [factor_2_30]; decide
      have factor_2_32 : (6 : ZMod 30218149543) ^ 4316878506 = 22958919045 := by
        calc
          (6 : ZMod 30218149543) ^ 4316878506 = (6 : ZMod 30218149543) ^ (2158439253 + 2158439253) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 2158439253 * (6 : ZMod 30218149543) ^ 2158439253 := by rw [pow_add]
          _ = 22958919045 := by rw [factor_2_31]; decide
      change (6 : ZMod 30218149543) ^ 4316878506 ≠ 1
      rw [factor_2_32]
      decide
    ·
      have factor_3_0 : (6 : ZMod 30218149543) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 30218149543) ^ 3 = 216 := by
        calc
          (6 : ZMod 30218149543) ^ 3 = (6 : ZMod 30218149543) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 1 * (6 : ZMod 30218149543) ^ 1) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 30218149543) ^ 6 = 46656 := by
        calc
          (6 : ZMod 30218149543) ^ 6 = (6 : ZMod 30218149543) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 3 * (6 : ZMod 30218149543) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 30218149543) ^ 12 = 2176782336 := by
        calc
          (6 : ZMod 30218149543) ^ 12 = (6 : ZMod 30218149543) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 6 * (6 : ZMod 30218149543) ^ 6 := by rw [pow_add]
          _ = 2176782336 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 30218149543) ^ 24 = 13184820695 := by
        calc
          (6 : ZMod 30218149543) ^ 24 = (6 : ZMod 30218149543) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 12 * (6 : ZMod 30218149543) ^ 12 := by rw [pow_add]
          _ = 13184820695 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 30218149543) ^ 49 = 3386933628 := by
        calc
          (6 : ZMod 30218149543) ^ 49 = (6 : ZMod 30218149543) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 24 * (6 : ZMod 30218149543) ^ 24) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 3386933628 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 30218149543) ^ 98 = 23553502431 := by
        calc
          (6 : ZMod 30218149543) ^ 98 = (6 : ZMod 30218149543) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 49 * (6 : ZMod 30218149543) ^ 49 := by rw [pow_add]
          _ = 23553502431 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 30218149543) ^ 197 = 14710022004 := by
        calc
          (6 : ZMod 30218149543) ^ 197 = (6 : ZMod 30218149543) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 98 * (6 : ZMod 30218149543) ^ 98) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 14710022004 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 30218149543) ^ 394 = 28050787273 := by
        calc
          (6 : ZMod 30218149543) ^ 394 = (6 : ZMod 30218149543) ^ (197 + 197) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 197 * (6 : ZMod 30218149543) ^ 197 := by rw [pow_add]
          _ = 28050787273 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 30218149543) ^ 789 = 14686110271 := by
        calc
          (6 : ZMod 30218149543) ^ 789 = (6 : ZMod 30218149543) ^ (394 + 394 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 394 * (6 : ZMod 30218149543) ^ 394) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 14686110271 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 30218149543) ^ 1579 = 9525584531 := by
        calc
          (6 : ZMod 30218149543) ^ 1579 = (6 : ZMod 30218149543) ^ (789 + 789 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 789 * (6 : ZMod 30218149543) ^ 789) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 9525584531 := by rw [factor_3_9]; decide
      have factor_3_11 : (6 : ZMod 30218149543) ^ 3158 = 25014424143 := by
        calc
          (6 : ZMod 30218149543) ^ 3158 = (6 : ZMod 30218149543) ^ (1579 + 1579) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1579 * (6 : ZMod 30218149543) ^ 1579 := by rw [pow_add]
          _ = 25014424143 := by rw [factor_3_10]; decide
      have factor_3_12 : (6 : ZMod 30218149543) ^ 6316 = 3415757275 := by
        calc
          (6 : ZMod 30218149543) ^ 6316 = (6 : ZMod 30218149543) ^ (3158 + 3158) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 3158 * (6 : ZMod 30218149543) ^ 3158 := by rw [pow_add]
          _ = 3415757275 := by rw [factor_3_11]; decide
      have factor_3_13 : (6 : ZMod 30218149543) ^ 12632 = 4326749906 := by
        calc
          (6 : ZMod 30218149543) ^ 12632 = (6 : ZMod 30218149543) ^ (6316 + 6316) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 6316 * (6 : ZMod 30218149543) ^ 6316 := by rw [pow_add]
          _ = 4326749906 := by rw [factor_3_12]; decide
      have factor_3_14 : (6 : ZMod 30218149543) ^ 25265 = 20020812084 := by
        calc
          (6 : ZMod 30218149543) ^ 25265 = (6 : ZMod 30218149543) ^ (12632 + 12632 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 12632 * (6 : ZMod 30218149543) ^ 12632) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 20020812084 := by rw [factor_3_13]; decide
      have factor_3_15 : (6 : ZMod 30218149543) ^ 50530 = 10352328232 := by
        calc
          (6 : ZMod 30218149543) ^ 50530 = (6 : ZMod 30218149543) ^ (25265 + 25265) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 25265 * (6 : ZMod 30218149543) ^ 25265 := by rw [pow_add]
          _ = 10352328232 := by rw [factor_3_14]; decide
      have factor_3_16 : (6 : ZMod 30218149543) ^ 101061 = 6677051407 := by
        calc
          (6 : ZMod 30218149543) ^ 101061 = (6 : ZMod 30218149543) ^ (50530 + 50530 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 50530 * (6 : ZMod 30218149543) ^ 50530) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 6677051407 := by rw [factor_3_15]; decide
      have factor_3_17 : (6 : ZMod 30218149543) ^ 202122 = 17115140317 := by
        calc
          (6 : ZMod 30218149543) ^ 202122 = (6 : ZMod 30218149543) ^ (101061 + 101061) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 101061 * (6 : ZMod 30218149543) ^ 101061 := by rw [pow_add]
          _ = 17115140317 := by rw [factor_3_16]; decide
      have factor_3_18 : (6 : ZMod 30218149543) ^ 404245 = 13772019595 := by
        calc
          (6 : ZMod 30218149543) ^ 404245 = (6 : ZMod 30218149543) ^ (202122 + 202122 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 202122 * (6 : ZMod 30218149543) ^ 202122) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 13772019595 := by rw [factor_3_17]; decide
      have factor_3_19 : (6 : ZMod 30218149543) ^ 808490 = 7498567144 := by
        calc
          (6 : ZMod 30218149543) ^ 808490 = (6 : ZMod 30218149543) ^ (404245 + 404245) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 404245 * (6 : ZMod 30218149543) ^ 404245 := by rw [pow_add]
          _ = 7498567144 := by rw [factor_3_18]; decide
      have factor_3_20 : (6 : ZMod 30218149543) ^ 1616981 = 27903885307 := by
        calc
          (6 : ZMod 30218149543) ^ 1616981 = (6 : ZMod 30218149543) ^ (808490 + 808490 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 808490 * (6 : ZMod 30218149543) ^ 808490) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 27903885307 := by rw [factor_3_19]; decide
      have factor_3_21 : (6 : ZMod 30218149543) ^ 3233962 = 178349970 := by
        calc
          (6 : ZMod 30218149543) ^ 3233962 = (6 : ZMod 30218149543) ^ (1616981 + 1616981) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1616981 * (6 : ZMod 30218149543) ^ 1616981 := by rw [pow_add]
          _ = 178349970 := by rw [factor_3_20]; decide
      have factor_3_22 : (6 : ZMod 30218149543) ^ 6467925 = 28638082855 := by
        calc
          (6 : ZMod 30218149543) ^ 6467925 = (6 : ZMod 30218149543) ^ (3233962 + 3233962 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 3233962 * (6 : ZMod 30218149543) ^ 3233962) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 28638082855 := by rw [factor_3_21]; decide
      have factor_3_23 : (6 : ZMod 30218149543) ^ 12935851 = 3153166655 := by
        calc
          (6 : ZMod 30218149543) ^ 12935851 = (6 : ZMod 30218149543) ^ (6467925 + 6467925 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 6467925 * (6 : ZMod 30218149543) ^ 6467925) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 3153166655 := by rw [factor_3_22]; decide
      have factor_3_24 : (6 : ZMod 30218149543) ^ 25871703 = 14082431642 := by
        calc
          (6 : ZMod 30218149543) ^ 25871703 = (6 : ZMod 30218149543) ^ (12935851 + 12935851 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 12935851 * (6 : ZMod 30218149543) ^ 12935851) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 14082431642 := by rw [factor_3_23]; decide
      have factor_3_25 : (6 : ZMod 30218149543) ^ 51743406 = 212255560 := by
        calc
          (6 : ZMod 30218149543) ^ 51743406 = (6 : ZMod 30218149543) ^ (25871703 + 25871703) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 25871703 * (6 : ZMod 30218149543) ^ 25871703 := by rw [pow_add]
          _ = 212255560 := by rw [factor_3_24]; decide
      have factor_3_26 : (6 : ZMod 30218149543) ^ 103486813 = 13730145852 := by
        calc
          (6 : ZMod 30218149543) ^ 103486813 = (6 : ZMod 30218149543) ^ (51743406 + 51743406 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 51743406 * (6 : ZMod 30218149543) ^ 51743406) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 13730145852 := by rw [factor_3_25]; decide
      have factor_3_27 : (6 : ZMod 30218149543) ^ 206973627 = 25617087192 := by
        calc
          (6 : ZMod 30218149543) ^ 206973627 = (6 : ZMod 30218149543) ^ (103486813 + 103486813 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 103486813 * (6 : ZMod 30218149543) ^ 103486813) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 25617087192 := by rw [factor_3_26]; decide
      have factor_3_28 : (6 : ZMod 30218149543) ^ 413947254 = 26321703759 := by
        calc
          (6 : ZMod 30218149543) ^ 413947254 = (6 : ZMod 30218149543) ^ (206973627 + 206973627) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 206973627 * (6 : ZMod 30218149543) ^ 206973627 := by rw [pow_add]
          _ = 26321703759 := by rw [factor_3_27]; decide
      change (6 : ZMod 30218149543) ^ 413947254 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (6 : ZMod 30218149543) ^ 1 = 6 := by norm_num
      have factor_4_1 : (6 : ZMod 30218149543) ^ 2 = 36 := by
        calc
          (6 : ZMod 30218149543) ^ 2 = (6 : ZMod 30218149543) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1 * (6 : ZMod 30218149543) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_4_0]; decide
      have factor_4_2 : (6 : ZMod 30218149543) ^ 5 = 7776 := by
        calc
          (6 : ZMod 30218149543) ^ 5 = (6 : ZMod 30218149543) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 2 * (6 : ZMod 30218149543) ^ 2) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_4_1]; decide
      have factor_4_3 : (6 : ZMod 30218149543) ^ 11 = 362797056 := by
        calc
          (6 : ZMod 30218149543) ^ 11 = (6 : ZMod 30218149543) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 5 * (6 : ZMod 30218149543) ^ 5) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 362797056 := by rw [factor_4_2]; decide
      have factor_4_4 : (6 : ZMod 30218149543) ^ 23 = 7233828373 := by
        calc
          (6 : ZMod 30218149543) ^ 23 = (6 : ZMod 30218149543) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 11 * (6 : ZMod 30218149543) ^ 11) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 7233828373 := by rw [factor_4_3]; decide
      have factor_4_5 : (6 : ZMod 30218149543) ^ 47 = 10166798004 := by
        calc
          (6 : ZMod 30218149543) ^ 47 = (6 : ZMod 30218149543) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 23 * (6 : ZMod 30218149543) ^ 23) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 10166798004 := by rw [factor_4_4]; decide
      have factor_4_6 : (6 : ZMod 30218149543) ^ 95 = 25710531800 := by
        calc
          (6 : ZMod 30218149543) ^ 95 = (6 : ZMod 30218149543) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 47 * (6 : ZMod 30218149543) ^ 47) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 25710531800 := by rw [factor_4_5]; decide
      have factor_4_7 : (6 : ZMod 30218149543) ^ 191 = 6148092110 := by
        calc
          (6 : ZMod 30218149543) ^ 191 = (6 : ZMod 30218149543) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 95 * (6 : ZMod 30218149543) ^ 95) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 6148092110 := by rw [factor_4_6]; decide
      have factor_4_8 : (6 : ZMod 30218149543) ^ 383 = 11789285416 := by
        calc
          (6 : ZMod 30218149543) ^ 383 = (6 : ZMod 30218149543) ^ (191 + 191 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 191 * (6 : ZMod 30218149543) ^ 191) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 11789285416 := by rw [factor_4_7]; decide
      have factor_4_9 : (6 : ZMod 30218149543) ^ 766 = 21713130504 := by
        calc
          (6 : ZMod 30218149543) ^ 766 = (6 : ZMod 30218149543) ^ (383 + 383) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 383 * (6 : ZMod 30218149543) ^ 383 := by rw [pow_add]
          _ = 21713130504 := by rw [factor_4_8]; decide
      have factor_4_10 : (6 : ZMod 30218149543) ^ 1533 = 19982739107 := by
        calc
          (6 : ZMod 30218149543) ^ 1533 = (6 : ZMod 30218149543) ^ (766 + 766 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = ((6 : ZMod 30218149543) ^ 766 * (6 : ZMod 30218149543) ^ 766) * (6 : ZMod 30218149543) := by rw [pow_succ, pow_add]
          _ = 19982739107 := by rw [factor_4_9]; decide
      have factor_4_11 : (6 : ZMod 30218149543) ^ 3066 = 22879011878 := by
        calc
          (6 : ZMod 30218149543) ^ 3066 = (6 : ZMod 30218149543) ^ (1533 + 1533) :=
            congrArg (fun n : ℕ => (6 : ZMod 30218149543) ^ n) (by norm_num)
          _ = (6 : ZMod 30218149543) ^ 1533 * (6 : ZMod 30218149543) ^ 1533 := by rw [pow_add]
          _ = 22879011878 := by rw [factor_4_10]; decide
      change (6 : ZMod 30218149543) ^ 3066 ≠ 1
      rw [factor_4_11]
      decide

#print axioms prime_lucas_30218149543

end TotientTailPeriodKiller
end Erdos249257
