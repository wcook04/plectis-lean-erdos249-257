import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime30218149543

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_120872598173 : Nat.Prime 120872598173 := by
  apply lucas_primality 120872598173 (2 : ZMod 120872598173)
  ·
      have fermat_0 : (2 : ZMod 120872598173) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 120872598173) ^ 3 = 8 := by
        calc
          (2 : ZMod 120872598173) ^ 3 = (2 : ZMod 120872598173) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 1 * (2 : ZMod 120872598173) ^ 1) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 120872598173) ^ 7 = 128 := by
        calc
          (2 : ZMod 120872598173) ^ 7 = (2 : ZMod 120872598173) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 3 * (2 : ZMod 120872598173) ^ 3) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 120872598173) ^ 14 = 16384 := by
        calc
          (2 : ZMod 120872598173) ^ 14 = (2 : ZMod 120872598173) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 7 * (2 : ZMod 120872598173) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 120872598173) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 120872598173) ^ 28 = (2 : ZMod 120872598173) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 14 * (2 : ZMod 120872598173) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 120872598173) ^ 56 = 119872683024 := by
        calc
          (2 : ZMod 120872598173) ^ 56 = (2 : ZMod 120872598173) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 28 * (2 : ZMod 120872598173) ^ 28 := by rw [pow_add]
          _ = 119872683024 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 120872598173) ^ 112 = 94682814164 := by
        calc
          (2 : ZMod 120872598173) ^ 112 = (2 : ZMod 120872598173) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 56 * (2 : ZMod 120872598173) ^ 56 := by rw [pow_add]
          _ = 94682814164 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 120872598173) ^ 225 = 99969510614 := by
        calc
          (2 : ZMod 120872598173) ^ 225 = (2 : ZMod 120872598173) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 112 * (2 : ZMod 120872598173) ^ 112) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 99969510614 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 120872598173) ^ 450 = 43479015140 := by
        calc
          (2 : ZMod 120872598173) ^ 450 = (2 : ZMod 120872598173) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 225 * (2 : ZMod 120872598173) ^ 225 := by rw [pow_add]
          _ = 43479015140 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 120872598173) ^ 900 = 114625839687 := by
        calc
          (2 : ZMod 120872598173) ^ 900 = (2 : ZMod 120872598173) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 450 * (2 : ZMod 120872598173) ^ 450 := by rw [pow_add]
          _ = 114625839687 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 120872598173) ^ 1801 = 96394923348 := by
        calc
          (2 : ZMod 120872598173) ^ 1801 = (2 : ZMod 120872598173) ^ (900 + 900 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 900 * (2 : ZMod 120872598173) ^ 900) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 96394923348 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 120872598173) ^ 3602 = 16567391016 := by
        calc
          (2 : ZMod 120872598173) ^ 3602 = (2 : ZMod 120872598173) ^ (1801 + 1801) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 1801 * (2 : ZMod 120872598173) ^ 1801 := by rw [pow_add]
          _ = 16567391016 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 120872598173) ^ 7204 = 54148257860 := by
        calc
          (2 : ZMod 120872598173) ^ 7204 = (2 : ZMod 120872598173) ^ (3602 + 3602) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 3602 * (2 : ZMod 120872598173) ^ 3602 := by rw [pow_add]
          _ = 54148257860 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 120872598173) ^ 14409 = 37135284705 := by
        calc
          (2 : ZMod 120872598173) ^ 14409 = (2 : ZMod 120872598173) ^ (7204 + 7204 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 7204 * (2 : ZMod 120872598173) ^ 7204) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 37135284705 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 120872598173) ^ 28818 = 60513897276 := by
        calc
          (2 : ZMod 120872598173) ^ 28818 = (2 : ZMod 120872598173) ^ (14409 + 14409) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 14409 * (2 : ZMod 120872598173) ^ 14409 := by rw [pow_add]
          _ = 60513897276 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 120872598173) ^ 57636 = 59444942199 := by
        calc
          (2 : ZMod 120872598173) ^ 57636 = (2 : ZMod 120872598173) ^ (28818 + 28818) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 28818 * (2 : ZMod 120872598173) ^ 28818 := by rw [pow_add]
          _ = 59444942199 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 120872598173) ^ 115273 = 9677544519 := by
        calc
          (2 : ZMod 120872598173) ^ 115273 = (2 : ZMod 120872598173) ^ (57636 + 57636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 57636 * (2 : ZMod 120872598173) ^ 57636) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 9677544519 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 120872598173) ^ 230546 = 112627142264 := by
        calc
          (2 : ZMod 120872598173) ^ 230546 = (2 : ZMod 120872598173) ^ (115273 + 115273) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 115273 * (2 : ZMod 120872598173) ^ 115273 := by rw [pow_add]
          _ = 112627142264 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 120872598173) ^ 461092 = 90632936012 := by
        calc
          (2 : ZMod 120872598173) ^ 461092 = (2 : ZMod 120872598173) ^ (230546 + 230546) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 230546 * (2 : ZMod 120872598173) ^ 230546 := by rw [pow_add]
          _ = 90632936012 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 120872598173) ^ 922184 = 54643964442 := by
        calc
          (2 : ZMod 120872598173) ^ 922184 = (2 : ZMod 120872598173) ^ (461092 + 461092) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 461092 * (2 : ZMod 120872598173) ^ 461092 := by rw [pow_add]
          _ = 54643964442 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 120872598173) ^ 1844369 = 115130290603 := by
        calc
          (2 : ZMod 120872598173) ^ 1844369 = (2 : ZMod 120872598173) ^ (922184 + 922184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 922184 * (2 : ZMod 120872598173) ^ 922184) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 115130290603 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 120872598173) ^ 3688738 = 76030681375 := by
        calc
          (2 : ZMod 120872598173) ^ 3688738 = (2 : ZMod 120872598173) ^ (1844369 + 1844369) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 1844369 * (2 : ZMod 120872598173) ^ 1844369 := by rw [pow_add]
          _ = 76030681375 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 120872598173) ^ 7377477 = 73401725532 := by
        calc
          (2 : ZMod 120872598173) ^ 7377477 = (2 : ZMod 120872598173) ^ (3688738 + 3688738 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 3688738 * (2 : ZMod 120872598173) ^ 3688738) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 73401725532 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 120872598173) ^ 14754955 = 73964942644 := by
        calc
          (2 : ZMod 120872598173) ^ 14754955 = (2 : ZMod 120872598173) ^ (7377477 + 7377477 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 7377477 * (2 : ZMod 120872598173) ^ 7377477) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 73964942644 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 120872598173) ^ 29509911 = 86836409598 := by
        calc
          (2 : ZMod 120872598173) ^ 29509911 = (2 : ZMod 120872598173) ^ (14754955 + 14754955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 14754955 * (2 : ZMod 120872598173) ^ 14754955) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 86836409598 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 120872598173) ^ 59019823 = 86476822934 := by
        calc
          (2 : ZMod 120872598173) ^ 59019823 = (2 : ZMod 120872598173) ^ (29509911 + 29509911 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 29509911 * (2 : ZMod 120872598173) ^ 29509911) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 86476822934 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 120872598173) ^ 118039646 = 84836915449 := by
        calc
          (2 : ZMod 120872598173) ^ 118039646 = (2 : ZMod 120872598173) ^ (59019823 + 59019823) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 59019823 * (2 : ZMod 120872598173) ^ 59019823 := by rw [pow_add]
          _ = 84836915449 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 120872598173) ^ 236079293 = 57708446886 := by
        calc
          (2 : ZMod 120872598173) ^ 236079293 = (2 : ZMod 120872598173) ^ (118039646 + 118039646 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 118039646 * (2 : ZMod 120872598173) ^ 118039646) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 57708446886 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 120872598173) ^ 472158586 = 94448198015 := by
        calc
          (2 : ZMod 120872598173) ^ 472158586 = (2 : ZMod 120872598173) ^ (236079293 + 236079293) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 236079293 * (2 : ZMod 120872598173) ^ 236079293 := by rw [pow_add]
          _ = 94448198015 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 120872598173) ^ 944317173 = 52133187948 := by
        calc
          (2 : ZMod 120872598173) ^ 944317173 = (2 : ZMod 120872598173) ^ (472158586 + 472158586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 472158586 * (2 : ZMod 120872598173) ^ 472158586) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 52133187948 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 120872598173) ^ 1888634346 = 11578015680 := by
        calc
          (2 : ZMod 120872598173) ^ 1888634346 = (2 : ZMod 120872598173) ^ (944317173 + 944317173) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 944317173 * (2 : ZMod 120872598173) ^ 944317173 := by rw [pow_add]
          _ = 11578015680 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 120872598173) ^ 3777268692 = 2954412891 := by
        calc
          (2 : ZMod 120872598173) ^ 3777268692 = (2 : ZMod 120872598173) ^ (1888634346 + 1888634346) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 1888634346 * (2 : ZMod 120872598173) ^ 1888634346 := by rw [pow_add]
          _ = 2954412891 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 120872598173) ^ 7554537385 = 8588531586 := by
        calc
          (2 : ZMod 120872598173) ^ 7554537385 = (2 : ZMod 120872598173) ^ (3777268692 + 3777268692 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 3777268692 * (2 : ZMod 120872598173) ^ 3777268692) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 8588531586 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 120872598173) ^ 15109074771 = 49941488669 := by
        calc
          (2 : ZMod 120872598173) ^ 15109074771 = (2 : ZMod 120872598173) ^ (7554537385 + 7554537385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 7554537385 * (2 : ZMod 120872598173) ^ 7554537385) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 49941488669 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 120872598173) ^ 30218149543 = 20989620834 := by
        calc
          (2 : ZMod 120872598173) ^ 30218149543 = (2 : ZMod 120872598173) ^ (15109074771 + 15109074771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 15109074771 * (2 : ZMod 120872598173) ^ 15109074771) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 20989620834 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 120872598173) ^ 60436299086 = 120872598172 := by
        calc
          (2 : ZMod 120872598173) ^ 60436299086 = (2 : ZMod 120872598173) ^ (30218149543 + 30218149543) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 30218149543 * (2 : ZMod 120872598173) ^ 30218149543 := by rw [pow_add]
          _ = 120872598172 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 120872598173) ^ 120872598172 = 1 := by
        calc
          (2 : ZMod 120872598173) ^ 120872598172 = (2 : ZMod 120872598173) ^ (60436299086 + 60436299086) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 60436299086 * (2 : ZMod 120872598173) ^ 60436299086 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (30218149543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (30218149543, 1)] : List FactorBlock).map factorBlockValue).prod = 120872598173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_30218149543) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 120872598173) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 120872598173) ^ 3 = 8 := by
        calc
          (2 : ZMod 120872598173) ^ 3 = (2 : ZMod 120872598173) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 1 * (2 : ZMod 120872598173) ^ 1) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 120872598173) ^ 7 = 128 := by
        calc
          (2 : ZMod 120872598173) ^ 7 = (2 : ZMod 120872598173) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 3 * (2 : ZMod 120872598173) ^ 3) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 120872598173) ^ 14 = 16384 := by
        calc
          (2 : ZMod 120872598173) ^ 14 = (2 : ZMod 120872598173) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 7 * (2 : ZMod 120872598173) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 120872598173) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 120872598173) ^ 28 = (2 : ZMod 120872598173) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 14 * (2 : ZMod 120872598173) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 120872598173) ^ 56 = 119872683024 := by
        calc
          (2 : ZMod 120872598173) ^ 56 = (2 : ZMod 120872598173) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 28 * (2 : ZMod 120872598173) ^ 28 := by rw [pow_add]
          _ = 119872683024 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 120872598173) ^ 112 = 94682814164 := by
        calc
          (2 : ZMod 120872598173) ^ 112 = (2 : ZMod 120872598173) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 56 * (2 : ZMod 120872598173) ^ 56 := by rw [pow_add]
          _ = 94682814164 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 120872598173) ^ 225 = 99969510614 := by
        calc
          (2 : ZMod 120872598173) ^ 225 = (2 : ZMod 120872598173) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 112 * (2 : ZMod 120872598173) ^ 112) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 99969510614 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 120872598173) ^ 450 = 43479015140 := by
        calc
          (2 : ZMod 120872598173) ^ 450 = (2 : ZMod 120872598173) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 225 * (2 : ZMod 120872598173) ^ 225 := by rw [pow_add]
          _ = 43479015140 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 120872598173) ^ 900 = 114625839687 := by
        calc
          (2 : ZMod 120872598173) ^ 900 = (2 : ZMod 120872598173) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 450 * (2 : ZMod 120872598173) ^ 450 := by rw [pow_add]
          _ = 114625839687 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 120872598173) ^ 1801 = 96394923348 := by
        calc
          (2 : ZMod 120872598173) ^ 1801 = (2 : ZMod 120872598173) ^ (900 + 900 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 900 * (2 : ZMod 120872598173) ^ 900) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 96394923348 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 120872598173) ^ 3602 = 16567391016 := by
        calc
          (2 : ZMod 120872598173) ^ 3602 = (2 : ZMod 120872598173) ^ (1801 + 1801) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 1801 * (2 : ZMod 120872598173) ^ 1801 := by rw [pow_add]
          _ = 16567391016 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 120872598173) ^ 7204 = 54148257860 := by
        calc
          (2 : ZMod 120872598173) ^ 7204 = (2 : ZMod 120872598173) ^ (3602 + 3602) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 3602 * (2 : ZMod 120872598173) ^ 3602 := by rw [pow_add]
          _ = 54148257860 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 120872598173) ^ 14409 = 37135284705 := by
        calc
          (2 : ZMod 120872598173) ^ 14409 = (2 : ZMod 120872598173) ^ (7204 + 7204 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 7204 * (2 : ZMod 120872598173) ^ 7204) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 37135284705 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 120872598173) ^ 28818 = 60513897276 := by
        calc
          (2 : ZMod 120872598173) ^ 28818 = (2 : ZMod 120872598173) ^ (14409 + 14409) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 14409 * (2 : ZMod 120872598173) ^ 14409 := by rw [pow_add]
          _ = 60513897276 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 120872598173) ^ 57636 = 59444942199 := by
        calc
          (2 : ZMod 120872598173) ^ 57636 = (2 : ZMod 120872598173) ^ (28818 + 28818) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 28818 * (2 : ZMod 120872598173) ^ 28818 := by rw [pow_add]
          _ = 59444942199 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 120872598173) ^ 115273 = 9677544519 := by
        calc
          (2 : ZMod 120872598173) ^ 115273 = (2 : ZMod 120872598173) ^ (57636 + 57636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 57636 * (2 : ZMod 120872598173) ^ 57636) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 9677544519 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 120872598173) ^ 230546 = 112627142264 := by
        calc
          (2 : ZMod 120872598173) ^ 230546 = (2 : ZMod 120872598173) ^ (115273 + 115273) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 115273 * (2 : ZMod 120872598173) ^ 115273 := by rw [pow_add]
          _ = 112627142264 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 120872598173) ^ 461092 = 90632936012 := by
        calc
          (2 : ZMod 120872598173) ^ 461092 = (2 : ZMod 120872598173) ^ (230546 + 230546) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 230546 * (2 : ZMod 120872598173) ^ 230546 := by rw [pow_add]
          _ = 90632936012 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 120872598173) ^ 922184 = 54643964442 := by
        calc
          (2 : ZMod 120872598173) ^ 922184 = (2 : ZMod 120872598173) ^ (461092 + 461092) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 461092 * (2 : ZMod 120872598173) ^ 461092 := by rw [pow_add]
          _ = 54643964442 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 120872598173) ^ 1844369 = 115130290603 := by
        calc
          (2 : ZMod 120872598173) ^ 1844369 = (2 : ZMod 120872598173) ^ (922184 + 922184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 922184 * (2 : ZMod 120872598173) ^ 922184) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 115130290603 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 120872598173) ^ 3688738 = 76030681375 := by
        calc
          (2 : ZMod 120872598173) ^ 3688738 = (2 : ZMod 120872598173) ^ (1844369 + 1844369) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 1844369 * (2 : ZMod 120872598173) ^ 1844369 := by rw [pow_add]
          _ = 76030681375 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 120872598173) ^ 7377477 = 73401725532 := by
        calc
          (2 : ZMod 120872598173) ^ 7377477 = (2 : ZMod 120872598173) ^ (3688738 + 3688738 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 3688738 * (2 : ZMod 120872598173) ^ 3688738) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 73401725532 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 120872598173) ^ 14754955 = 73964942644 := by
        calc
          (2 : ZMod 120872598173) ^ 14754955 = (2 : ZMod 120872598173) ^ (7377477 + 7377477 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 7377477 * (2 : ZMod 120872598173) ^ 7377477) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 73964942644 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 120872598173) ^ 29509911 = 86836409598 := by
        calc
          (2 : ZMod 120872598173) ^ 29509911 = (2 : ZMod 120872598173) ^ (14754955 + 14754955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 14754955 * (2 : ZMod 120872598173) ^ 14754955) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 86836409598 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 120872598173) ^ 59019823 = 86476822934 := by
        calc
          (2 : ZMod 120872598173) ^ 59019823 = (2 : ZMod 120872598173) ^ (29509911 + 29509911 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 29509911 * (2 : ZMod 120872598173) ^ 29509911) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 86476822934 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 120872598173) ^ 118039646 = 84836915449 := by
        calc
          (2 : ZMod 120872598173) ^ 118039646 = (2 : ZMod 120872598173) ^ (59019823 + 59019823) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 59019823 * (2 : ZMod 120872598173) ^ 59019823 := by rw [pow_add]
          _ = 84836915449 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 120872598173) ^ 236079293 = 57708446886 := by
        calc
          (2 : ZMod 120872598173) ^ 236079293 = (2 : ZMod 120872598173) ^ (118039646 + 118039646 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 118039646 * (2 : ZMod 120872598173) ^ 118039646) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 57708446886 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 120872598173) ^ 472158586 = 94448198015 := by
        calc
          (2 : ZMod 120872598173) ^ 472158586 = (2 : ZMod 120872598173) ^ (236079293 + 236079293) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 236079293 * (2 : ZMod 120872598173) ^ 236079293 := by rw [pow_add]
          _ = 94448198015 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 120872598173) ^ 944317173 = 52133187948 := by
        calc
          (2 : ZMod 120872598173) ^ 944317173 = (2 : ZMod 120872598173) ^ (472158586 + 472158586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 472158586 * (2 : ZMod 120872598173) ^ 472158586) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 52133187948 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 120872598173) ^ 1888634346 = 11578015680 := by
        calc
          (2 : ZMod 120872598173) ^ 1888634346 = (2 : ZMod 120872598173) ^ (944317173 + 944317173) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 944317173 * (2 : ZMod 120872598173) ^ 944317173 := by rw [pow_add]
          _ = 11578015680 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 120872598173) ^ 3777268692 = 2954412891 := by
        calc
          (2 : ZMod 120872598173) ^ 3777268692 = (2 : ZMod 120872598173) ^ (1888634346 + 1888634346) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 1888634346 * (2 : ZMod 120872598173) ^ 1888634346 := by rw [pow_add]
          _ = 2954412891 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 120872598173) ^ 7554537385 = 8588531586 := by
        calc
          (2 : ZMod 120872598173) ^ 7554537385 = (2 : ZMod 120872598173) ^ (3777268692 + 3777268692 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 3777268692 * (2 : ZMod 120872598173) ^ 3777268692) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 8588531586 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 120872598173) ^ 15109074771 = 49941488669 := by
        calc
          (2 : ZMod 120872598173) ^ 15109074771 = (2 : ZMod 120872598173) ^ (7554537385 + 7554537385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 7554537385 * (2 : ZMod 120872598173) ^ 7554537385) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 49941488669 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 120872598173) ^ 30218149543 = 20989620834 := by
        calc
          (2 : ZMod 120872598173) ^ 30218149543 = (2 : ZMod 120872598173) ^ (15109074771 + 15109074771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = ((2 : ZMod 120872598173) ^ 15109074771 * (2 : ZMod 120872598173) ^ 15109074771) * (2 : ZMod 120872598173) := by rw [pow_succ, pow_add]
          _ = 20989620834 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 120872598173) ^ 60436299086 = 120872598172 := by
        calc
          (2 : ZMod 120872598173) ^ 60436299086 = (2 : ZMod 120872598173) ^ (30218149543 + 30218149543) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 30218149543 * (2 : ZMod 120872598173) ^ 30218149543 := by rw [pow_add]
          _ = 120872598172 := by rw [factor_0_34]; decide
      change (2 : ZMod 120872598173) ^ 60436299086 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (2 : ZMod 120872598173) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 120872598173) ^ 2 = 4 := by
        calc
          (2 : ZMod 120872598173) ^ 2 = (2 : ZMod 120872598173) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 1 * (2 : ZMod 120872598173) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 120872598173) ^ 4 = 16 := by
        calc
          (2 : ZMod 120872598173) ^ 4 = (2 : ZMod 120872598173) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 120872598173) ^ n) (by norm_num)
          _ = (2 : ZMod 120872598173) ^ 2 * (2 : ZMod 120872598173) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      change (2 : ZMod 120872598173) ^ 4 ≠ 1
      rw [factor_1_2]
      decide

#print axioms prime_lucas_120872598173

end TotientTailPeriodKiller
end Erdos249257
