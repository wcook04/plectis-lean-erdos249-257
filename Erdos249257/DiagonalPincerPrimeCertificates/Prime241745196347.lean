import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime120872598173

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_241745196347 : Nat.Prime 241745196347 := by
  apply lucas_primality 241745196347 (2 : ZMod 241745196347)
  ·
      have fermat_0 : (2 : ZMod 241745196347) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 241745196347) ^ 3 = 8 := by
        calc
          (2 : ZMod 241745196347) ^ 3 = (2 : ZMod 241745196347) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 1 * (2 : ZMod 241745196347) ^ 1) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 241745196347) ^ 7 = 128 := by
        calc
          (2 : ZMod 241745196347) ^ 7 = (2 : ZMod 241745196347) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 3 * (2 : ZMod 241745196347) ^ 3) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 241745196347) ^ 14 = 16384 := by
        calc
          (2 : ZMod 241745196347) ^ 14 = (2 : ZMod 241745196347) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 7 * (2 : ZMod 241745196347) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 241745196347) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 241745196347) ^ 28 = (2 : ZMod 241745196347) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 14 * (2 : ZMod 241745196347) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 241745196347) ^ 56 = 119872384952 := by
        calc
          (2 : ZMod 241745196347) ^ 56 = (2 : ZMod 241745196347) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 28 * (2 : ZMod 241745196347) ^ 28 := by rw [pow_add]
          _ = 119872384952 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 241745196347) ^ 112 = 73851903352 := by
        calc
          (2 : ZMod 241745196347) ^ 112 = (2 : ZMod 241745196347) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 56 * (2 : ZMod 241745196347) ^ 56 := by rw [pow_add]
          _ = 73851903352 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 241745196347) ^ 225 = 103284115766 := by
        calc
          (2 : ZMod 241745196347) ^ 225 = (2 : ZMod 241745196347) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 112 * (2 : ZMod 241745196347) ^ 112) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 103284115766 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 241745196347) ^ 450 = 84434645410 := by
        calc
          (2 : ZMod 241745196347) ^ 450 = (2 : ZMod 241745196347) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 225 * (2 : ZMod 241745196347) ^ 225 := by rw [pow_add]
          _ = 84434645410 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 241745196347) ^ 900 = 214203365613 := by
        calc
          (2 : ZMod 241745196347) ^ 900 = (2 : ZMod 241745196347) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 450 * (2 : ZMod 241745196347) ^ 450 := by rw [pow_add]
          _ = 214203365613 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 241745196347) ^ 1801 = 130773416200 := by
        calc
          (2 : ZMod 241745196347) ^ 1801 = (2 : ZMod 241745196347) ^ (900 + 900 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 900 * (2 : ZMod 241745196347) ^ 900) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 130773416200 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 241745196347) ^ 3602 = 16196797429 := by
        calc
          (2 : ZMod 241745196347) ^ 3602 = (2 : ZMod 241745196347) ^ (1801 + 1801) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 1801 * (2 : ZMod 241745196347) ^ 1801 := by rw [pow_add]
          _ = 16196797429 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 241745196347) ^ 7204 = 37472581898 := by
        calc
          (2 : ZMod 241745196347) ^ 7204 = (2 : ZMod 241745196347) ^ (3602 + 3602) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 3602 * (2 : ZMod 241745196347) ^ 3602 := by rw [pow_add]
          _ = 37472581898 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 241745196347) ^ 14409 = 231621660739 := by
        calc
          (2 : ZMod 241745196347) ^ 14409 = (2 : ZMod 241745196347) ^ (7204 + 7204 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 7204 * (2 : ZMod 241745196347) ^ 7204) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 231621660739 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 241745196347) ^ 28818 = 233318923248 := by
        calc
          (2 : ZMod 241745196347) ^ 28818 = (2 : ZMod 241745196347) ^ (14409 + 14409) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 14409 * (2 : ZMod 241745196347) ^ 14409 := by rw [pow_add]
          _ = 233318923248 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 241745196347) ^ 57636 = 121652442540 := by
        calc
          (2 : ZMod 241745196347) ^ 57636 = (2 : ZMod 241745196347) ^ (28818 + 28818) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 28818 * (2 : ZMod 241745196347) ^ 28818 := by rw [pow_add]
          _ = 121652442540 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 241745196347) ^ 115273 = 229347838488 := by
        calc
          (2 : ZMod 241745196347) ^ 115273 = (2 : ZMod 241745196347) ^ (57636 + 57636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 57636 * (2 : ZMod 241745196347) ^ 57636) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 229347838488 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 241745196347) ^ 230546 = 124324563397 := by
        calc
          (2 : ZMod 241745196347) ^ 230546 = (2 : ZMod 241745196347) ^ (115273 + 115273) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 115273 * (2 : ZMod 241745196347) ^ 115273 := by rw [pow_add]
          _ = 124324563397 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 241745196347) ^ 461092 = 117801169988 := by
        calc
          (2 : ZMod 241745196347) ^ 461092 = (2 : ZMod 241745196347) ^ (230546 + 230546) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 230546 * (2 : ZMod 241745196347) ^ 230546 := by rw [pow_add]
          _ = 117801169988 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 241745196347) ^ 922184 = 13031871097 := by
        calc
          (2 : ZMod 241745196347) ^ 922184 = (2 : ZMod 241745196347) ^ (461092 + 461092) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 461092 * (2 : ZMod 241745196347) ^ 461092 := by rw [pow_add]
          _ = 13031871097 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 241745196347) ^ 1844369 = 171466492901 := by
        calc
          (2 : ZMod 241745196347) ^ 1844369 = (2 : ZMod 241745196347) ^ (922184 + 922184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 922184 * (2 : ZMod 241745196347) ^ 922184) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 171466492901 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 241745196347) ^ 3688738 = 235273649352 := by
        calc
          (2 : ZMod 241745196347) ^ 3688738 = (2 : ZMod 241745196347) ^ (1844369 + 1844369) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 1844369 * (2 : ZMod 241745196347) ^ 1844369 := by rw [pow_add]
          _ = 235273649352 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 241745196347) ^ 7377477 = 239977395287 := by
        calc
          (2 : ZMod 241745196347) ^ 7377477 = (2 : ZMod 241745196347) ^ (3688738 + 3688738 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 3688738 * (2 : ZMod 241745196347) ^ 3688738) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 239977395287 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 241745196347) ^ 14754955 = 108563338445 := by
        calc
          (2 : ZMod 241745196347) ^ 14754955 = (2 : ZMod 241745196347) ^ (7377477 + 7377477 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 7377477 * (2 : ZMod 241745196347) ^ 7377477) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 108563338445 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 241745196347) ^ 29509911 = 55880188045 := by
        calc
          (2 : ZMod 241745196347) ^ 29509911 = (2 : ZMod 241745196347) ^ (14754955 + 14754955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 14754955 * (2 : ZMod 241745196347) ^ 14754955) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 55880188045 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 241745196347) ^ 59019823 = 54366430442 := by
        calc
          (2 : ZMod 241745196347) ^ 59019823 = (2 : ZMod 241745196347) ^ (29509911 + 29509911 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 29509911 * (2 : ZMod 241745196347) ^ 29509911) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 54366430442 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 241745196347) ^ 118039646 = 182355583957 := by
        calc
          (2 : ZMod 241745196347) ^ 118039646 = (2 : ZMod 241745196347) ^ (59019823 + 59019823) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 59019823 * (2 : ZMod 241745196347) ^ 59019823 := by rw [pow_add]
          _ = 182355583957 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 241745196347) ^ 236079293 = 55522100391 := by
        calc
          (2 : ZMod 241745196347) ^ 236079293 = (2 : ZMod 241745196347) ^ (118039646 + 118039646 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 118039646 * (2 : ZMod 241745196347) ^ 118039646) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 55522100391 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 241745196347) ^ 472158586 = 134617819087 := by
        calc
          (2 : ZMod 241745196347) ^ 472158586 = (2 : ZMod 241745196347) ^ (236079293 + 236079293) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 236079293 * (2 : ZMod 241745196347) ^ 236079293 := by rw [pow_add]
          _ = 134617819087 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 241745196347) ^ 944317173 = 207057560008 := by
        calc
          (2 : ZMod 241745196347) ^ 944317173 = (2 : ZMod 241745196347) ^ (472158586 + 472158586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 472158586 * (2 : ZMod 241745196347) ^ 472158586) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 207057560008 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 241745196347) ^ 1888634346 = 56077363647 := by
        calc
          (2 : ZMod 241745196347) ^ 1888634346 = (2 : ZMod 241745196347) ^ (944317173 + 944317173) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 944317173 * (2 : ZMod 241745196347) ^ 944317173 := by rw [pow_add]
          _ = 56077363647 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 241745196347) ^ 3777268692 = 17230991863 := by
        calc
          (2 : ZMod 241745196347) ^ 3777268692 = (2 : ZMod 241745196347) ^ (1888634346 + 1888634346) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 1888634346 * (2 : ZMod 241745196347) ^ 1888634346 := by rw [pow_add]
          _ = 17230991863 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 241745196347) ^ 7554537385 = 189366761935 := by
        calc
          (2 : ZMod 241745196347) ^ 7554537385 = (2 : ZMod 241745196347) ^ (3777268692 + 3777268692 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 3777268692 * (2 : ZMod 241745196347) ^ 3777268692) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 189366761935 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 241745196347) ^ 15109074771 = 147010102022 := by
        calc
          (2 : ZMod 241745196347) ^ 15109074771 = (2 : ZMod 241745196347) ^ (7554537385 + 7554537385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 7554537385 * (2 : ZMod 241745196347) ^ 7554537385) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 147010102022 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 241745196347) ^ 30218149543 = 67114872301 := by
        calc
          (2 : ZMod 241745196347) ^ 30218149543 = (2 : ZMod 241745196347) ^ (15109074771 + 15109074771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 15109074771 * (2 : ZMod 241745196347) ^ 15109074771) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 67114872301 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 241745196347) ^ 60436299086 = 51101272358 := by
        calc
          (2 : ZMod 241745196347) ^ 60436299086 = (2 : ZMod 241745196347) ^ (30218149543 + 30218149543) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 30218149543 * (2 : ZMod 241745196347) ^ 30218149543 := by rw [pow_add]
          _ = 51101272358 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 241745196347) ^ 120872598173 = 241745196346 := by
        calc
          (2 : ZMod 241745196347) ^ 120872598173 = (2 : ZMod 241745196347) ^ (60436299086 + 60436299086 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 60436299086 * (2 : ZMod 241745196347) ^ 60436299086) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 241745196346 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 241745196347) ^ 241745196346 = 1 := by
        calc
          (2 : ZMod 241745196347) ^ 241745196346 = (2 : ZMod 241745196347) ^ (120872598173 + 120872598173) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 120872598173 * (2 : ZMod 241745196347) ^ 120872598173 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (120872598173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (120872598173, 1)] : List FactorBlock).map factorBlockValue).prod = 241745196347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_120872598173) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 241745196347) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 241745196347) ^ 3 = 8 := by
        calc
          (2 : ZMod 241745196347) ^ 3 = (2 : ZMod 241745196347) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 1 * (2 : ZMod 241745196347) ^ 1) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 241745196347) ^ 7 = 128 := by
        calc
          (2 : ZMod 241745196347) ^ 7 = (2 : ZMod 241745196347) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 3 * (2 : ZMod 241745196347) ^ 3) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 241745196347) ^ 14 = 16384 := by
        calc
          (2 : ZMod 241745196347) ^ 14 = (2 : ZMod 241745196347) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 7 * (2 : ZMod 241745196347) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 241745196347) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 241745196347) ^ 28 = (2 : ZMod 241745196347) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 14 * (2 : ZMod 241745196347) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 241745196347) ^ 56 = 119872384952 := by
        calc
          (2 : ZMod 241745196347) ^ 56 = (2 : ZMod 241745196347) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 28 * (2 : ZMod 241745196347) ^ 28 := by rw [pow_add]
          _ = 119872384952 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 241745196347) ^ 112 = 73851903352 := by
        calc
          (2 : ZMod 241745196347) ^ 112 = (2 : ZMod 241745196347) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 56 * (2 : ZMod 241745196347) ^ 56 := by rw [pow_add]
          _ = 73851903352 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 241745196347) ^ 225 = 103284115766 := by
        calc
          (2 : ZMod 241745196347) ^ 225 = (2 : ZMod 241745196347) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 112 * (2 : ZMod 241745196347) ^ 112) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 103284115766 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 241745196347) ^ 450 = 84434645410 := by
        calc
          (2 : ZMod 241745196347) ^ 450 = (2 : ZMod 241745196347) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 225 * (2 : ZMod 241745196347) ^ 225 := by rw [pow_add]
          _ = 84434645410 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 241745196347) ^ 900 = 214203365613 := by
        calc
          (2 : ZMod 241745196347) ^ 900 = (2 : ZMod 241745196347) ^ (450 + 450) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 450 * (2 : ZMod 241745196347) ^ 450 := by rw [pow_add]
          _ = 214203365613 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 241745196347) ^ 1801 = 130773416200 := by
        calc
          (2 : ZMod 241745196347) ^ 1801 = (2 : ZMod 241745196347) ^ (900 + 900 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 900 * (2 : ZMod 241745196347) ^ 900) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 130773416200 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 241745196347) ^ 3602 = 16196797429 := by
        calc
          (2 : ZMod 241745196347) ^ 3602 = (2 : ZMod 241745196347) ^ (1801 + 1801) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 1801 * (2 : ZMod 241745196347) ^ 1801 := by rw [pow_add]
          _ = 16196797429 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 241745196347) ^ 7204 = 37472581898 := by
        calc
          (2 : ZMod 241745196347) ^ 7204 = (2 : ZMod 241745196347) ^ (3602 + 3602) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 3602 * (2 : ZMod 241745196347) ^ 3602 := by rw [pow_add]
          _ = 37472581898 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 241745196347) ^ 14409 = 231621660739 := by
        calc
          (2 : ZMod 241745196347) ^ 14409 = (2 : ZMod 241745196347) ^ (7204 + 7204 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 7204 * (2 : ZMod 241745196347) ^ 7204) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 231621660739 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 241745196347) ^ 28818 = 233318923248 := by
        calc
          (2 : ZMod 241745196347) ^ 28818 = (2 : ZMod 241745196347) ^ (14409 + 14409) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 14409 * (2 : ZMod 241745196347) ^ 14409 := by rw [pow_add]
          _ = 233318923248 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 241745196347) ^ 57636 = 121652442540 := by
        calc
          (2 : ZMod 241745196347) ^ 57636 = (2 : ZMod 241745196347) ^ (28818 + 28818) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 28818 * (2 : ZMod 241745196347) ^ 28818 := by rw [pow_add]
          _ = 121652442540 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 241745196347) ^ 115273 = 229347838488 := by
        calc
          (2 : ZMod 241745196347) ^ 115273 = (2 : ZMod 241745196347) ^ (57636 + 57636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 57636 * (2 : ZMod 241745196347) ^ 57636) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 229347838488 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 241745196347) ^ 230546 = 124324563397 := by
        calc
          (2 : ZMod 241745196347) ^ 230546 = (2 : ZMod 241745196347) ^ (115273 + 115273) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 115273 * (2 : ZMod 241745196347) ^ 115273 := by rw [pow_add]
          _ = 124324563397 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 241745196347) ^ 461092 = 117801169988 := by
        calc
          (2 : ZMod 241745196347) ^ 461092 = (2 : ZMod 241745196347) ^ (230546 + 230546) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 230546 * (2 : ZMod 241745196347) ^ 230546 := by rw [pow_add]
          _ = 117801169988 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 241745196347) ^ 922184 = 13031871097 := by
        calc
          (2 : ZMod 241745196347) ^ 922184 = (2 : ZMod 241745196347) ^ (461092 + 461092) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 461092 * (2 : ZMod 241745196347) ^ 461092 := by rw [pow_add]
          _ = 13031871097 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 241745196347) ^ 1844369 = 171466492901 := by
        calc
          (2 : ZMod 241745196347) ^ 1844369 = (2 : ZMod 241745196347) ^ (922184 + 922184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 922184 * (2 : ZMod 241745196347) ^ 922184) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 171466492901 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 241745196347) ^ 3688738 = 235273649352 := by
        calc
          (2 : ZMod 241745196347) ^ 3688738 = (2 : ZMod 241745196347) ^ (1844369 + 1844369) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 1844369 * (2 : ZMod 241745196347) ^ 1844369 := by rw [pow_add]
          _ = 235273649352 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 241745196347) ^ 7377477 = 239977395287 := by
        calc
          (2 : ZMod 241745196347) ^ 7377477 = (2 : ZMod 241745196347) ^ (3688738 + 3688738 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 3688738 * (2 : ZMod 241745196347) ^ 3688738) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 239977395287 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 241745196347) ^ 14754955 = 108563338445 := by
        calc
          (2 : ZMod 241745196347) ^ 14754955 = (2 : ZMod 241745196347) ^ (7377477 + 7377477 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 7377477 * (2 : ZMod 241745196347) ^ 7377477) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 108563338445 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 241745196347) ^ 29509911 = 55880188045 := by
        calc
          (2 : ZMod 241745196347) ^ 29509911 = (2 : ZMod 241745196347) ^ (14754955 + 14754955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 14754955 * (2 : ZMod 241745196347) ^ 14754955) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 55880188045 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 241745196347) ^ 59019823 = 54366430442 := by
        calc
          (2 : ZMod 241745196347) ^ 59019823 = (2 : ZMod 241745196347) ^ (29509911 + 29509911 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 29509911 * (2 : ZMod 241745196347) ^ 29509911) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 54366430442 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 241745196347) ^ 118039646 = 182355583957 := by
        calc
          (2 : ZMod 241745196347) ^ 118039646 = (2 : ZMod 241745196347) ^ (59019823 + 59019823) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 59019823 * (2 : ZMod 241745196347) ^ 59019823 := by rw [pow_add]
          _ = 182355583957 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 241745196347) ^ 236079293 = 55522100391 := by
        calc
          (2 : ZMod 241745196347) ^ 236079293 = (2 : ZMod 241745196347) ^ (118039646 + 118039646 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 118039646 * (2 : ZMod 241745196347) ^ 118039646) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 55522100391 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 241745196347) ^ 472158586 = 134617819087 := by
        calc
          (2 : ZMod 241745196347) ^ 472158586 = (2 : ZMod 241745196347) ^ (236079293 + 236079293) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 236079293 * (2 : ZMod 241745196347) ^ 236079293 := by rw [pow_add]
          _ = 134617819087 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 241745196347) ^ 944317173 = 207057560008 := by
        calc
          (2 : ZMod 241745196347) ^ 944317173 = (2 : ZMod 241745196347) ^ (472158586 + 472158586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 472158586 * (2 : ZMod 241745196347) ^ 472158586) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 207057560008 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 241745196347) ^ 1888634346 = 56077363647 := by
        calc
          (2 : ZMod 241745196347) ^ 1888634346 = (2 : ZMod 241745196347) ^ (944317173 + 944317173) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 944317173 * (2 : ZMod 241745196347) ^ 944317173 := by rw [pow_add]
          _ = 56077363647 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 241745196347) ^ 3777268692 = 17230991863 := by
        calc
          (2 : ZMod 241745196347) ^ 3777268692 = (2 : ZMod 241745196347) ^ (1888634346 + 1888634346) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 1888634346 * (2 : ZMod 241745196347) ^ 1888634346 := by rw [pow_add]
          _ = 17230991863 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 241745196347) ^ 7554537385 = 189366761935 := by
        calc
          (2 : ZMod 241745196347) ^ 7554537385 = (2 : ZMod 241745196347) ^ (3777268692 + 3777268692 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 3777268692 * (2 : ZMod 241745196347) ^ 3777268692) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 189366761935 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 241745196347) ^ 15109074771 = 147010102022 := by
        calc
          (2 : ZMod 241745196347) ^ 15109074771 = (2 : ZMod 241745196347) ^ (7554537385 + 7554537385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 7554537385 * (2 : ZMod 241745196347) ^ 7554537385) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 147010102022 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 241745196347) ^ 30218149543 = 67114872301 := by
        calc
          (2 : ZMod 241745196347) ^ 30218149543 = (2 : ZMod 241745196347) ^ (15109074771 + 15109074771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 15109074771 * (2 : ZMod 241745196347) ^ 15109074771) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 67114872301 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 241745196347) ^ 60436299086 = 51101272358 := by
        calc
          (2 : ZMod 241745196347) ^ 60436299086 = (2 : ZMod 241745196347) ^ (30218149543 + 30218149543) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 30218149543 * (2 : ZMod 241745196347) ^ 30218149543 := by rw [pow_add]
          _ = 51101272358 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 241745196347) ^ 120872598173 = 241745196346 := by
        calc
          (2 : ZMod 241745196347) ^ 120872598173 = (2 : ZMod 241745196347) ^ (60436299086 + 60436299086 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = ((2 : ZMod 241745196347) ^ 60436299086 * (2 : ZMod 241745196347) ^ 60436299086) * (2 : ZMod 241745196347) := by rw [pow_succ, pow_add]
          _ = 241745196346 := by rw [factor_0_35]; decide
      change (2 : ZMod 241745196347) ^ 120872598173 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (2 : ZMod 241745196347) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 241745196347) ^ 2 = 4 := by
        calc
          (2 : ZMod 241745196347) ^ 2 = (2 : ZMod 241745196347) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 241745196347) ^ n) (by norm_num)
          _ = (2 : ZMod 241745196347) ^ 1 * (2 : ZMod 241745196347) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      change (2 : ZMod 241745196347) ^ 2 ≠ 1
      rw [factor_1_1]
      decide

#print axioms prime_lucas_241745196347

end TotientTailPeriodKiller
end Erdos249257
