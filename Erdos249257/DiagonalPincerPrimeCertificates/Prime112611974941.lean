import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_112611974941 : Nat.Prime 112611974941 := by
  apply lucas_primality 112611974941 (6 : ZMod 112611974941)
  ·
      have fermat_0 : (6 : ZMod 112611974941) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 112611974941) ^ 3 = 216 := by
        calc
          (6 : ZMod 112611974941) ^ 3 = (6 : ZMod 112611974941) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1 * (6 : ZMod 112611974941) ^ 1) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 112611974941) ^ 6 = 46656 := by
        calc
          (6 : ZMod 112611974941) ^ 6 = (6 : ZMod 112611974941) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 3 * (6 : ZMod 112611974941) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 112611974941) ^ 13 = 13060694016 := by
        calc
          (6 : ZMod 112611974941) ^ 13 = (6 : ZMod 112611974941) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 6 * (6 : ZMod 112611974941) ^ 6) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 13060694016 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 112611974941) ^ 26 = 76631968313 := by
        calc
          (6 : ZMod 112611974941) ^ 26 = (6 : ZMod 112611974941) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 13 * (6 : ZMod 112611974941) ^ 13 := by rw [pow_add]
          _ = 76631968313 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 112611974941) ^ 52 = 41932155622 := by
        calc
          (6 : ZMod 112611974941) ^ 52 = (6 : ZMod 112611974941) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 26 * (6 : ZMod 112611974941) ^ 26 := by rw [pow_add]
          _ = 41932155622 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 112611974941) ^ 104 = 80417132556 := by
        calc
          (6 : ZMod 112611974941) ^ 104 = (6 : ZMod 112611974941) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 52 * (6 : ZMod 112611974941) ^ 52 := by rw [pow_add]
          _ = 80417132556 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 112611974941) ^ 209 = 12857593531 := by
        calc
          (6 : ZMod 112611974941) ^ 209 = (6 : ZMod 112611974941) ^ (104 + 104 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 104 * (6 : ZMod 112611974941) ^ 104) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 12857593531 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 112611974941) ^ 419 = 40119262626 := by
        calc
          (6 : ZMod 112611974941) ^ 419 = (6 : ZMod 112611974941) ^ (209 + 209 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 209 * (6 : ZMod 112611974941) ^ 209) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 40119262626 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 112611974941) ^ 839 = 53935538983 := by
        calc
          (6 : ZMod 112611974941) ^ 839 = (6 : ZMod 112611974941) ^ (419 + 419 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 419 * (6 : ZMod 112611974941) ^ 419) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 53935538983 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 112611974941) ^ 1678 = 51516805668 := by
        calc
          (6 : ZMod 112611974941) ^ 1678 = (6 : ZMod 112611974941) ^ (839 + 839) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 839 * (6 : ZMod 112611974941) ^ 839 := by rw [pow_add]
          _ = 51516805668 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 112611974941) ^ 3356 = 69996039829 := by
        calc
          (6 : ZMod 112611974941) ^ 3356 = (6 : ZMod 112611974941) ^ (1678 + 1678) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1678 * (6 : ZMod 112611974941) ^ 1678 := by rw [pow_add]
          _ = 69996039829 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 112611974941) ^ 6712 = 105386793926 := by
        calc
          (6 : ZMod 112611974941) ^ 6712 = (6 : ZMod 112611974941) ^ (3356 + 3356) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 3356 * (6 : ZMod 112611974941) ^ 3356 := by rw [pow_add]
          _ = 105386793926 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 112611974941) ^ 13424 = 42027956943 := by
        calc
          (6 : ZMod 112611974941) ^ 13424 = (6 : ZMod 112611974941) ^ (6712 + 6712) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 6712 * (6 : ZMod 112611974941) ^ 6712 := by rw [pow_add]
          _ = 42027956943 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 112611974941) ^ 26848 = 74415824908 := by
        calc
          (6 : ZMod 112611974941) ^ 26848 = (6 : ZMod 112611974941) ^ (13424 + 13424) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 13424 * (6 : ZMod 112611974941) ^ 13424 := by rw [pow_add]
          _ = 74415824908 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 112611974941) ^ 53697 = 29719670624 := by
        calc
          (6 : ZMod 112611974941) ^ 53697 = (6 : ZMod 112611974941) ^ (26848 + 26848 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 26848 * (6 : ZMod 112611974941) ^ 26848) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 29719670624 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 112611974941) ^ 107395 = 18469690700 := by
        calc
          (6 : ZMod 112611974941) ^ 107395 = (6 : ZMod 112611974941) ^ (53697 + 53697 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 53697 * (6 : ZMod 112611974941) ^ 53697) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 18469690700 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 112611974941) ^ 214790 = 24720231333 := by
        calc
          (6 : ZMod 112611974941) ^ 214790 = (6 : ZMod 112611974941) ^ (107395 + 107395) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 107395 * (6 : ZMod 112611974941) ^ 107395 := by rw [pow_add]
          _ = 24720231333 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 112611974941) ^ 429580 = 77538982268 := by
        calc
          (6 : ZMod 112611974941) ^ 429580 = (6 : ZMod 112611974941) ^ (214790 + 214790) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 214790 * (6 : ZMod 112611974941) ^ 214790 := by rw [pow_add]
          _ = 77538982268 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 112611974941) ^ 859161 = 22130329422 := by
        calc
          (6 : ZMod 112611974941) ^ 859161 = (6 : ZMod 112611974941) ^ (429580 + 429580 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 429580 * (6 : ZMod 112611974941) ^ 429580) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 22130329422 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 112611974941) ^ 1718322 = 80423177573 := by
        calc
          (6 : ZMod 112611974941) ^ 1718322 = (6 : ZMod 112611974941) ^ (859161 + 859161) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 859161 * (6 : ZMod 112611974941) ^ 859161 := by rw [pow_add]
          _ = 80423177573 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 112611974941) ^ 3436644 = 60154648002 := by
        calc
          (6 : ZMod 112611974941) ^ 3436644 = (6 : ZMod 112611974941) ^ (1718322 + 1718322) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1718322 * (6 : ZMod 112611974941) ^ 1718322 := by rw [pow_add]
          _ = 60154648002 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 112611974941) ^ 6873289 = 107701809925 := by
        calc
          (6 : ZMod 112611974941) ^ 6873289 = (6 : ZMod 112611974941) ^ (3436644 + 3436644 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 3436644 * (6 : ZMod 112611974941) ^ 3436644) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 107701809925 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 112611974941) ^ 13746578 = 25010166526 := by
        calc
          (6 : ZMod 112611974941) ^ 13746578 = (6 : ZMod 112611974941) ^ (6873289 + 6873289) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 6873289 * (6 : ZMod 112611974941) ^ 6873289 := by rw [pow_add]
          _ = 25010166526 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 112611974941) ^ 27493157 = 78785045088 := by
        calc
          (6 : ZMod 112611974941) ^ 27493157 = (6 : ZMod 112611974941) ^ (13746578 + 13746578 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 13746578 * (6 : ZMod 112611974941) ^ 13746578) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 78785045088 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 112611974941) ^ 54986315 = 98022617725 := by
        calc
          (6 : ZMod 112611974941) ^ 54986315 = (6 : ZMod 112611974941) ^ (27493157 + 27493157 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 27493157 * (6 : ZMod 112611974941) ^ 27493157) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 98022617725 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 112611974941) ^ 109972631 = 101383157453 := by
        calc
          (6 : ZMod 112611974941) ^ 109972631 = (6 : ZMod 112611974941) ^ (54986315 + 54986315 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 54986315 * (6 : ZMod 112611974941) ^ 54986315) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 101383157453 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 112611974941) ^ 219945263 = 74391738573 := by
        calc
          (6 : ZMod 112611974941) ^ 219945263 = (6 : ZMod 112611974941) ^ (109972631 + 109972631 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 109972631 * (6 : ZMod 112611974941) ^ 109972631) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 74391738573 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 112611974941) ^ 439890527 = 14325894027 := by
        calc
          (6 : ZMod 112611974941) ^ 439890527 = (6 : ZMod 112611974941) ^ (219945263 + 219945263 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 219945263 * (6 : ZMod 112611974941) ^ 219945263) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 14325894027 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 112611974941) ^ 879781054 = 4416836681 := by
        calc
          (6 : ZMod 112611974941) ^ 879781054 = (6 : ZMod 112611974941) ^ (439890527 + 439890527) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 439890527 * (6 : ZMod 112611974941) ^ 439890527 := by rw [pow_add]
          _ = 4416836681 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 112611974941) ^ 1759562108 = 90151593758 := by
        calc
          (6 : ZMod 112611974941) ^ 1759562108 = (6 : ZMod 112611974941) ^ (879781054 + 879781054) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 879781054 * (6 : ZMod 112611974941) ^ 879781054 := by rw [pow_add]
          _ = 90151593758 := by rw [fermat_29]; decide
      have fermat_31 : (6 : ZMod 112611974941) ^ 3519124216 = 76153854364 := by
        calc
          (6 : ZMod 112611974941) ^ 3519124216 = (6 : ZMod 112611974941) ^ (1759562108 + 1759562108) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1759562108 * (6 : ZMod 112611974941) ^ 1759562108 := by rw [pow_add]
          _ = 76153854364 := by rw [fermat_30]; decide
      have fermat_32 : (6 : ZMod 112611974941) ^ 7038248433 = 40616283391 := by
        calc
          (6 : ZMod 112611974941) ^ 7038248433 = (6 : ZMod 112611974941) ^ (3519124216 + 3519124216 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 3519124216 * (6 : ZMod 112611974941) ^ 3519124216) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 40616283391 := by rw [fermat_31]; decide
      have fermat_33 : (6 : ZMod 112611974941) ^ 14076496867 = 71979426708 := by
        calc
          (6 : ZMod 112611974941) ^ 14076496867 = (6 : ZMod 112611974941) ^ (7038248433 + 7038248433 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 7038248433 * (6 : ZMod 112611974941) ^ 7038248433) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 71979426708 := by rw [fermat_32]; decide
      have fermat_34 : (6 : ZMod 112611974941) ^ 28152993735 = 95830565489 := by
        calc
          (6 : ZMod 112611974941) ^ 28152993735 = (6 : ZMod 112611974941) ^ (14076496867 + 14076496867 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 14076496867 * (6 : ZMod 112611974941) ^ 14076496867) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 95830565489 := by rw [fermat_33]; decide
      have fermat_35 : (6 : ZMod 112611974941) ^ 56305987470 = 112611974940 := by
        calc
          (6 : ZMod 112611974941) ^ 56305987470 = (6 : ZMod 112611974941) ^ (28152993735 + 28152993735) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 28152993735 * (6 : ZMod 112611974941) ^ 28152993735 := by rw [pow_add]
          _ = 112611974940 := by rw [fermat_34]; decide
      have fermat_36 : (6 : ZMod 112611974941) ^ 112611974940 = 1 := by
        calc
          (6 : ZMod 112611974941) ^ 112611974940 = (6 : ZMod 112611974941) ^ (56305987470 + 56305987470) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 56305987470 * (6 : ZMod 112611974941) ^ 56305987470 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (17, 1), (373, 1), (98663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (17, 1), (373, 1), (98663, 1)] : List FactorBlock).map factorBlockValue).prod = 112611974941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 112611974941) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 112611974941) ^ 3 = 216 := by
        calc
          (6 : ZMod 112611974941) ^ 3 = (6 : ZMod 112611974941) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1 * (6 : ZMod 112611974941) ^ 1) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 112611974941) ^ 6 = 46656 := by
        calc
          (6 : ZMod 112611974941) ^ 6 = (6 : ZMod 112611974941) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 3 * (6 : ZMod 112611974941) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 112611974941) ^ 13 = 13060694016 := by
        calc
          (6 : ZMod 112611974941) ^ 13 = (6 : ZMod 112611974941) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 6 * (6 : ZMod 112611974941) ^ 6) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 13060694016 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 112611974941) ^ 26 = 76631968313 := by
        calc
          (6 : ZMod 112611974941) ^ 26 = (6 : ZMod 112611974941) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 13 * (6 : ZMod 112611974941) ^ 13 := by rw [pow_add]
          _ = 76631968313 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 112611974941) ^ 52 = 41932155622 := by
        calc
          (6 : ZMod 112611974941) ^ 52 = (6 : ZMod 112611974941) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 26 * (6 : ZMod 112611974941) ^ 26 := by rw [pow_add]
          _ = 41932155622 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 112611974941) ^ 104 = 80417132556 := by
        calc
          (6 : ZMod 112611974941) ^ 104 = (6 : ZMod 112611974941) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 52 * (6 : ZMod 112611974941) ^ 52 := by rw [pow_add]
          _ = 80417132556 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 112611974941) ^ 209 = 12857593531 := by
        calc
          (6 : ZMod 112611974941) ^ 209 = (6 : ZMod 112611974941) ^ (104 + 104 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 104 * (6 : ZMod 112611974941) ^ 104) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 12857593531 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 112611974941) ^ 419 = 40119262626 := by
        calc
          (6 : ZMod 112611974941) ^ 419 = (6 : ZMod 112611974941) ^ (209 + 209 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 209 * (6 : ZMod 112611974941) ^ 209) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 40119262626 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 112611974941) ^ 839 = 53935538983 := by
        calc
          (6 : ZMod 112611974941) ^ 839 = (6 : ZMod 112611974941) ^ (419 + 419 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 419 * (6 : ZMod 112611974941) ^ 419) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 53935538983 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 112611974941) ^ 1678 = 51516805668 := by
        calc
          (6 : ZMod 112611974941) ^ 1678 = (6 : ZMod 112611974941) ^ (839 + 839) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 839 * (6 : ZMod 112611974941) ^ 839 := by rw [pow_add]
          _ = 51516805668 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 112611974941) ^ 3356 = 69996039829 := by
        calc
          (6 : ZMod 112611974941) ^ 3356 = (6 : ZMod 112611974941) ^ (1678 + 1678) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1678 * (6 : ZMod 112611974941) ^ 1678 := by rw [pow_add]
          _ = 69996039829 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 112611974941) ^ 6712 = 105386793926 := by
        calc
          (6 : ZMod 112611974941) ^ 6712 = (6 : ZMod 112611974941) ^ (3356 + 3356) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 3356 * (6 : ZMod 112611974941) ^ 3356 := by rw [pow_add]
          _ = 105386793926 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 112611974941) ^ 13424 = 42027956943 := by
        calc
          (6 : ZMod 112611974941) ^ 13424 = (6 : ZMod 112611974941) ^ (6712 + 6712) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 6712 * (6 : ZMod 112611974941) ^ 6712 := by rw [pow_add]
          _ = 42027956943 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 112611974941) ^ 26848 = 74415824908 := by
        calc
          (6 : ZMod 112611974941) ^ 26848 = (6 : ZMod 112611974941) ^ (13424 + 13424) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 13424 * (6 : ZMod 112611974941) ^ 13424 := by rw [pow_add]
          _ = 74415824908 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 112611974941) ^ 53697 = 29719670624 := by
        calc
          (6 : ZMod 112611974941) ^ 53697 = (6 : ZMod 112611974941) ^ (26848 + 26848 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 26848 * (6 : ZMod 112611974941) ^ 26848) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 29719670624 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 112611974941) ^ 107395 = 18469690700 := by
        calc
          (6 : ZMod 112611974941) ^ 107395 = (6 : ZMod 112611974941) ^ (53697 + 53697 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 53697 * (6 : ZMod 112611974941) ^ 53697) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 18469690700 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 112611974941) ^ 214790 = 24720231333 := by
        calc
          (6 : ZMod 112611974941) ^ 214790 = (6 : ZMod 112611974941) ^ (107395 + 107395) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 107395 * (6 : ZMod 112611974941) ^ 107395 := by rw [pow_add]
          _ = 24720231333 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 112611974941) ^ 429580 = 77538982268 := by
        calc
          (6 : ZMod 112611974941) ^ 429580 = (6 : ZMod 112611974941) ^ (214790 + 214790) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 214790 * (6 : ZMod 112611974941) ^ 214790 := by rw [pow_add]
          _ = 77538982268 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 112611974941) ^ 859161 = 22130329422 := by
        calc
          (6 : ZMod 112611974941) ^ 859161 = (6 : ZMod 112611974941) ^ (429580 + 429580 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 429580 * (6 : ZMod 112611974941) ^ 429580) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 22130329422 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 112611974941) ^ 1718322 = 80423177573 := by
        calc
          (6 : ZMod 112611974941) ^ 1718322 = (6 : ZMod 112611974941) ^ (859161 + 859161) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 859161 * (6 : ZMod 112611974941) ^ 859161 := by rw [pow_add]
          _ = 80423177573 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 112611974941) ^ 3436644 = 60154648002 := by
        calc
          (6 : ZMod 112611974941) ^ 3436644 = (6 : ZMod 112611974941) ^ (1718322 + 1718322) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1718322 * (6 : ZMod 112611974941) ^ 1718322 := by rw [pow_add]
          _ = 60154648002 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 112611974941) ^ 6873289 = 107701809925 := by
        calc
          (6 : ZMod 112611974941) ^ 6873289 = (6 : ZMod 112611974941) ^ (3436644 + 3436644 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 3436644 * (6 : ZMod 112611974941) ^ 3436644) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 107701809925 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 112611974941) ^ 13746578 = 25010166526 := by
        calc
          (6 : ZMod 112611974941) ^ 13746578 = (6 : ZMod 112611974941) ^ (6873289 + 6873289) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 6873289 * (6 : ZMod 112611974941) ^ 6873289 := by rw [pow_add]
          _ = 25010166526 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 112611974941) ^ 27493157 = 78785045088 := by
        calc
          (6 : ZMod 112611974941) ^ 27493157 = (6 : ZMod 112611974941) ^ (13746578 + 13746578 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 13746578 * (6 : ZMod 112611974941) ^ 13746578) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 78785045088 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 112611974941) ^ 54986315 = 98022617725 := by
        calc
          (6 : ZMod 112611974941) ^ 54986315 = (6 : ZMod 112611974941) ^ (27493157 + 27493157 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 27493157 * (6 : ZMod 112611974941) ^ 27493157) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 98022617725 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 112611974941) ^ 109972631 = 101383157453 := by
        calc
          (6 : ZMod 112611974941) ^ 109972631 = (6 : ZMod 112611974941) ^ (54986315 + 54986315 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 54986315 * (6 : ZMod 112611974941) ^ 54986315) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 101383157453 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 112611974941) ^ 219945263 = 74391738573 := by
        calc
          (6 : ZMod 112611974941) ^ 219945263 = (6 : ZMod 112611974941) ^ (109972631 + 109972631 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 109972631 * (6 : ZMod 112611974941) ^ 109972631) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 74391738573 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 112611974941) ^ 439890527 = 14325894027 := by
        calc
          (6 : ZMod 112611974941) ^ 439890527 = (6 : ZMod 112611974941) ^ (219945263 + 219945263 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 219945263 * (6 : ZMod 112611974941) ^ 219945263) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 14325894027 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 112611974941) ^ 879781054 = 4416836681 := by
        calc
          (6 : ZMod 112611974941) ^ 879781054 = (6 : ZMod 112611974941) ^ (439890527 + 439890527) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 439890527 * (6 : ZMod 112611974941) ^ 439890527 := by rw [pow_add]
          _ = 4416836681 := by rw [factor_0_28]; decide
      have factor_0_30 : (6 : ZMod 112611974941) ^ 1759562108 = 90151593758 := by
        calc
          (6 : ZMod 112611974941) ^ 1759562108 = (6 : ZMod 112611974941) ^ (879781054 + 879781054) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 879781054 * (6 : ZMod 112611974941) ^ 879781054 := by rw [pow_add]
          _ = 90151593758 := by rw [factor_0_29]; decide
      have factor_0_31 : (6 : ZMod 112611974941) ^ 3519124216 = 76153854364 := by
        calc
          (6 : ZMod 112611974941) ^ 3519124216 = (6 : ZMod 112611974941) ^ (1759562108 + 1759562108) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1759562108 * (6 : ZMod 112611974941) ^ 1759562108 := by rw [pow_add]
          _ = 76153854364 := by rw [factor_0_30]; decide
      have factor_0_32 : (6 : ZMod 112611974941) ^ 7038248433 = 40616283391 := by
        calc
          (6 : ZMod 112611974941) ^ 7038248433 = (6 : ZMod 112611974941) ^ (3519124216 + 3519124216 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 3519124216 * (6 : ZMod 112611974941) ^ 3519124216) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 40616283391 := by rw [factor_0_31]; decide
      have factor_0_33 : (6 : ZMod 112611974941) ^ 14076496867 = 71979426708 := by
        calc
          (6 : ZMod 112611974941) ^ 14076496867 = (6 : ZMod 112611974941) ^ (7038248433 + 7038248433 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 7038248433 * (6 : ZMod 112611974941) ^ 7038248433) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 71979426708 := by rw [factor_0_32]; decide
      have factor_0_34 : (6 : ZMod 112611974941) ^ 28152993735 = 95830565489 := by
        calc
          (6 : ZMod 112611974941) ^ 28152993735 = (6 : ZMod 112611974941) ^ (14076496867 + 14076496867 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 14076496867 * (6 : ZMod 112611974941) ^ 14076496867) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 95830565489 := by rw [factor_0_33]; decide
      have factor_0_35 : (6 : ZMod 112611974941) ^ 56305987470 = 112611974940 := by
        calc
          (6 : ZMod 112611974941) ^ 56305987470 = (6 : ZMod 112611974941) ^ (28152993735 + 28152993735) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 28152993735 * (6 : ZMod 112611974941) ^ 28152993735 := by rw [pow_add]
          _ = 112611974940 := by rw [factor_0_34]; decide
      change (6 : ZMod 112611974941) ^ 56305987470 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (6 : ZMod 112611974941) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 112611974941) ^ 2 = 36 := by
        calc
          (6 : ZMod 112611974941) ^ 2 = (6 : ZMod 112611974941) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1 * (6 : ZMod 112611974941) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 112611974941) ^ 4 = 1296 := by
        calc
          (6 : ZMod 112611974941) ^ 4 = (6 : ZMod 112611974941) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 2 * (6 : ZMod 112611974941) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 112611974941) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 112611974941) ^ 8 = (6 : ZMod 112611974941) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 4 * (6 : ZMod 112611974941) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 112611974941) ^ 17 = 34863203586 := by
        calc
          (6 : ZMod 112611974941) ^ 17 = (6 : ZMod 112611974941) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 8 * (6 : ZMod 112611974941) ^ 8) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 34863203586 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 112611974941) ^ 34 = 58479718097 := by
        calc
          (6 : ZMod 112611974941) ^ 34 = (6 : ZMod 112611974941) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 17 * (6 : ZMod 112611974941) ^ 17 := by rw [pow_add]
          _ = 58479718097 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 112611974941) ^ 69 = 85807303133 := by
        calc
          (6 : ZMod 112611974941) ^ 69 = (6 : ZMod 112611974941) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 34 * (6 : ZMod 112611974941) ^ 34) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 85807303133 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 112611974941) ^ 139 = 90998711346 := by
        calc
          (6 : ZMod 112611974941) ^ 139 = (6 : ZMod 112611974941) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 69 * (6 : ZMod 112611974941) ^ 69) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 90998711346 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 112611974941) ^ 279 = 30009475539 := by
        calc
          (6 : ZMod 112611974941) ^ 279 = (6 : ZMod 112611974941) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 139 * (6 : ZMod 112611974941) ^ 139) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 30009475539 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 112611974941) ^ 559 = 34136773577 := by
        calc
          (6 : ZMod 112611974941) ^ 559 = (6 : ZMod 112611974941) ^ (279 + 279 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 279 * (6 : ZMod 112611974941) ^ 279) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 34136773577 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 112611974941) ^ 1118 = 36802700118 := by
        calc
          (6 : ZMod 112611974941) ^ 1118 = (6 : ZMod 112611974941) ^ (559 + 559) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 559 * (6 : ZMod 112611974941) ^ 559 := by rw [pow_add]
          _ = 36802700118 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 112611974941) ^ 2237 = 30308848336 := by
        calc
          (6 : ZMod 112611974941) ^ 2237 = (6 : ZMod 112611974941) ^ (1118 + 1118 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1118 * (6 : ZMod 112611974941) ^ 1118) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 30308848336 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 112611974941) ^ 4474 = 38241978712 := by
        calc
          (6 : ZMod 112611974941) ^ 4474 = (6 : ZMod 112611974941) ^ (2237 + 2237) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 2237 * (6 : ZMod 112611974941) ^ 2237 := by rw [pow_add]
          _ = 38241978712 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 112611974941) ^ 8949 = 21179634462 := by
        calc
          (6 : ZMod 112611974941) ^ 8949 = (6 : ZMod 112611974941) ^ (4474 + 4474 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 4474 * (6 : ZMod 112611974941) ^ 4474) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 21179634462 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 112611974941) ^ 17899 = 66378093267 := by
        calc
          (6 : ZMod 112611974941) ^ 17899 = (6 : ZMod 112611974941) ^ (8949 + 8949 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 8949 * (6 : ZMod 112611974941) ^ 8949) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 66378093267 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 112611974941) ^ 35798 = 71809958958 := by
        calc
          (6 : ZMod 112611974941) ^ 35798 = (6 : ZMod 112611974941) ^ (17899 + 17899) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 17899 * (6 : ZMod 112611974941) ^ 17899 := by rw [pow_add]
          _ = 71809958958 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 112611974941) ^ 71596 = 77970398244 := by
        calc
          (6 : ZMod 112611974941) ^ 71596 = (6 : ZMod 112611974941) ^ (35798 + 35798) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 35798 * (6 : ZMod 112611974941) ^ 35798 := by rw [pow_add]
          _ = 77970398244 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 112611974941) ^ 143193 = 96904946837 := by
        calc
          (6 : ZMod 112611974941) ^ 143193 = (6 : ZMod 112611974941) ^ (71596 + 71596 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 71596 * (6 : ZMod 112611974941) ^ 71596) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 96904946837 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 112611974941) ^ 286387 = 40863170230 := by
        calc
          (6 : ZMod 112611974941) ^ 286387 = (6 : ZMod 112611974941) ^ (143193 + 143193 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 143193 * (6 : ZMod 112611974941) ^ 143193) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 40863170230 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 112611974941) ^ 572774 = 87986431768 := by
        calc
          (6 : ZMod 112611974941) ^ 572774 = (6 : ZMod 112611974941) ^ (286387 + 286387) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 286387 * (6 : ZMod 112611974941) ^ 286387 := by rw [pow_add]
          _ = 87986431768 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 112611974941) ^ 1145548 = 77270798893 := by
        calc
          (6 : ZMod 112611974941) ^ 1145548 = (6 : ZMod 112611974941) ^ (572774 + 572774) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 572774 * (6 : ZMod 112611974941) ^ 572774 := by rw [pow_add]
          _ = 77270798893 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 112611974941) ^ 2291096 = 21470940447 := by
        calc
          (6 : ZMod 112611974941) ^ 2291096 = (6 : ZMod 112611974941) ^ (1145548 + 1145548) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1145548 * (6 : ZMod 112611974941) ^ 1145548 := by rw [pow_add]
          _ = 21470940447 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 112611974941) ^ 4582192 = 92666194970 := by
        calc
          (6 : ZMod 112611974941) ^ 4582192 = (6 : ZMod 112611974941) ^ (2291096 + 2291096) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 2291096 * (6 : ZMod 112611974941) ^ 2291096 := by rw [pow_add]
          _ = 92666194970 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 112611974941) ^ 9164385 = 34340568152 := by
        calc
          (6 : ZMod 112611974941) ^ 9164385 = (6 : ZMod 112611974941) ^ (4582192 + 4582192 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 4582192 * (6 : ZMod 112611974941) ^ 4582192) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 34340568152 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 112611974941) ^ 18328771 = 34584393729 := by
        calc
          (6 : ZMod 112611974941) ^ 18328771 = (6 : ZMod 112611974941) ^ (9164385 + 9164385 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 9164385 * (6 : ZMod 112611974941) ^ 9164385) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 34584393729 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 112611974941) ^ 36657543 = 69801955238 := by
        calc
          (6 : ZMod 112611974941) ^ 36657543 = (6 : ZMod 112611974941) ^ (18328771 + 18328771 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 18328771 * (6 : ZMod 112611974941) ^ 18328771) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 69801955238 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 112611974941) ^ 73315087 = 62127419198 := by
        calc
          (6 : ZMod 112611974941) ^ 73315087 = (6 : ZMod 112611974941) ^ (36657543 + 36657543 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 36657543 * (6 : ZMod 112611974941) ^ 36657543) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 62127419198 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 112611974941) ^ 146630175 = 78396682255 := by
        calc
          (6 : ZMod 112611974941) ^ 146630175 = (6 : ZMod 112611974941) ^ (73315087 + 73315087 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 73315087 * (6 : ZMod 112611974941) ^ 73315087) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 78396682255 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 112611974941) ^ 293260351 = 44630758068 := by
        calc
          (6 : ZMod 112611974941) ^ 293260351 = (6 : ZMod 112611974941) ^ (146630175 + 146630175 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 146630175 * (6 : ZMod 112611974941) ^ 146630175) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 44630758068 := by rw [factor_1_27]; decide
      have factor_1_29 : (6 : ZMod 112611974941) ^ 586520702 = 63033217101 := by
        calc
          (6 : ZMod 112611974941) ^ 586520702 = (6 : ZMod 112611974941) ^ (293260351 + 293260351) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 293260351 * (6 : ZMod 112611974941) ^ 293260351 := by rw [pow_add]
          _ = 63033217101 := by rw [factor_1_28]; decide
      have factor_1_30 : (6 : ZMod 112611974941) ^ 1173041405 = 103972909065 := by
        calc
          (6 : ZMod 112611974941) ^ 1173041405 = (6 : ZMod 112611974941) ^ (586520702 + 586520702 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 586520702 * (6 : ZMod 112611974941) ^ 586520702) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 103972909065 := by rw [factor_1_29]; decide
      have factor_1_31 : (6 : ZMod 112611974941) ^ 2346082811 = 77673559413 := by
        calc
          (6 : ZMod 112611974941) ^ 2346082811 = (6 : ZMod 112611974941) ^ (1173041405 + 1173041405 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1173041405 * (6 : ZMod 112611974941) ^ 1173041405) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 77673559413 := by rw [factor_1_30]; decide
      have factor_1_32 : (6 : ZMod 112611974941) ^ 4692165622 = 69682328693 := by
        calc
          (6 : ZMod 112611974941) ^ 4692165622 = (6 : ZMod 112611974941) ^ (2346082811 + 2346082811) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 2346082811 * (6 : ZMod 112611974941) ^ 2346082811 := by rw [pow_add]
          _ = 69682328693 := by rw [factor_1_31]; decide
      have factor_1_33 : (6 : ZMod 112611974941) ^ 9384331245 = 67834534886 := by
        calc
          (6 : ZMod 112611974941) ^ 9384331245 = (6 : ZMod 112611974941) ^ (4692165622 + 4692165622 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 4692165622 * (6 : ZMod 112611974941) ^ 4692165622) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 67834534886 := by rw [factor_1_32]; decide
      have factor_1_34 : (6 : ZMod 112611974941) ^ 18768662490 = 83407053042 := by
        calc
          (6 : ZMod 112611974941) ^ 18768662490 = (6 : ZMod 112611974941) ^ (9384331245 + 9384331245) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 9384331245 * (6 : ZMod 112611974941) ^ 9384331245 := by rw [pow_add]
          _ = 83407053042 := by rw [factor_1_33]; decide
      have factor_1_35 : (6 : ZMod 112611974941) ^ 37537324980 = 83407053041 := by
        calc
          (6 : ZMod 112611974941) ^ 37537324980 = (6 : ZMod 112611974941) ^ (18768662490 + 18768662490) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 18768662490 * (6 : ZMod 112611974941) ^ 18768662490 := by rw [pow_add]
          _ = 83407053041 := by rw [factor_1_34]; decide
      change (6 : ZMod 112611974941) ^ 37537324980 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (6 : ZMod 112611974941) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 112611974941) ^ 2 = 36 := by
        calc
          (6 : ZMod 112611974941) ^ 2 = (6 : ZMod 112611974941) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1 * (6 : ZMod 112611974941) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 112611974941) ^ 5 = 7776 := by
        calc
          (6 : ZMod 112611974941) ^ 5 = (6 : ZMod 112611974941) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 2 * (6 : ZMod 112611974941) ^ 2) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 112611974941) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 112611974941) ^ 10 = (6 : ZMod 112611974941) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 5 * (6 : ZMod 112611974941) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 112611974941) ^ 20 = 98061628470 := by
        calc
          (6 : ZMod 112611974941) ^ 20 = (6 : ZMod 112611974941) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 10 * (6 : ZMod 112611974941) ^ 10 := by rw [pow_add]
          _ = 98061628470 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 112611974941) ^ 41 = 62956053681 := by
        calc
          (6 : ZMod 112611974941) ^ 41 = (6 : ZMod 112611974941) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 20 * (6 : ZMod 112611974941) ^ 20) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 62956053681 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 112611974941) ^ 83 = 36071362931 := by
        calc
          (6 : ZMod 112611974941) ^ 83 = (6 : ZMod 112611974941) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 41 * (6 : ZMod 112611974941) ^ 41) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 36071362931 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 112611974941) ^ 167 = 103738221892 := by
        calc
          (6 : ZMod 112611974941) ^ 167 = (6 : ZMod 112611974941) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 83 * (6 : ZMod 112611974941) ^ 83) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 103738221892 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 112611974941) ^ 335 = 37604750713 := by
        calc
          (6 : ZMod 112611974941) ^ 335 = (6 : ZMod 112611974941) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 167 * (6 : ZMod 112611974941) ^ 167) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 37604750713 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 112611974941) ^ 671 = 91073036999 := by
        calc
          (6 : ZMod 112611974941) ^ 671 = (6 : ZMod 112611974941) ^ (335 + 335 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 335 * (6 : ZMod 112611974941) ^ 335) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 91073036999 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 112611974941) ^ 1342 = 13249976809 := by
        calc
          (6 : ZMod 112611974941) ^ 1342 = (6 : ZMod 112611974941) ^ (671 + 671) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 671 * (6 : ZMod 112611974941) ^ 671 := by rw [pow_add]
          _ = 13249976809 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 112611974941) ^ 2684 = 63537976311 := by
        calc
          (6 : ZMod 112611974941) ^ 2684 = (6 : ZMod 112611974941) ^ (1342 + 1342) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1342 * (6 : ZMod 112611974941) ^ 1342 := by rw [pow_add]
          _ = 63537976311 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 112611974941) ^ 5369 = 80082497470 := by
        calc
          (6 : ZMod 112611974941) ^ 5369 = (6 : ZMod 112611974941) ^ (2684 + 2684 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 2684 * (6 : ZMod 112611974941) ^ 2684) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 80082497470 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 112611974941) ^ 10739 = 77589073503 := by
        calc
          (6 : ZMod 112611974941) ^ 10739 = (6 : ZMod 112611974941) ^ (5369 + 5369 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 5369 * (6 : ZMod 112611974941) ^ 5369) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 77589073503 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 112611974941) ^ 21479 = 85362018690 := by
        calc
          (6 : ZMod 112611974941) ^ 21479 = (6 : ZMod 112611974941) ^ (10739 + 10739 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 10739 * (6 : ZMod 112611974941) ^ 10739) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 85362018690 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 112611974941) ^ 42958 = 86757398736 := by
        calc
          (6 : ZMod 112611974941) ^ 42958 = (6 : ZMod 112611974941) ^ (21479 + 21479) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 21479 * (6 : ZMod 112611974941) ^ 21479 := by rw [pow_add]
          _ = 86757398736 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 112611974941) ^ 85916 = 93956157410 := by
        calc
          (6 : ZMod 112611974941) ^ 85916 = (6 : ZMod 112611974941) ^ (42958 + 42958) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 42958 * (6 : ZMod 112611974941) ^ 42958 := by rw [pow_add]
          _ = 93956157410 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 112611974941) ^ 171832 = 7241512874 := by
        calc
          (6 : ZMod 112611974941) ^ 171832 = (6 : ZMod 112611974941) ^ (85916 + 85916) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 85916 * (6 : ZMod 112611974941) ^ 85916 := by rw [pow_add]
          _ = 7241512874 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 112611974941) ^ 343664 = 15330852842 := by
        calc
          (6 : ZMod 112611974941) ^ 343664 = (6 : ZMod 112611974941) ^ (171832 + 171832) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 171832 * (6 : ZMod 112611974941) ^ 171832 := by rw [pow_add]
          _ = 15330852842 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 112611974941) ^ 687328 = 32452037032 := by
        calc
          (6 : ZMod 112611974941) ^ 687328 = (6 : ZMod 112611974941) ^ (343664 + 343664) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 343664 * (6 : ZMod 112611974941) ^ 343664 := by rw [pow_add]
          _ = 32452037032 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 112611974941) ^ 1374657 = 87562676076 := by
        calc
          (6 : ZMod 112611974941) ^ 1374657 = (6 : ZMod 112611974941) ^ (687328 + 687328 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 687328 * (6 : ZMod 112611974941) ^ 687328) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 87562676076 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 112611974941) ^ 2749315 = 48195486816 := by
        calc
          (6 : ZMod 112611974941) ^ 2749315 = (6 : ZMod 112611974941) ^ (1374657 + 1374657 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1374657 * (6 : ZMod 112611974941) ^ 1374657) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 48195486816 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 112611974941) ^ 5498631 = 26140518518 := by
        calc
          (6 : ZMod 112611974941) ^ 5498631 = (6 : ZMod 112611974941) ^ (2749315 + 2749315 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 2749315 * (6 : ZMod 112611974941) ^ 2749315) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 26140518518 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 112611974941) ^ 10997263 = 39802410741 := by
        calc
          (6 : ZMod 112611974941) ^ 10997263 = (6 : ZMod 112611974941) ^ (5498631 + 5498631 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 5498631 * (6 : ZMod 112611974941) ^ 5498631) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 39802410741 := by rw [factor_2_22]; decide
      have factor_2_24 : (6 : ZMod 112611974941) ^ 21994526 = 88093121482 := by
        calc
          (6 : ZMod 112611974941) ^ 21994526 = (6 : ZMod 112611974941) ^ (10997263 + 10997263) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 10997263 * (6 : ZMod 112611974941) ^ 10997263 := by rw [pow_add]
          _ = 88093121482 := by rw [factor_2_23]; decide
      have factor_2_25 : (6 : ZMod 112611974941) ^ 43989052 = 72283771899 := by
        calc
          (6 : ZMod 112611974941) ^ 43989052 = (6 : ZMod 112611974941) ^ (21994526 + 21994526) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 21994526 * (6 : ZMod 112611974941) ^ 21994526 := by rw [pow_add]
          _ = 72283771899 := by rw [factor_2_24]; decide
      have factor_2_26 : (6 : ZMod 112611974941) ^ 87978105 = 22715309848 := by
        calc
          (6 : ZMod 112611974941) ^ 87978105 = (6 : ZMod 112611974941) ^ (43989052 + 43989052 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 43989052 * (6 : ZMod 112611974941) ^ 43989052) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 22715309848 := by rw [factor_2_25]; decide
      have factor_2_27 : (6 : ZMod 112611974941) ^ 175956210 = 88103883002 := by
        calc
          (6 : ZMod 112611974941) ^ 175956210 = (6 : ZMod 112611974941) ^ (87978105 + 87978105) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 87978105 * (6 : ZMod 112611974941) ^ 87978105 := by rw [pow_add]
          _ = 88103883002 := by rw [factor_2_26]; decide
      have factor_2_28 : (6 : ZMod 112611974941) ^ 351912421 = 44286152295 := by
        calc
          (6 : ZMod 112611974941) ^ 351912421 = (6 : ZMod 112611974941) ^ (175956210 + 175956210 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 175956210 * (6 : ZMod 112611974941) ^ 175956210) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 44286152295 := by rw [factor_2_27]; decide
      have factor_2_29 : (6 : ZMod 112611974941) ^ 703824843 = 109468475246 := by
        calc
          (6 : ZMod 112611974941) ^ 703824843 = (6 : ZMod 112611974941) ^ (351912421 + 351912421 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 351912421 * (6 : ZMod 112611974941) ^ 351912421) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 109468475246 := by rw [factor_2_28]; decide
      have factor_2_30 : (6 : ZMod 112611974941) ^ 1407649686 = 3739760146 := by
        calc
          (6 : ZMod 112611974941) ^ 1407649686 = (6 : ZMod 112611974941) ^ (703824843 + 703824843) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 703824843 * (6 : ZMod 112611974941) ^ 703824843 := by rw [pow_add]
          _ = 3739760146 := by rw [factor_2_29]; decide
      have factor_2_31 : (6 : ZMod 112611974941) ^ 2815299373 = 59303557536 := by
        calc
          (6 : ZMod 112611974941) ^ 2815299373 = (6 : ZMod 112611974941) ^ (1407649686 + 1407649686 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1407649686 * (6 : ZMod 112611974941) ^ 1407649686) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 59303557536 := by rw [factor_2_30]; decide
      have factor_2_32 : (6 : ZMod 112611974941) ^ 5630598747 = 61609660428 := by
        calc
          (6 : ZMod 112611974941) ^ 5630598747 = (6 : ZMod 112611974941) ^ (2815299373 + 2815299373 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 2815299373 * (6 : ZMod 112611974941) ^ 2815299373) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 61609660428 := by rw [factor_2_31]; decide
      have factor_2_33 : (6 : ZMod 112611974941) ^ 11261197494 = 12618754329 := by
        calc
          (6 : ZMod 112611974941) ^ 11261197494 = (6 : ZMod 112611974941) ^ (5630598747 + 5630598747) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 5630598747 * (6 : ZMod 112611974941) ^ 5630598747 := by rw [pow_add]
          _ = 12618754329 := by rw [factor_2_32]; decide
      have factor_2_34 : (6 : ZMod 112611974941) ^ 22522394988 = 93823495423 := by
        calc
          (6 : ZMod 112611974941) ^ 22522394988 = (6 : ZMod 112611974941) ^ (11261197494 + 11261197494) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 11261197494 * (6 : ZMod 112611974941) ^ 11261197494 := by rw [pow_add]
          _ = 93823495423 := by rw [factor_2_33]; decide
      change (6 : ZMod 112611974941) ^ 22522394988 ≠ 1
      rw [factor_2_34]
      decide
    ·
      have factor_3_0 : (6 : ZMod 112611974941) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 112611974941) ^ 3 = 216 := by
        calc
          (6 : ZMod 112611974941) ^ 3 = (6 : ZMod 112611974941) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1 * (6 : ZMod 112611974941) ^ 1) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 112611974941) ^ 6 = 46656 := by
        calc
          (6 : ZMod 112611974941) ^ 6 = (6 : ZMod 112611974941) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 3 * (6 : ZMod 112611974941) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 112611974941) ^ 12 = 2176782336 := by
        calc
          (6 : ZMod 112611974941) ^ 12 = (6 : ZMod 112611974941) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 6 * (6 : ZMod 112611974941) ^ 6 := by rw [pow_add]
          _ = 2176782336 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 112611974941) ^ 24 = 61562763672 := by
        calc
          (6 : ZMod 112611974941) ^ 24 = (6 : ZMod 112611974941) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 12 * (6 : ZMod 112611974941) ^ 12 := by rw [pow_add]
          _ = 61562763672 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 112611974941) ^ 49 = 26261717142 := by
        calc
          (6 : ZMod 112611974941) ^ 49 = (6 : ZMod 112611974941) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 24 * (6 : ZMod 112611974941) ^ 24) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 26261717142 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 112611974941) ^ 98 = 17930430534 := by
        calc
          (6 : ZMod 112611974941) ^ 98 = (6 : ZMod 112611974941) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 49 * (6 : ZMod 112611974941) ^ 49 := by rw [pow_add]
          _ = 17930430534 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 112611974941) ^ 197 = 6730269830 := by
        calc
          (6 : ZMod 112611974941) ^ 197 = (6 : ZMod 112611974941) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 98 * (6 : ZMod 112611974941) ^ 98) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 6730269830 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 112611974941) ^ 394 = 77855147279 := by
        calc
          (6 : ZMod 112611974941) ^ 394 = (6 : ZMod 112611974941) ^ (197 + 197) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 197 * (6 : ZMod 112611974941) ^ 197 := by rw [pow_add]
          _ = 77855147279 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 112611974941) ^ 789 = 300233495 := by
        calc
          (6 : ZMod 112611974941) ^ 789 = (6 : ZMod 112611974941) ^ (394 + 394 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 394 * (6 : ZMod 112611974941) ^ 394) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 300233495 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 112611974941) ^ 1579 = 52742199096 := by
        calc
          (6 : ZMod 112611974941) ^ 1579 = (6 : ZMod 112611974941) ^ (789 + 789 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 789 * (6 : ZMod 112611974941) ^ 789) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 52742199096 := by rw [factor_3_9]; decide
      have factor_3_11 : (6 : ZMod 112611974941) ^ 3158 = 8396888019 := by
        calc
          (6 : ZMod 112611974941) ^ 3158 = (6 : ZMod 112611974941) ^ (1579 + 1579) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1579 * (6 : ZMod 112611974941) ^ 1579 := by rw [pow_add]
          _ = 8396888019 := by rw [factor_3_10]; decide
      have factor_3_12 : (6 : ZMod 112611974941) ^ 6317 = 67132200585 := by
        calc
          (6 : ZMod 112611974941) ^ 6317 = (6 : ZMod 112611974941) ^ (3158 + 3158 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 3158 * (6 : ZMod 112611974941) ^ 3158) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 67132200585 := by rw [factor_3_11]; decide
      have factor_3_13 : (6 : ZMod 112611974941) ^ 12634 = 8943178095 := by
        calc
          (6 : ZMod 112611974941) ^ 12634 = (6 : ZMod 112611974941) ^ (6317 + 6317) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 6317 * (6 : ZMod 112611974941) ^ 6317 := by rw [pow_add]
          _ = 8943178095 := by rw [factor_3_12]; decide
      have factor_3_14 : (6 : ZMod 112611974941) ^ 25269 = 8966418093 := by
        calc
          (6 : ZMod 112611974941) ^ 25269 = (6 : ZMod 112611974941) ^ (12634 + 12634 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 12634 * (6 : ZMod 112611974941) ^ 12634) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 8966418093 := by rw [factor_3_13]; decide
      have factor_3_15 : (6 : ZMod 112611974941) ^ 50538 = 110469509765 := by
        calc
          (6 : ZMod 112611974941) ^ 50538 = (6 : ZMod 112611974941) ^ (25269 + 25269) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 25269 * (6 : ZMod 112611974941) ^ 25269 := by rw [pow_add]
          _ = 110469509765 := by rw [factor_3_14]; decide
      have factor_3_16 : (6 : ZMod 112611974941) ^ 101077 = 48777372965 := by
        calc
          (6 : ZMod 112611974941) ^ 101077 = (6 : ZMod 112611974941) ^ (50538 + 50538 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 50538 * (6 : ZMod 112611974941) ^ 50538) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 48777372965 := by rw [factor_3_15]; decide
      have factor_3_17 : (6 : ZMod 112611974941) ^ 202155 = 95211831494 := by
        calc
          (6 : ZMod 112611974941) ^ 202155 = (6 : ZMod 112611974941) ^ (101077 + 101077 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 101077 * (6 : ZMod 112611974941) ^ 101077) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 95211831494 := by rw [factor_3_16]; decide
      have factor_3_18 : (6 : ZMod 112611974941) ^ 404311 = 111076347698 := by
        calc
          (6 : ZMod 112611974941) ^ 404311 = (6 : ZMod 112611974941) ^ (202155 + 202155 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 202155 * (6 : ZMod 112611974941) ^ 202155) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 111076347698 := by rw [factor_3_17]; decide
      have factor_3_19 : (6 : ZMod 112611974941) ^ 808622 = 80803745490 := by
        calc
          (6 : ZMod 112611974941) ^ 808622 = (6 : ZMod 112611974941) ^ (404311 + 404311) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 404311 * (6 : ZMod 112611974941) ^ 404311 := by rw [pow_add]
          _ = 80803745490 := by rw [factor_3_18]; decide
      have factor_3_20 : (6 : ZMod 112611974941) ^ 1617244 = 109838025355 := by
        calc
          (6 : ZMod 112611974941) ^ 1617244 = (6 : ZMod 112611974941) ^ (808622 + 808622) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 808622 * (6 : ZMod 112611974941) ^ 808622 := by rw [pow_add]
          _ = 109838025355 := by rw [factor_3_19]; decide
      have factor_3_21 : (6 : ZMod 112611974941) ^ 3234489 = 78117011388 := by
        calc
          (6 : ZMod 112611974941) ^ 3234489 = (6 : ZMod 112611974941) ^ (1617244 + 1617244 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1617244 * (6 : ZMod 112611974941) ^ 1617244) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 78117011388 := by rw [factor_3_20]; decide
      have factor_3_22 : (6 : ZMod 112611974941) ^ 6468978 = 101568762184 := by
        calc
          (6 : ZMod 112611974941) ^ 6468978 = (6 : ZMod 112611974941) ^ (3234489 + 3234489) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 3234489 * (6 : ZMod 112611974941) ^ 3234489 := by rw [pow_add]
          _ = 101568762184 := by rw [factor_3_21]; decide
      have factor_3_23 : (6 : ZMod 112611974941) ^ 12937956 = 45984231771 := by
        calc
          (6 : ZMod 112611974941) ^ 12937956 = (6 : ZMod 112611974941) ^ (6468978 + 6468978) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 6468978 * (6 : ZMod 112611974941) ^ 6468978 := by rw [pow_add]
          _ = 45984231771 := by rw [factor_3_22]; decide
      have factor_3_24 : (6 : ZMod 112611974941) ^ 25875913 = 99411637552 := by
        calc
          (6 : ZMod 112611974941) ^ 25875913 = (6 : ZMod 112611974941) ^ (12937956 + 12937956 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 12937956 * (6 : ZMod 112611974941) ^ 12937956) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 99411637552 := by rw [factor_3_23]; decide
      have factor_3_25 : (6 : ZMod 112611974941) ^ 51751826 = 71316766684 := by
        calc
          (6 : ZMod 112611974941) ^ 51751826 = (6 : ZMod 112611974941) ^ (25875913 + 25875913) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 25875913 * (6 : ZMod 112611974941) ^ 25875913 := by rw [pow_add]
          _ = 71316766684 := by rw [factor_3_24]; decide
      have factor_3_26 : (6 : ZMod 112611974941) ^ 103503653 = 40280625258 := by
        calc
          (6 : ZMod 112611974941) ^ 103503653 = (6 : ZMod 112611974941) ^ (51751826 + 51751826 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 51751826 * (6 : ZMod 112611974941) ^ 51751826) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 40280625258 := by rw [factor_3_25]; decide
      have factor_3_27 : (6 : ZMod 112611974941) ^ 207007306 = 51646503930 := by
        calc
          (6 : ZMod 112611974941) ^ 207007306 = (6 : ZMod 112611974941) ^ (103503653 + 103503653) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 103503653 * (6 : ZMod 112611974941) ^ 103503653 := by rw [pow_add]
          _ = 51646503930 := by rw [factor_3_26]; decide
      have factor_3_28 : (6 : ZMod 112611974941) ^ 414014613 = 88941007478 := by
        calc
          (6 : ZMod 112611974941) ^ 414014613 = (6 : ZMod 112611974941) ^ (207007306 + 207007306 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 207007306 * (6 : ZMod 112611974941) ^ 207007306) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 88941007478 := by rw [factor_3_27]; decide
      have factor_3_29 : (6 : ZMod 112611974941) ^ 828029227 = 33441804737 := by
        calc
          (6 : ZMod 112611974941) ^ 828029227 = (6 : ZMod 112611974941) ^ (414014613 + 414014613 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 414014613 * (6 : ZMod 112611974941) ^ 414014613) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 33441804737 := by rw [factor_3_28]; decide
      have factor_3_30 : (6 : ZMod 112611974941) ^ 1656058455 = 35623089025 := by
        calc
          (6 : ZMod 112611974941) ^ 1656058455 = (6 : ZMod 112611974941) ^ (828029227 + 828029227 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 828029227 * (6 : ZMod 112611974941) ^ 828029227) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 35623089025 := by rw [factor_3_29]; decide
      have factor_3_31 : (6 : ZMod 112611974941) ^ 3312116910 = 59507988187 := by
        calc
          (6 : ZMod 112611974941) ^ 3312116910 = (6 : ZMod 112611974941) ^ (1656058455 + 1656058455) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1656058455 * (6 : ZMod 112611974941) ^ 1656058455 := by rw [pow_add]
          _ = 59507988187 := by rw [factor_3_30]; decide
      have factor_3_32 : (6 : ZMod 112611974941) ^ 6624233820 = 63361576482 := by
        calc
          (6 : ZMod 112611974941) ^ 6624233820 = (6 : ZMod 112611974941) ^ (3312116910 + 3312116910) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 3312116910 * (6 : ZMod 112611974941) ^ 3312116910 := by rw [pow_add]
          _ = 63361576482 := by rw [factor_3_31]; decide
      change (6 : ZMod 112611974941) ^ 6624233820 ≠ 1
      rw [factor_3_32]
      decide
    ·
      have factor_4_0 : (6 : ZMod 112611974941) ^ 1 = 6 := by norm_num
      have factor_4_1 : (6 : ZMod 112611974941) ^ 2 = 36 := by
        calc
          (6 : ZMod 112611974941) ^ 2 = (6 : ZMod 112611974941) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1 * (6 : ZMod 112611974941) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_4_0]; decide
      have factor_4_2 : (6 : ZMod 112611974941) ^ 4 = 1296 := by
        calc
          (6 : ZMod 112611974941) ^ 4 = (6 : ZMod 112611974941) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 2 * (6 : ZMod 112611974941) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_4_1]; decide
      have factor_4_3 : (6 : ZMod 112611974941) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 112611974941) ^ 8 = (6 : ZMod 112611974941) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 4 * (6 : ZMod 112611974941) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_4_2]; decide
      have factor_4_4 : (6 : ZMod 112611974941) ^ 17 = 34863203586 := by
        calc
          (6 : ZMod 112611974941) ^ 17 = (6 : ZMod 112611974941) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 8 * (6 : ZMod 112611974941) ^ 8) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 34863203586 := by rw [factor_4_3]; decide
      have factor_4_5 : (6 : ZMod 112611974941) ^ 35 = 13042383759 := by
        calc
          (6 : ZMod 112611974941) ^ 35 = (6 : ZMod 112611974941) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 17 * (6 : ZMod 112611974941) ^ 17) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 13042383759 := by rw [factor_4_4]; decide
      have factor_4_6 : (6 : ZMod 112611974941) ^ 71 = 48539589381 := by
        calc
          (6 : ZMod 112611974941) ^ 71 = (6 : ZMod 112611974941) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 35 * (6 : ZMod 112611974941) ^ 35) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 48539589381 := by rw [factor_4_5]; decide
      have factor_4_7 : (6 : ZMod 112611974941) ^ 143 = 29592141189 := by
        calc
          (6 : ZMod 112611974941) ^ 143 = (6 : ZMod 112611974941) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 71 * (6 : ZMod 112611974941) ^ 71) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 29592141189 := by rw [factor_4_6]; decide
      have factor_4_8 : (6 : ZMod 112611974941) ^ 287 = 63567146011 := by
        calc
          (6 : ZMod 112611974941) ^ 287 = (6 : ZMod 112611974941) ^ (143 + 143 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 143 * (6 : ZMod 112611974941) ^ 143) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 63567146011 := by rw [factor_4_7]; decide
      have factor_4_9 : (6 : ZMod 112611974941) ^ 575 = 69037321109 := by
        calc
          (6 : ZMod 112611974941) ^ 575 = (6 : ZMod 112611974941) ^ (287 + 287 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 287 * (6 : ZMod 112611974941) ^ 287) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 69037321109 := by rw [factor_4_8]; decide
      have factor_4_10 : (6 : ZMod 112611974941) ^ 1151 = 43745064023 := by
        calc
          (6 : ZMod 112611974941) ^ 1151 = (6 : ZMod 112611974941) ^ (575 + 575 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 575 * (6 : ZMod 112611974941) ^ 575) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 43745064023 := by rw [factor_4_9]; decide
      have factor_4_11 : (6 : ZMod 112611974941) ^ 2303 = 64607802077 := by
        calc
          (6 : ZMod 112611974941) ^ 2303 = (6 : ZMod 112611974941) ^ (1151 + 1151 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1151 * (6 : ZMod 112611974941) ^ 1151) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 64607802077 := by rw [factor_4_10]; decide
      have factor_4_12 : (6 : ZMod 112611974941) ^ 4606 = 5623142845 := by
        calc
          (6 : ZMod 112611974941) ^ 4606 = (6 : ZMod 112611974941) ^ (2303 + 2303) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 2303 * (6 : ZMod 112611974941) ^ 2303 := by rw [pow_add]
          _ = 5623142845 := by rw [factor_4_11]; decide
      have factor_4_13 : (6 : ZMod 112611974941) ^ 9213 = 85844097746 := by
        calc
          (6 : ZMod 112611974941) ^ 9213 = (6 : ZMod 112611974941) ^ (4606 + 4606 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 4606 * (6 : ZMod 112611974941) ^ 4606) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 85844097746 := by rw [factor_4_12]; decide
      have factor_4_14 : (6 : ZMod 112611974941) ^ 18427 = 38188478701 := by
        calc
          (6 : ZMod 112611974941) ^ 18427 = (6 : ZMod 112611974941) ^ (9213 + 9213 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 9213 * (6 : ZMod 112611974941) ^ 9213) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 38188478701 := by rw [factor_4_13]; decide
      have factor_4_15 : (6 : ZMod 112611974941) ^ 36854 = 27827195629 := by
        calc
          (6 : ZMod 112611974941) ^ 36854 = (6 : ZMod 112611974941) ^ (18427 + 18427) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 18427 * (6 : ZMod 112611974941) ^ 18427 := by rw [pow_add]
          _ = 27827195629 := by rw [factor_4_14]; decide
      have factor_4_16 : (6 : ZMod 112611974941) ^ 73708 = 39460630573 := by
        calc
          (6 : ZMod 112611974941) ^ 73708 = (6 : ZMod 112611974941) ^ (36854 + 36854) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 36854 * (6 : ZMod 112611974941) ^ 36854 := by rw [pow_add]
          _ = 39460630573 := by rw [factor_4_15]; decide
      have factor_4_17 : (6 : ZMod 112611974941) ^ 147416 = 73892956968 := by
        calc
          (6 : ZMod 112611974941) ^ 147416 = (6 : ZMod 112611974941) ^ (73708 + 73708) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 73708 * (6 : ZMod 112611974941) ^ 73708 := by rw [pow_add]
          _ = 73892956968 := by rw [factor_4_16]; decide
      have factor_4_18 : (6 : ZMod 112611974941) ^ 294832 = 104969491154 := by
        calc
          (6 : ZMod 112611974941) ^ 294832 = (6 : ZMod 112611974941) ^ (147416 + 147416) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 147416 * (6 : ZMod 112611974941) ^ 147416 := by rw [pow_add]
          _ = 104969491154 := by rw [factor_4_17]; decide
      have factor_4_19 : (6 : ZMod 112611974941) ^ 589665 = 1241910979 := by
        calc
          (6 : ZMod 112611974941) ^ 589665 = (6 : ZMod 112611974941) ^ (294832 + 294832 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 294832 * (6 : ZMod 112611974941) ^ 294832) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 1241910979 := by rw [factor_4_18]; decide
      have factor_4_20 : (6 : ZMod 112611974941) ^ 1179331 = 108109168733 := by
        calc
          (6 : ZMod 112611974941) ^ 1179331 = (6 : ZMod 112611974941) ^ (589665 + 589665 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 589665 * (6 : ZMod 112611974941) ^ 589665) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 108109168733 := by rw [factor_4_19]; decide
      have factor_4_21 : (6 : ZMod 112611974941) ^ 2358662 = 65628040563 := by
        calc
          (6 : ZMod 112611974941) ^ 2358662 = (6 : ZMod 112611974941) ^ (1179331 + 1179331) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1179331 * (6 : ZMod 112611974941) ^ 1179331 := by rw [pow_add]
          _ = 65628040563 := by rw [factor_4_20]; decide
      have factor_4_22 : (6 : ZMod 112611974941) ^ 4717324 = 32787903648 := by
        calc
          (6 : ZMod 112611974941) ^ 4717324 = (6 : ZMod 112611974941) ^ (2358662 + 2358662) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 2358662 * (6 : ZMod 112611974941) ^ 2358662 := by rw [pow_add]
          _ = 32787903648 := by rw [factor_4_21]; decide
      have factor_4_23 : (6 : ZMod 112611974941) ^ 9434649 = 24581852228 := by
        calc
          (6 : ZMod 112611974941) ^ 9434649 = (6 : ZMod 112611974941) ^ (4717324 + 4717324 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 4717324 * (6 : ZMod 112611974941) ^ 4717324) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 24581852228 := by rw [factor_4_22]; decide
      have factor_4_24 : (6 : ZMod 112611974941) ^ 18869298 = 26913663764 := by
        calc
          (6 : ZMod 112611974941) ^ 18869298 = (6 : ZMod 112611974941) ^ (9434649 + 9434649) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 9434649 * (6 : ZMod 112611974941) ^ 9434649 := by rw [pow_add]
          _ = 26913663764 := by rw [factor_4_23]; decide
      have factor_4_25 : (6 : ZMod 112611974941) ^ 37738597 = 66645958406 := by
        calc
          (6 : ZMod 112611974941) ^ 37738597 = (6 : ZMod 112611974941) ^ (18869298 + 18869298 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 18869298 * (6 : ZMod 112611974941) ^ 18869298) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 66645958406 := by rw [factor_4_24]; decide
      have factor_4_26 : (6 : ZMod 112611974941) ^ 75477195 = 85090799032 := by
        calc
          (6 : ZMod 112611974941) ^ 75477195 = (6 : ZMod 112611974941) ^ (37738597 + 37738597 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 37738597 * (6 : ZMod 112611974941) ^ 37738597) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 85090799032 := by rw [factor_4_25]; decide
      have factor_4_27 : (6 : ZMod 112611974941) ^ 150954390 = 44886679760 := by
        calc
          (6 : ZMod 112611974941) ^ 150954390 = (6 : ZMod 112611974941) ^ (75477195 + 75477195) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 75477195 * (6 : ZMod 112611974941) ^ 75477195 := by rw [pow_add]
          _ = 44886679760 := by rw [factor_4_26]; decide
      have factor_4_28 : (6 : ZMod 112611974941) ^ 301908780 = 45150196272 := by
        calc
          (6 : ZMod 112611974941) ^ 301908780 = (6 : ZMod 112611974941) ^ (150954390 + 150954390) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 150954390 * (6 : ZMod 112611974941) ^ 150954390 := by rw [pow_add]
          _ = 45150196272 := by rw [factor_4_27]; decide
      change (6 : ZMod 112611974941) ^ 301908780 ≠ 1
      rw [factor_4_28]
      decide
    ·
      have factor_5_0 : (6 : ZMod 112611974941) ^ 1 = 6 := by norm_num
      have factor_5_1 : (6 : ZMod 112611974941) ^ 2 = 36 := by
        calc
          (6 : ZMod 112611974941) ^ 2 = (6 : ZMod 112611974941) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 1 * (6 : ZMod 112611974941) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_5_0]; decide
      have factor_5_2 : (6 : ZMod 112611974941) ^ 4 = 1296 := by
        calc
          (6 : ZMod 112611974941) ^ 4 = (6 : ZMod 112611974941) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 2 * (6 : ZMod 112611974941) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_5_1]; decide
      have factor_5_3 : (6 : ZMod 112611974941) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 112611974941) ^ 8 = (6 : ZMod 112611974941) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 4 * (6 : ZMod 112611974941) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_5_2]; decide
      have factor_5_4 : (6 : ZMod 112611974941) ^ 17 = 34863203586 := by
        calc
          (6 : ZMod 112611974941) ^ 17 = (6 : ZMod 112611974941) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 8 * (6 : ZMod 112611974941) ^ 8) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 34863203586 := by rw [factor_5_3]; decide
      have factor_5_5 : (6 : ZMod 112611974941) ^ 34 = 58479718097 := by
        calc
          (6 : ZMod 112611974941) ^ 34 = (6 : ZMod 112611974941) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 17 * (6 : ZMod 112611974941) ^ 17 := by rw [pow_add]
          _ = 58479718097 := by rw [factor_5_4]; decide
      have factor_5_6 : (6 : ZMod 112611974941) ^ 69 = 85807303133 := by
        calc
          (6 : ZMod 112611974941) ^ 69 = (6 : ZMod 112611974941) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 34 * (6 : ZMod 112611974941) ^ 34) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 85807303133 := by rw [factor_5_5]; decide
      have factor_5_7 : (6 : ZMod 112611974941) ^ 139 = 90998711346 := by
        calc
          (6 : ZMod 112611974941) ^ 139 = (6 : ZMod 112611974941) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 69 * (6 : ZMod 112611974941) ^ 69) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 90998711346 := by rw [factor_5_6]; decide
      have factor_5_8 : (6 : ZMod 112611974941) ^ 278 = 61307566727 := by
        calc
          (6 : ZMod 112611974941) ^ 278 = (6 : ZMod 112611974941) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 139 * (6 : ZMod 112611974941) ^ 139 := by rw [pow_add]
          _ = 61307566727 := by rw [factor_5_7]; decide
      have factor_5_9 : (6 : ZMod 112611974941) ^ 557 = 60382341596 := by
        calc
          (6 : ZMod 112611974941) ^ 557 = (6 : ZMod 112611974941) ^ (278 + 278 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 278 * (6 : ZMod 112611974941) ^ 278) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 60382341596 := by rw [factor_5_8]; decide
      have factor_5_10 : (6 : ZMod 112611974941) ^ 1114 = 39129777333 := by
        calc
          (6 : ZMod 112611974941) ^ 1114 = (6 : ZMod 112611974941) ^ (557 + 557) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 557 * (6 : ZMod 112611974941) ^ 557 := by rw [pow_add]
          _ = 39129777333 := by rw [factor_5_9]; decide
      have factor_5_11 : (6 : ZMod 112611974941) ^ 2229 = 105762546827 := by
        calc
          (6 : ZMod 112611974941) ^ 2229 = (6 : ZMod 112611974941) ^ (1114 + 1114 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 1114 * (6 : ZMod 112611974941) ^ 1114) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 105762546827 := by rw [factor_5_10]; decide
      have factor_5_12 : (6 : ZMod 112611974941) ^ 4458 = 64691967688 := by
        calc
          (6 : ZMod 112611974941) ^ 4458 = (6 : ZMod 112611974941) ^ (2229 + 2229) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 2229 * (6 : ZMod 112611974941) ^ 2229 := by rw [pow_add]
          _ = 64691967688 := by rw [factor_5_11]; decide
      have factor_5_13 : (6 : ZMod 112611974941) ^ 8917 = 60653461542 := by
        calc
          (6 : ZMod 112611974941) ^ 8917 = (6 : ZMod 112611974941) ^ (4458 + 4458 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 4458 * (6 : ZMod 112611974941) ^ 4458) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 60653461542 := by rw [factor_5_12]; decide
      have factor_5_14 : (6 : ZMod 112611974941) ^ 17834 = 74299790494 := by
        calc
          (6 : ZMod 112611974941) ^ 17834 = (6 : ZMod 112611974941) ^ (8917 + 8917) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 8917 * (6 : ZMod 112611974941) ^ 8917 := by rw [pow_add]
          _ = 74299790494 := by rw [factor_5_13]; decide
      have factor_5_15 : (6 : ZMod 112611974941) ^ 35668 = 107436201506 := by
        calc
          (6 : ZMod 112611974941) ^ 35668 = (6 : ZMod 112611974941) ^ (17834 + 17834) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 17834 * (6 : ZMod 112611974941) ^ 17834 := by rw [pow_add]
          _ = 107436201506 := by rw [factor_5_14]; decide
      have factor_5_16 : (6 : ZMod 112611974941) ^ 71336 = 22752553058 := by
        calc
          (6 : ZMod 112611974941) ^ 71336 = (6 : ZMod 112611974941) ^ (35668 + 35668) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 35668 * (6 : ZMod 112611974941) ^ 35668 := by rw [pow_add]
          _ = 22752553058 := by rw [factor_5_15]; decide
      have factor_5_17 : (6 : ZMod 112611974941) ^ 142672 = 14532546298 := by
        calc
          (6 : ZMod 112611974941) ^ 142672 = (6 : ZMod 112611974941) ^ (71336 + 71336) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 71336 * (6 : ZMod 112611974941) ^ 71336 := by rw [pow_add]
          _ = 14532546298 := by rw [factor_5_16]; decide
      have factor_5_18 : (6 : ZMod 112611974941) ^ 285345 = 14490461193 := by
        calc
          (6 : ZMod 112611974941) ^ 285345 = (6 : ZMod 112611974941) ^ (142672 + 142672 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = ((6 : ZMod 112611974941) ^ 142672 * (6 : ZMod 112611974941) ^ 142672) * (6 : ZMod 112611974941) := by rw [pow_succ, pow_add]
          _ = 14490461193 := by rw [factor_5_17]; decide
      have factor_5_19 : (6 : ZMod 112611974941) ^ 570690 = 67838204237 := by
        calc
          (6 : ZMod 112611974941) ^ 570690 = (6 : ZMod 112611974941) ^ (285345 + 285345) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 285345 * (6 : ZMod 112611974941) ^ 285345 := by rw [pow_add]
          _ = 67838204237 := by rw [factor_5_18]; decide
      have factor_5_20 : (6 : ZMod 112611974941) ^ 1141380 = 19592697291 := by
        calc
          (6 : ZMod 112611974941) ^ 1141380 = (6 : ZMod 112611974941) ^ (570690 + 570690) :=
            congrArg (fun n : ℕ => (6 : ZMod 112611974941) ^ n) (by norm_num)
          _ = (6 : ZMod 112611974941) ^ 570690 * (6 : ZMod 112611974941) ^ 570690 := by rw [pow_add]
          _ = 19592697291 := by rw [factor_5_19]; decide
      change (6 : ZMod 112611974941) ^ 1141380 ≠ 1
      rw [factor_5_20]
      decide

#print axioms prime_lucas_112611974941

end TotientTailPeriodKiller
end Erdos249257
