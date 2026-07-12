import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2302624777

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_317762219227 : Nat.Prime 317762219227 := by
  apply lucas_primality 317762219227 (2 : ZMod 317762219227)
  ·
      have fermat_0 : (2 : ZMod 317762219227) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 317762219227) ^ 2 = 4 := by
        calc
          (2 : ZMod 317762219227) ^ 2 = (2 : ZMod 317762219227) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 1 * (2 : ZMod 317762219227) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 317762219227) ^ 4 = 16 := by
        calc
          (2 : ZMod 317762219227) ^ 4 = (2 : ZMod 317762219227) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 2 * (2 : ZMod 317762219227) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 317762219227) ^ 9 = 512 := by
        calc
          (2 : ZMod 317762219227) ^ 9 = (2 : ZMod 317762219227) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 4 * (2 : ZMod 317762219227) ^ 4) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 317762219227) ^ 18 = 262144 := by
        calc
          (2 : ZMod 317762219227) ^ 18 = (2 : ZMod 317762219227) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 9 * (2 : ZMod 317762219227) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 317762219227) ^ 36 = 68719476736 := by
        calc
          (2 : ZMod 317762219227) ^ 36 = (2 : ZMod 317762219227) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 18 * (2 : ZMod 317762219227) ^ 18 := by rw [pow_add]
          _ = 68719476736 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 317762219227) ^ 73 = 39039800589 := by
        calc
          (2 : ZMod 317762219227) ^ 73 = (2 : ZMod 317762219227) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 36 * (2 : ZMod 317762219227) ^ 36) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 39039800589 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 317762219227) ^ 147 = 264942511036 := by
        calc
          (2 : ZMod 317762219227) ^ 147 = (2 : ZMod 317762219227) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 73 * (2 : ZMod 317762219227) ^ 73) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 264942511036 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 317762219227) ^ 295 = 257879344835 := by
        calc
          (2 : ZMod 317762219227) ^ 295 = (2 : ZMod 317762219227) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 147 * (2 : ZMod 317762219227) ^ 147) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 257879344835 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 317762219227) ^ 591 = 137954989429 := by
        calc
          (2 : ZMod 317762219227) ^ 591 = (2 : ZMod 317762219227) ^ (295 + 295 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 295 * (2 : ZMod 317762219227) ^ 295) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 137954989429 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 317762219227) ^ 1183 = 166276831567 := by
        calc
          (2 : ZMod 317762219227) ^ 1183 = (2 : ZMod 317762219227) ^ (591 + 591 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 591 * (2 : ZMod 317762219227) ^ 591) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 166276831567 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 317762219227) ^ 2367 = 312274424258 := by
        calc
          (2 : ZMod 317762219227) ^ 2367 = (2 : ZMod 317762219227) ^ (1183 + 1183 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1183 * (2 : ZMod 317762219227) ^ 1183) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 312274424258 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 317762219227) ^ 4735 = 215936290659 := by
        calc
          (2 : ZMod 317762219227) ^ 4735 = (2 : ZMod 317762219227) ^ (2367 + 2367 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 2367 * (2 : ZMod 317762219227) ^ 2367) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 215936290659 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 317762219227) ^ 9470 = 123513420535 := by
        calc
          (2 : ZMod 317762219227) ^ 9470 = (2 : ZMod 317762219227) ^ (4735 + 4735) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 4735 * (2 : ZMod 317762219227) ^ 4735 := by rw [pow_add]
          _ = 123513420535 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 317762219227) ^ 18940 = 132659705394 := by
        calc
          (2 : ZMod 317762219227) ^ 18940 = (2 : ZMod 317762219227) ^ (9470 + 9470) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 9470 * (2 : ZMod 317762219227) ^ 9470 := by rw [pow_add]
          _ = 132659705394 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 317762219227) ^ 37880 = 300436429952 := by
        calc
          (2 : ZMod 317762219227) ^ 37880 = (2 : ZMod 317762219227) ^ (18940 + 18940) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 18940 * (2 : ZMod 317762219227) ^ 18940 := by rw [pow_add]
          _ = 300436429952 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 317762219227) ^ 75760 = 79927750349 := by
        calc
          (2 : ZMod 317762219227) ^ 75760 = (2 : ZMod 317762219227) ^ (37880 + 37880) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 37880 * (2 : ZMod 317762219227) ^ 37880 := by rw [pow_add]
          _ = 79927750349 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 317762219227) ^ 151520 = 274149644013 := by
        calc
          (2 : ZMod 317762219227) ^ 151520 = (2 : ZMod 317762219227) ^ (75760 + 75760) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 75760 * (2 : ZMod 317762219227) ^ 75760 := by rw [pow_add]
          _ = 274149644013 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 317762219227) ^ 303041 = 113891945491 := by
        calc
          (2 : ZMod 317762219227) ^ 303041 = (2 : ZMod 317762219227) ^ (151520 + 151520 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 151520 * (2 : ZMod 317762219227) ^ 151520) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 113891945491 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 317762219227) ^ 606083 = 263303926780 := by
        calc
          (2 : ZMod 317762219227) ^ 606083 = (2 : ZMod 317762219227) ^ (303041 + 303041 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 303041 * (2 : ZMod 317762219227) ^ 303041) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 263303926780 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 317762219227) ^ 1212166 = 308834571128 := by
        calc
          (2 : ZMod 317762219227) ^ 1212166 = (2 : ZMod 317762219227) ^ (606083 + 606083) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 606083 * (2 : ZMod 317762219227) ^ 606083 := by rw [pow_add]
          _ = 308834571128 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 317762219227) ^ 2424333 = 27171251386 := by
        calc
          (2 : ZMod 317762219227) ^ 2424333 = (2 : ZMod 317762219227) ^ (1212166 + 1212166 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1212166 * (2 : ZMod 317762219227) ^ 1212166) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 27171251386 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 317762219227) ^ 4848666 = 278434642108 := by
        calc
          (2 : ZMod 317762219227) ^ 4848666 = (2 : ZMod 317762219227) ^ (2424333 + 2424333) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 2424333 * (2 : ZMod 317762219227) ^ 2424333 := by rw [pow_add]
          _ = 278434642108 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 317762219227) ^ 9697333 = 234477318912 := by
        calc
          (2 : ZMod 317762219227) ^ 9697333 = (2 : ZMod 317762219227) ^ (4848666 + 4848666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 4848666 * (2 : ZMod 317762219227) ^ 4848666) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 234477318912 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 317762219227) ^ 19394666 = 204672551648 := by
        calc
          (2 : ZMod 317762219227) ^ 19394666 = (2 : ZMod 317762219227) ^ (9697333 + 9697333) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 9697333 * (2 : ZMod 317762219227) ^ 9697333 := by rw [pow_add]
          _ = 204672551648 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 317762219227) ^ 38789333 = 64432804675 := by
        calc
          (2 : ZMod 317762219227) ^ 38789333 = (2 : ZMod 317762219227) ^ (19394666 + 19394666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 19394666 * (2 : ZMod 317762219227) ^ 19394666) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 64432804675 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 317762219227) ^ 77578666 = 83927381391 := by
        calc
          (2 : ZMod 317762219227) ^ 77578666 = (2 : ZMod 317762219227) ^ (38789333 + 38789333) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 38789333 * (2 : ZMod 317762219227) ^ 38789333 := by rw [pow_add]
          _ = 83927381391 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 317762219227) ^ 155157333 = 160462587439 := by
        calc
          (2 : ZMod 317762219227) ^ 155157333 = (2 : ZMod 317762219227) ^ (77578666 + 77578666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 77578666 * (2 : ZMod 317762219227) ^ 77578666) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 160462587439 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 317762219227) ^ 310314667 = 165545445546 := by
        calc
          (2 : ZMod 317762219227) ^ 310314667 = (2 : ZMod 317762219227) ^ (155157333 + 155157333 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 155157333 * (2 : ZMod 317762219227) ^ 155157333) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 165545445546 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 317762219227) ^ 620629334 = 104733256374 := by
        calc
          (2 : ZMod 317762219227) ^ 620629334 = (2 : ZMod 317762219227) ^ (310314667 + 310314667) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 310314667 * (2 : ZMod 317762219227) ^ 310314667 := by rw [pow_add]
          _ = 104733256374 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 317762219227) ^ 1241258668 = 49974587144 := by
        calc
          (2 : ZMod 317762219227) ^ 1241258668 = (2 : ZMod 317762219227) ^ (620629334 + 620629334) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 620629334 * (2 : ZMod 317762219227) ^ 620629334 := by rw [pow_add]
          _ = 49974587144 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 317762219227) ^ 2482517337 = 179945074237 := by
        calc
          (2 : ZMod 317762219227) ^ 2482517337 = (2 : ZMod 317762219227) ^ (1241258668 + 1241258668 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1241258668 * (2 : ZMod 317762219227) ^ 1241258668) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 179945074237 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 317762219227) ^ 4965034675 = 184749623050 := by
        calc
          (2 : ZMod 317762219227) ^ 4965034675 = (2 : ZMod 317762219227) ^ (2482517337 + 2482517337 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 2482517337 * (2 : ZMod 317762219227) ^ 2482517337) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 184749623050 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 317762219227) ^ 9930069350 = 5484994227 := by
        calc
          (2 : ZMod 317762219227) ^ 9930069350 = (2 : ZMod 317762219227) ^ (4965034675 + 4965034675) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 4965034675 * (2 : ZMod 317762219227) ^ 4965034675 := by rw [pow_add]
          _ = 5484994227 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 317762219227) ^ 19860138701 = 105597944724 := by
        calc
          (2 : ZMod 317762219227) ^ 19860138701 = (2 : ZMod 317762219227) ^ (9930069350 + 9930069350 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 9930069350 * (2 : ZMod 317762219227) ^ 9930069350) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 105597944724 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 317762219227) ^ 39720277403 = 53226192248 := by
        calc
          (2 : ZMod 317762219227) ^ 39720277403 = (2 : ZMod 317762219227) ^ (19860138701 + 19860138701 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 19860138701 * (2 : ZMod 317762219227) ^ 19860138701) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 53226192248 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 317762219227) ^ 79440554806 = 54024278043 := by
        calc
          (2 : ZMod 317762219227) ^ 79440554806 = (2 : ZMod 317762219227) ^ (39720277403 + 39720277403) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 39720277403 * (2 : ZMod 317762219227) ^ 39720277403 := by rw [pow_add]
          _ = 54024278043 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 317762219227) ^ 158881109613 = 317762219226 := by
        calc
          (2 : ZMod 317762219227) ^ 158881109613 = (2 : ZMod 317762219227) ^ (79440554806 + 79440554806 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 79440554806 * (2 : ZMod 317762219227) ^ 79440554806) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 317762219226 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 317762219227) ^ 317762219226 = 1 := by
        calc
          (2 : ZMod 317762219227) ^ 317762219226 = (2 : ZMod 317762219227) ^ (158881109613 + 158881109613) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 158881109613 * (2 : ZMod 317762219227) ^ 158881109613 := by rw [pow_add]
          _ = 1 := by rw [fermat_37]; decide
      simpa using fermat_38
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (2302624777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (2302624777, 1)] : List FactorBlock).map factorBlockValue).prod = 317762219227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_2302624777) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 317762219227) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 317762219227) ^ 2 = 4 := by
        calc
          (2 : ZMod 317762219227) ^ 2 = (2 : ZMod 317762219227) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 1 * (2 : ZMod 317762219227) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 317762219227) ^ 4 = 16 := by
        calc
          (2 : ZMod 317762219227) ^ 4 = (2 : ZMod 317762219227) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 2 * (2 : ZMod 317762219227) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 317762219227) ^ 9 = 512 := by
        calc
          (2 : ZMod 317762219227) ^ 9 = (2 : ZMod 317762219227) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 4 * (2 : ZMod 317762219227) ^ 4) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 317762219227) ^ 18 = 262144 := by
        calc
          (2 : ZMod 317762219227) ^ 18 = (2 : ZMod 317762219227) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 9 * (2 : ZMod 317762219227) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 317762219227) ^ 36 = 68719476736 := by
        calc
          (2 : ZMod 317762219227) ^ 36 = (2 : ZMod 317762219227) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 18 * (2 : ZMod 317762219227) ^ 18 := by rw [pow_add]
          _ = 68719476736 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 317762219227) ^ 73 = 39039800589 := by
        calc
          (2 : ZMod 317762219227) ^ 73 = (2 : ZMod 317762219227) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 36 * (2 : ZMod 317762219227) ^ 36) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 39039800589 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 317762219227) ^ 147 = 264942511036 := by
        calc
          (2 : ZMod 317762219227) ^ 147 = (2 : ZMod 317762219227) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 73 * (2 : ZMod 317762219227) ^ 73) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 264942511036 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 317762219227) ^ 295 = 257879344835 := by
        calc
          (2 : ZMod 317762219227) ^ 295 = (2 : ZMod 317762219227) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 147 * (2 : ZMod 317762219227) ^ 147) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 257879344835 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 317762219227) ^ 591 = 137954989429 := by
        calc
          (2 : ZMod 317762219227) ^ 591 = (2 : ZMod 317762219227) ^ (295 + 295 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 295 * (2 : ZMod 317762219227) ^ 295) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 137954989429 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 317762219227) ^ 1183 = 166276831567 := by
        calc
          (2 : ZMod 317762219227) ^ 1183 = (2 : ZMod 317762219227) ^ (591 + 591 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 591 * (2 : ZMod 317762219227) ^ 591) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 166276831567 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 317762219227) ^ 2367 = 312274424258 := by
        calc
          (2 : ZMod 317762219227) ^ 2367 = (2 : ZMod 317762219227) ^ (1183 + 1183 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1183 * (2 : ZMod 317762219227) ^ 1183) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 312274424258 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 317762219227) ^ 4735 = 215936290659 := by
        calc
          (2 : ZMod 317762219227) ^ 4735 = (2 : ZMod 317762219227) ^ (2367 + 2367 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 2367 * (2 : ZMod 317762219227) ^ 2367) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 215936290659 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 317762219227) ^ 9470 = 123513420535 := by
        calc
          (2 : ZMod 317762219227) ^ 9470 = (2 : ZMod 317762219227) ^ (4735 + 4735) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 4735 * (2 : ZMod 317762219227) ^ 4735 := by rw [pow_add]
          _ = 123513420535 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 317762219227) ^ 18940 = 132659705394 := by
        calc
          (2 : ZMod 317762219227) ^ 18940 = (2 : ZMod 317762219227) ^ (9470 + 9470) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 9470 * (2 : ZMod 317762219227) ^ 9470 := by rw [pow_add]
          _ = 132659705394 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 317762219227) ^ 37880 = 300436429952 := by
        calc
          (2 : ZMod 317762219227) ^ 37880 = (2 : ZMod 317762219227) ^ (18940 + 18940) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 18940 * (2 : ZMod 317762219227) ^ 18940 := by rw [pow_add]
          _ = 300436429952 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 317762219227) ^ 75760 = 79927750349 := by
        calc
          (2 : ZMod 317762219227) ^ 75760 = (2 : ZMod 317762219227) ^ (37880 + 37880) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 37880 * (2 : ZMod 317762219227) ^ 37880 := by rw [pow_add]
          _ = 79927750349 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 317762219227) ^ 151520 = 274149644013 := by
        calc
          (2 : ZMod 317762219227) ^ 151520 = (2 : ZMod 317762219227) ^ (75760 + 75760) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 75760 * (2 : ZMod 317762219227) ^ 75760 := by rw [pow_add]
          _ = 274149644013 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 317762219227) ^ 303041 = 113891945491 := by
        calc
          (2 : ZMod 317762219227) ^ 303041 = (2 : ZMod 317762219227) ^ (151520 + 151520 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 151520 * (2 : ZMod 317762219227) ^ 151520) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 113891945491 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 317762219227) ^ 606083 = 263303926780 := by
        calc
          (2 : ZMod 317762219227) ^ 606083 = (2 : ZMod 317762219227) ^ (303041 + 303041 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 303041 * (2 : ZMod 317762219227) ^ 303041) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 263303926780 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 317762219227) ^ 1212166 = 308834571128 := by
        calc
          (2 : ZMod 317762219227) ^ 1212166 = (2 : ZMod 317762219227) ^ (606083 + 606083) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 606083 * (2 : ZMod 317762219227) ^ 606083 := by rw [pow_add]
          _ = 308834571128 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 317762219227) ^ 2424333 = 27171251386 := by
        calc
          (2 : ZMod 317762219227) ^ 2424333 = (2 : ZMod 317762219227) ^ (1212166 + 1212166 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1212166 * (2 : ZMod 317762219227) ^ 1212166) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 27171251386 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 317762219227) ^ 4848666 = 278434642108 := by
        calc
          (2 : ZMod 317762219227) ^ 4848666 = (2 : ZMod 317762219227) ^ (2424333 + 2424333) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 2424333 * (2 : ZMod 317762219227) ^ 2424333 := by rw [pow_add]
          _ = 278434642108 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 317762219227) ^ 9697333 = 234477318912 := by
        calc
          (2 : ZMod 317762219227) ^ 9697333 = (2 : ZMod 317762219227) ^ (4848666 + 4848666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 4848666 * (2 : ZMod 317762219227) ^ 4848666) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 234477318912 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 317762219227) ^ 19394666 = 204672551648 := by
        calc
          (2 : ZMod 317762219227) ^ 19394666 = (2 : ZMod 317762219227) ^ (9697333 + 9697333) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 9697333 * (2 : ZMod 317762219227) ^ 9697333 := by rw [pow_add]
          _ = 204672551648 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 317762219227) ^ 38789333 = 64432804675 := by
        calc
          (2 : ZMod 317762219227) ^ 38789333 = (2 : ZMod 317762219227) ^ (19394666 + 19394666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 19394666 * (2 : ZMod 317762219227) ^ 19394666) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 64432804675 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 317762219227) ^ 77578666 = 83927381391 := by
        calc
          (2 : ZMod 317762219227) ^ 77578666 = (2 : ZMod 317762219227) ^ (38789333 + 38789333) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 38789333 * (2 : ZMod 317762219227) ^ 38789333 := by rw [pow_add]
          _ = 83927381391 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 317762219227) ^ 155157333 = 160462587439 := by
        calc
          (2 : ZMod 317762219227) ^ 155157333 = (2 : ZMod 317762219227) ^ (77578666 + 77578666 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 77578666 * (2 : ZMod 317762219227) ^ 77578666) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 160462587439 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 317762219227) ^ 310314667 = 165545445546 := by
        calc
          (2 : ZMod 317762219227) ^ 310314667 = (2 : ZMod 317762219227) ^ (155157333 + 155157333 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 155157333 * (2 : ZMod 317762219227) ^ 155157333) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 165545445546 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 317762219227) ^ 620629334 = 104733256374 := by
        calc
          (2 : ZMod 317762219227) ^ 620629334 = (2 : ZMod 317762219227) ^ (310314667 + 310314667) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 310314667 * (2 : ZMod 317762219227) ^ 310314667 := by rw [pow_add]
          _ = 104733256374 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 317762219227) ^ 1241258668 = 49974587144 := by
        calc
          (2 : ZMod 317762219227) ^ 1241258668 = (2 : ZMod 317762219227) ^ (620629334 + 620629334) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 620629334 * (2 : ZMod 317762219227) ^ 620629334 := by rw [pow_add]
          _ = 49974587144 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 317762219227) ^ 2482517337 = 179945074237 := by
        calc
          (2 : ZMod 317762219227) ^ 2482517337 = (2 : ZMod 317762219227) ^ (1241258668 + 1241258668 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1241258668 * (2 : ZMod 317762219227) ^ 1241258668) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 179945074237 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 317762219227) ^ 4965034675 = 184749623050 := by
        calc
          (2 : ZMod 317762219227) ^ 4965034675 = (2 : ZMod 317762219227) ^ (2482517337 + 2482517337 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 2482517337 * (2 : ZMod 317762219227) ^ 2482517337) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 184749623050 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 317762219227) ^ 9930069350 = 5484994227 := by
        calc
          (2 : ZMod 317762219227) ^ 9930069350 = (2 : ZMod 317762219227) ^ (4965034675 + 4965034675) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 4965034675 * (2 : ZMod 317762219227) ^ 4965034675 := by rw [pow_add]
          _ = 5484994227 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 317762219227) ^ 19860138701 = 105597944724 := by
        calc
          (2 : ZMod 317762219227) ^ 19860138701 = (2 : ZMod 317762219227) ^ (9930069350 + 9930069350 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 9930069350 * (2 : ZMod 317762219227) ^ 9930069350) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 105597944724 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 317762219227) ^ 39720277403 = 53226192248 := by
        calc
          (2 : ZMod 317762219227) ^ 39720277403 = (2 : ZMod 317762219227) ^ (19860138701 + 19860138701 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 19860138701 * (2 : ZMod 317762219227) ^ 19860138701) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 53226192248 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 317762219227) ^ 79440554806 = 54024278043 := by
        calc
          (2 : ZMod 317762219227) ^ 79440554806 = (2 : ZMod 317762219227) ^ (39720277403 + 39720277403) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 39720277403 * (2 : ZMod 317762219227) ^ 39720277403 := by rw [pow_add]
          _ = 54024278043 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 317762219227) ^ 158881109613 = 317762219226 := by
        calc
          (2 : ZMod 317762219227) ^ 158881109613 = (2 : ZMod 317762219227) ^ (79440554806 + 79440554806 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 79440554806 * (2 : ZMod 317762219227) ^ 79440554806) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 317762219226 := by rw [factor_0_36]; decide
      change (2 : ZMod 317762219227) ^ 158881109613 ≠ 1
      rw [factor_0_37]
      decide
    ·
      have factor_1_0 : (2 : ZMod 317762219227) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 317762219227) ^ 3 = 8 := by
        calc
          (2 : ZMod 317762219227) ^ 3 = (2 : ZMod 317762219227) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1 * (2 : ZMod 317762219227) ^ 1) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 317762219227) ^ 6 = 64 := by
        calc
          (2 : ZMod 317762219227) ^ 6 = (2 : ZMod 317762219227) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 3 * (2 : ZMod 317762219227) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 317762219227) ^ 12 = 4096 := by
        calc
          (2 : ZMod 317762219227) ^ 12 = (2 : ZMod 317762219227) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 6 * (2 : ZMod 317762219227) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 317762219227) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 317762219227) ^ 24 = (2 : ZMod 317762219227) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 12 * (2 : ZMod 317762219227) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 317762219227) ^ 49 = 193063170295 := by
        calc
          (2 : ZMod 317762219227) ^ 49 = (2 : ZMod 317762219227) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 24 * (2 : ZMod 317762219227) ^ 24) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 193063170295 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 317762219227) ^ 98 = 109029252752 := by
        calc
          (2 : ZMod 317762219227) ^ 98 = (2 : ZMod 317762219227) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 49 * (2 : ZMod 317762219227) ^ 49 := by rw [pow_add]
          _ = 109029252752 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 317762219227) ^ 197 = 9548289593 := by
        calc
          (2 : ZMod 317762219227) ^ 197 = (2 : ZMod 317762219227) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 98 * (2 : ZMod 317762219227) ^ 98) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 9548289593 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 317762219227) ^ 394 = 270895459047 := by
        calc
          (2 : ZMod 317762219227) ^ 394 = (2 : ZMod 317762219227) ^ (197 + 197) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 197 * (2 : ZMod 317762219227) ^ 197 := by rw [pow_add]
          _ = 270895459047 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 317762219227) ^ 789 = 69795648665 := by
        calc
          (2 : ZMod 317762219227) ^ 789 = (2 : ZMod 317762219227) ^ (394 + 394 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 394 * (2 : ZMod 317762219227) ^ 394) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 69795648665 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 317762219227) ^ 1578 = 307360281590 := by
        calc
          (2 : ZMod 317762219227) ^ 1578 = (2 : ZMod 317762219227) ^ (789 + 789) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 789 * (2 : ZMod 317762219227) ^ 789 := by rw [pow_add]
          _ = 307360281590 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 317762219227) ^ 3156 = 228425047627 := by
        calc
          (2 : ZMod 317762219227) ^ 3156 = (2 : ZMod 317762219227) ^ (1578 + 1578) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 1578 * (2 : ZMod 317762219227) ^ 1578 := by rw [pow_add]
          _ = 228425047627 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 317762219227) ^ 6313 = 260243020092 := by
        calc
          (2 : ZMod 317762219227) ^ 6313 = (2 : ZMod 317762219227) ^ (3156 + 3156 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 3156 * (2 : ZMod 317762219227) ^ 3156) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 260243020092 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 317762219227) ^ 12626 = 89605995292 := by
        calc
          (2 : ZMod 317762219227) ^ 12626 = (2 : ZMod 317762219227) ^ (6313 + 6313) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 6313 * (2 : ZMod 317762219227) ^ 6313 := by rw [pow_add]
          _ = 89605995292 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 317762219227) ^ 25253 = 175865003428 := by
        calc
          (2 : ZMod 317762219227) ^ 25253 = (2 : ZMod 317762219227) ^ (12626 + 12626 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 12626 * (2 : ZMod 317762219227) ^ 12626) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 175865003428 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 317762219227) ^ 50506 = 89484762600 := by
        calc
          (2 : ZMod 317762219227) ^ 50506 = (2 : ZMod 317762219227) ^ (25253 + 25253) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 25253 * (2 : ZMod 317762219227) ^ 25253 := by rw [pow_add]
          _ = 89484762600 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 317762219227) ^ 101013 = 49476022136 := by
        calc
          (2 : ZMod 317762219227) ^ 101013 = (2 : ZMod 317762219227) ^ (50506 + 50506 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 50506 * (2 : ZMod 317762219227) ^ 50506) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 49476022136 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 317762219227) ^ 202027 = 180563702331 := by
        calc
          (2 : ZMod 317762219227) ^ 202027 = (2 : ZMod 317762219227) ^ (101013 + 101013 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 101013 * (2 : ZMod 317762219227) ^ 101013) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 180563702331 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 317762219227) ^ 404055 = 178406639561 := by
        calc
          (2 : ZMod 317762219227) ^ 404055 = (2 : ZMod 317762219227) ^ (202027 + 202027 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 202027 * (2 : ZMod 317762219227) ^ 202027) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 178406639561 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 317762219227) ^ 808111 = 165169186084 := by
        calc
          (2 : ZMod 317762219227) ^ 808111 = (2 : ZMod 317762219227) ^ (404055 + 404055 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 404055 * (2 : ZMod 317762219227) ^ 404055) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 165169186084 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 317762219227) ^ 1616222 = 61183333414 := by
        calc
          (2 : ZMod 317762219227) ^ 1616222 = (2 : ZMod 317762219227) ^ (808111 + 808111) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 808111 * (2 : ZMod 317762219227) ^ 808111 := by rw [pow_add]
          _ = 61183333414 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 317762219227) ^ 3232444 = 116767509238 := by
        calc
          (2 : ZMod 317762219227) ^ 3232444 = (2 : ZMod 317762219227) ^ (1616222 + 1616222) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 1616222 * (2 : ZMod 317762219227) ^ 1616222 := by rw [pow_add]
          _ = 116767509238 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 317762219227) ^ 6464888 = 280290913614 := by
        calc
          (2 : ZMod 317762219227) ^ 6464888 = (2 : ZMod 317762219227) ^ (3232444 + 3232444) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 3232444 * (2 : ZMod 317762219227) ^ 3232444 := by rw [pow_add]
          _ = 280290913614 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 317762219227) ^ 12929777 = 134645201662 := by
        calc
          (2 : ZMod 317762219227) ^ 12929777 = (2 : ZMod 317762219227) ^ (6464888 + 6464888 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 6464888 * (2 : ZMod 317762219227) ^ 6464888) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 134645201662 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 317762219227) ^ 25859555 = 114239812015 := by
        calc
          (2 : ZMod 317762219227) ^ 25859555 = (2 : ZMod 317762219227) ^ (12929777 + 12929777 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 12929777 * (2 : ZMod 317762219227) ^ 12929777) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 114239812015 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 317762219227) ^ 51719111 = 231386952128 := by
        calc
          (2 : ZMod 317762219227) ^ 51719111 = (2 : ZMod 317762219227) ^ (25859555 + 25859555 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 25859555 * (2 : ZMod 317762219227) ^ 25859555) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 231386952128 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 317762219227) ^ 103438222 = 163789596800 := by
        calc
          (2 : ZMod 317762219227) ^ 103438222 = (2 : ZMod 317762219227) ^ (51719111 + 51719111) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 51719111 * (2 : ZMod 317762219227) ^ 51719111 := by rw [pow_add]
          _ = 163789596800 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 317762219227) ^ 206876444 = 302888952849 := by
        calc
          (2 : ZMod 317762219227) ^ 206876444 = (2 : ZMod 317762219227) ^ (103438222 + 103438222) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 103438222 * (2 : ZMod 317762219227) ^ 103438222 := by rw [pow_add]
          _ = 302888952849 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 317762219227) ^ 413752889 = 292451592980 := by
        calc
          (2 : ZMod 317762219227) ^ 413752889 = (2 : ZMod 317762219227) ^ (206876444 + 206876444 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 206876444 * (2 : ZMod 317762219227) ^ 206876444) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 292451592980 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 317762219227) ^ 827505779 = 226545722419 := by
        calc
          (2 : ZMod 317762219227) ^ 827505779 = (2 : ZMod 317762219227) ^ (413752889 + 413752889 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 413752889 * (2 : ZMod 317762219227) ^ 413752889) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 226545722419 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 317762219227) ^ 1655011558 = 146221399465 := by
        calc
          (2 : ZMod 317762219227) ^ 1655011558 = (2 : ZMod 317762219227) ^ (827505779 + 827505779) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 827505779 * (2 : ZMod 317762219227) ^ 827505779 := by rw [pow_add]
          _ = 146221399465 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 317762219227) ^ 3310023116 = 262216381734 := by
        calc
          (2 : ZMod 317762219227) ^ 3310023116 = (2 : ZMod 317762219227) ^ (1655011558 + 1655011558) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 1655011558 * (2 : ZMod 317762219227) ^ 1655011558 := by rw [pow_add]
          _ = 262216381734 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 317762219227) ^ 6620046233 = 152497821037 := by
        calc
          (2 : ZMod 317762219227) ^ 6620046233 = (2 : ZMod 317762219227) ^ (3310023116 + 3310023116 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 3310023116 * (2 : ZMod 317762219227) ^ 3310023116) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 152497821037 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 317762219227) ^ 13240092467 = 106174718071 := by
        calc
          (2 : ZMod 317762219227) ^ 13240092467 = (2 : ZMod 317762219227) ^ (6620046233 + 6620046233 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 6620046233 * (2 : ZMod 317762219227) ^ 6620046233) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 106174718071 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 317762219227) ^ 26480184935 = 251897213835 := by
        calc
          (2 : ZMod 317762219227) ^ 26480184935 = (2 : ZMod 317762219227) ^ (13240092467 + 13240092467 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 13240092467 * (2 : ZMod 317762219227) ^ 13240092467) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 251897213835 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 317762219227) ^ 52960369871 = 252302797544 := by
        calc
          (2 : ZMod 317762219227) ^ 52960369871 = (2 : ZMod 317762219227) ^ (26480184935 + 26480184935 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 26480184935 * (2 : ZMod 317762219227) ^ 26480184935) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 252302797544 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 317762219227) ^ 105920739742 = 252302797543 := by
        calc
          (2 : ZMod 317762219227) ^ 105920739742 = (2 : ZMod 317762219227) ^ (52960369871 + 52960369871) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 52960369871 * (2 : ZMod 317762219227) ^ 52960369871 := by rw [pow_add]
          _ = 252302797543 := by rw [factor_1_35]; decide
      change (2 : ZMod 317762219227) ^ 105920739742 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (2 : ZMod 317762219227) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 317762219227) ^ 3 = 8 := by
        calc
          (2 : ZMod 317762219227) ^ 3 = (2 : ZMod 317762219227) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1 * (2 : ZMod 317762219227) ^ 1) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 317762219227) ^ 6 = 64 := by
        calc
          (2 : ZMod 317762219227) ^ 6 = (2 : ZMod 317762219227) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 3 * (2 : ZMod 317762219227) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 317762219227) ^ 12 = 4096 := by
        calc
          (2 : ZMod 317762219227) ^ 12 = (2 : ZMod 317762219227) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 6 * (2 : ZMod 317762219227) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 317762219227) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 317762219227) ^ 25 = (2 : ZMod 317762219227) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 12 * (2 : ZMod 317762219227) ^ 12) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 317762219227) ^ 51 = 136728242726 := by
        calc
          (2 : ZMod 317762219227) ^ 51 = (2 : ZMod 317762219227) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 25 * (2 : ZMod 317762219227) ^ 25) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 136728242726 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 317762219227) ^ 102 = 155656947897 := by
        calc
          (2 : ZMod 317762219227) ^ 102 = (2 : ZMod 317762219227) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 51 * (2 : ZMod 317762219227) ^ 51 := by rw [pow_add]
          _ = 155656947897 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 317762219227) ^ 205 = 220026601219 := by
        calc
          (2 : ZMod 317762219227) ^ 205 = (2 : ZMod 317762219227) ^ (102 + 102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 102 * (2 : ZMod 317762219227) ^ 102) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 220026601219 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 317762219227) ^ 411 = 59231783404 := by
        calc
          (2 : ZMod 317762219227) ^ 411 = (2 : ZMod 317762219227) ^ (205 + 205 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 205 * (2 : ZMod 317762219227) ^ 205) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 59231783404 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 317762219227) ^ 823 = 25134352846 := by
        calc
          (2 : ZMod 317762219227) ^ 823 = (2 : ZMod 317762219227) ^ (411 + 411 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 411 * (2 : ZMod 317762219227) ^ 411) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 25134352846 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 317762219227) ^ 1646 = 203137858386 := by
        calc
          (2 : ZMod 317762219227) ^ 1646 = (2 : ZMod 317762219227) ^ (823 + 823) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 823 * (2 : ZMod 317762219227) ^ 823 := by rw [pow_add]
          _ = 203137858386 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 317762219227) ^ 3293 = 165917017352 := by
        calc
          (2 : ZMod 317762219227) ^ 3293 = (2 : ZMod 317762219227) ^ (1646 + 1646 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1646 * (2 : ZMod 317762219227) ^ 1646) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 165917017352 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 317762219227) ^ 6587 = 148473010299 := by
        calc
          (2 : ZMod 317762219227) ^ 6587 = (2 : ZMod 317762219227) ^ (3293 + 3293 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 3293 * (2 : ZMod 317762219227) ^ 3293) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 148473010299 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 317762219227) ^ 13175 = 89620506800 := by
        calc
          (2 : ZMod 317762219227) ^ 13175 = (2 : ZMod 317762219227) ^ (6587 + 6587 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 6587 * (2 : ZMod 317762219227) ^ 6587) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 89620506800 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 317762219227) ^ 26351 = 5794023564 := by
        calc
          (2 : ZMod 317762219227) ^ 26351 = (2 : ZMod 317762219227) ^ (13175 + 13175 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 13175 * (2 : ZMod 317762219227) ^ 13175) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 5794023564 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 317762219227) ^ 52702 = 314048736395 := by
        calc
          (2 : ZMod 317762219227) ^ 52702 = (2 : ZMod 317762219227) ^ (26351 + 26351) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 26351 * (2 : ZMod 317762219227) ^ 26351 := by rw [pow_add]
          _ = 314048736395 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 317762219227) ^ 105405 = 140903096950 := by
        calc
          (2 : ZMod 317762219227) ^ 105405 = (2 : ZMod 317762219227) ^ (52702 + 52702 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 52702 * (2 : ZMod 317762219227) ^ 52702) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 140903096950 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 317762219227) ^ 210811 = 170261919233 := by
        calc
          (2 : ZMod 317762219227) ^ 210811 = (2 : ZMod 317762219227) ^ (105405 + 105405 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 105405 * (2 : ZMod 317762219227) ^ 105405) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 170261919233 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 317762219227) ^ 421623 = 64233737551 := by
        calc
          (2 : ZMod 317762219227) ^ 421623 = (2 : ZMod 317762219227) ^ (210811 + 210811 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 210811 * (2 : ZMod 317762219227) ^ 210811) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 64233737551 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 317762219227) ^ 843246 = 221629264638 := by
        calc
          (2 : ZMod 317762219227) ^ 843246 = (2 : ZMod 317762219227) ^ (421623 + 421623) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 421623 * (2 : ZMod 317762219227) ^ 421623 := by rw [pow_add]
          _ = 221629264638 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 317762219227) ^ 1686492 = 191009330401 := by
        calc
          (2 : ZMod 317762219227) ^ 1686492 = (2 : ZMod 317762219227) ^ (843246 + 843246) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 843246 * (2 : ZMod 317762219227) ^ 843246 := by rw [pow_add]
          _ = 191009330401 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 317762219227) ^ 3372985 = 157790751093 := by
        calc
          (2 : ZMod 317762219227) ^ 3372985 = (2 : ZMod 317762219227) ^ (1686492 + 1686492 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1686492 * (2 : ZMod 317762219227) ^ 1686492) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 157790751093 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 317762219227) ^ 6745971 = 38576662001 := by
        calc
          (2 : ZMod 317762219227) ^ 6745971 = (2 : ZMod 317762219227) ^ (3372985 + 3372985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 3372985 * (2 : ZMod 317762219227) ^ 3372985) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 38576662001 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 317762219227) ^ 13491942 = 223648449862 := by
        calc
          (2 : ZMod 317762219227) ^ 13491942 = (2 : ZMod 317762219227) ^ (6745971 + 6745971) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 6745971 * (2 : ZMod 317762219227) ^ 6745971 := by rw [pow_add]
          _ = 223648449862 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 317762219227) ^ 26983884 = 37064509576 := by
        calc
          (2 : ZMod 317762219227) ^ 26983884 = (2 : ZMod 317762219227) ^ (13491942 + 13491942) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 13491942 * (2 : ZMod 317762219227) ^ 13491942 := by rw [pow_add]
          _ = 37064509576 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 317762219227) ^ 53967768 = 287897746335 := by
        calc
          (2 : ZMod 317762219227) ^ 53967768 = (2 : ZMod 317762219227) ^ (26983884 + 26983884) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 26983884 * (2 : ZMod 317762219227) ^ 26983884 := by rw [pow_add]
          _ = 287897746335 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 317762219227) ^ 107935536 = 288639199578 := by
        calc
          (2 : ZMod 317762219227) ^ 107935536 = (2 : ZMod 317762219227) ^ (53967768 + 53967768) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 53967768 * (2 : ZMod 317762219227) ^ 53967768 := by rw [pow_add]
          _ = 288639199578 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 317762219227) ^ 215871072 = 66854888348 := by
        calc
          (2 : ZMod 317762219227) ^ 215871072 = (2 : ZMod 317762219227) ^ (107935536 + 107935536) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 107935536 * (2 : ZMod 317762219227) ^ 107935536 := by rw [pow_add]
          _ = 66854888348 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 317762219227) ^ 431742145 = 24719984401 := by
        calc
          (2 : ZMod 317762219227) ^ 431742145 = (2 : ZMod 317762219227) ^ (215871072 + 215871072 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 215871072 * (2 : ZMod 317762219227) ^ 215871072) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 24719984401 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 317762219227) ^ 863484291 = 206900529900 := by
        calc
          (2 : ZMod 317762219227) ^ 863484291 = (2 : ZMod 317762219227) ^ (431742145 + 431742145 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 431742145 * (2 : ZMod 317762219227) ^ 431742145) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 206900529900 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 317762219227) ^ 1726968582 = 156350187239 := by
        calc
          (2 : ZMod 317762219227) ^ 1726968582 = (2 : ZMod 317762219227) ^ (863484291 + 863484291) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 863484291 * (2 : ZMod 317762219227) ^ 863484291 := by rw [pow_add]
          _ = 156350187239 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 317762219227) ^ 3453937165 = 151497024588 := by
        calc
          (2 : ZMod 317762219227) ^ 3453937165 = (2 : ZMod 317762219227) ^ (1726968582 + 1726968582 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 1726968582 * (2 : ZMod 317762219227) ^ 1726968582) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 151497024588 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 317762219227) ^ 6907874331 = 217208337593 := by
        calc
          (2 : ZMod 317762219227) ^ 6907874331 = (2 : ZMod 317762219227) ^ (3453937165 + 3453937165 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 3453937165 * (2 : ZMod 317762219227) ^ 3453937165) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 217208337593 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 317762219227) ^ 13815748662 = 87612346805 := by
        calc
          (2 : ZMod 317762219227) ^ 13815748662 = (2 : ZMod 317762219227) ^ (6907874331 + 6907874331) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 6907874331 * (2 : ZMod 317762219227) ^ 6907874331 := by rw [pow_add]
          _ = 87612346805 := by rw [factor_2_32]; decide
      change (2 : ZMod 317762219227) ^ 13815748662 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (2 : ZMod 317762219227) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 317762219227) ^ 2 = 4 := by
        calc
          (2 : ZMod 317762219227) ^ 2 = (2 : ZMod 317762219227) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 1 * (2 : ZMod 317762219227) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 317762219227) ^ 4 = 16 := by
        calc
          (2 : ZMod 317762219227) ^ 4 = (2 : ZMod 317762219227) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 2 * (2 : ZMod 317762219227) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 317762219227) ^ 8 = 256 := by
        calc
          (2 : ZMod 317762219227) ^ 8 = (2 : ZMod 317762219227) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 4 * (2 : ZMod 317762219227) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 317762219227) ^ 17 = 131072 := by
        calc
          (2 : ZMod 317762219227) ^ 17 = (2 : ZMod 317762219227) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 8 * (2 : ZMod 317762219227) ^ 8) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 317762219227) ^ 34 = 17179869184 := by
        calc
          (2 : ZMod 317762219227) ^ 34 = (2 : ZMod 317762219227) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 17 * (2 : ZMod 317762219227) ^ 17 := by rw [pow_add]
          _ = 17179869184 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 317762219227) ^ 69 = 181181235852 := by
        calc
          (2 : ZMod 317762219227) ^ 69 = (2 : ZMod 317762219227) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = ((2 : ZMod 317762219227) ^ 34 * (2 : ZMod 317762219227) ^ 34) * (2 : ZMod 317762219227) := by rw [pow_succ, pow_add]
          _ = 181181235852 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 317762219227) ^ 138 = 7965017855 := by
        calc
          (2 : ZMod 317762219227) ^ 138 = (2 : ZMod 317762219227) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (2 : ZMod 317762219227) ^ n) (by norm_num)
          _ = (2 : ZMod 317762219227) ^ 69 * (2 : ZMod 317762219227) ^ 69 := by rw [pow_add]
          _ = 7965017855 := by rw [factor_3_6]; decide
      change (2 : ZMod 317762219227) ^ 138 ≠ 1
      rw [factor_3_7]
      decide

#print axioms prime_lucas_317762219227

end TotientTailPeriodKiller
end Erdos249257
