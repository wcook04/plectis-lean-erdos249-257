import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime924160957

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_792930101107 : Nat.Prime 792930101107 := by
  apply lucas_primality 792930101107 (2 : ZMod 792930101107)
  ·
      have fermat_0 : (2 : ZMod 792930101107) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 792930101107) ^ 2 = 4 := by
        calc
          (2 : ZMod 792930101107) ^ 2 = (2 : ZMod 792930101107) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1 * (2 : ZMod 792930101107) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 792930101107) ^ 5 = 32 := by
        calc
          (2 : ZMod 792930101107) ^ 5 = (2 : ZMod 792930101107) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 2 * (2 : ZMod 792930101107) ^ 2) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 792930101107) ^ 11 = 2048 := by
        calc
          (2 : ZMod 792930101107) ^ 11 = (2 : ZMod 792930101107) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 5 * (2 : ZMod 792930101107) ^ 5) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 792930101107) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 792930101107) ^ 23 = (2 : ZMod 792930101107) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 11 * (2 : ZMod 792930101107) ^ 11) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 792930101107) ^ 46 = 590895280248 := by
        calc
          (2 : ZMod 792930101107) ^ 46 = (2 : ZMod 792930101107) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 23 * (2 : ZMod 792930101107) ^ 23 := by rw [pow_add]
          _ = 590895280248 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 792930101107) ^ 92 = 227330051889 := by
        calc
          (2 : ZMod 792930101107) ^ 92 = (2 : ZMod 792930101107) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 46 * (2 : ZMod 792930101107) ^ 46 := by rw [pow_add]
          _ = 227330051889 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 792930101107) ^ 184 = 145353411459 := by
        calc
          (2 : ZMod 792930101107) ^ 184 = (2 : ZMod 792930101107) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 92 * (2 : ZMod 792930101107) ^ 92 := by rw [pow_add]
          _ = 145353411459 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 792930101107) ^ 369 = 356567152185 := by
        calc
          (2 : ZMod 792930101107) ^ 369 = (2 : ZMod 792930101107) ^ (184 + 184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 184 * (2 : ZMod 792930101107) ^ 184) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 356567152185 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 792930101107) ^ 738 = 746627362467 := by
        calc
          (2 : ZMod 792930101107) ^ 738 = (2 : ZMod 792930101107) ^ (369 + 369) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 369 * (2 : ZMod 792930101107) ^ 369 := by rw [pow_add]
          _ = 746627362467 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 792930101107) ^ 1476 = 560364548023 := by
        calc
          (2 : ZMod 792930101107) ^ 1476 = (2 : ZMod 792930101107) ^ (738 + 738) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 738 * (2 : ZMod 792930101107) ^ 738 := by rw [pow_add]
          _ = 560364548023 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 792930101107) ^ 2953 = 91270548209 := by
        calc
          (2 : ZMod 792930101107) ^ 2953 = (2 : ZMod 792930101107) ^ (1476 + 1476 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1476 * (2 : ZMod 792930101107) ^ 1476) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 91270548209 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 792930101107) ^ 5907 = 307908048594 := by
        calc
          (2 : ZMod 792930101107) ^ 5907 = (2 : ZMod 792930101107) ^ (2953 + 2953 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 2953 * (2 : ZMod 792930101107) ^ 2953) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 307908048594 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 792930101107) ^ 11815 = 97089585173 := by
        calc
          (2 : ZMod 792930101107) ^ 11815 = (2 : ZMod 792930101107) ^ (5907 + 5907 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 5907 * (2 : ZMod 792930101107) ^ 5907) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 97089585173 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 792930101107) ^ 23631 = 746130931006 := by
        calc
          (2 : ZMod 792930101107) ^ 23631 = (2 : ZMod 792930101107) ^ (11815 + 11815 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 11815 * (2 : ZMod 792930101107) ^ 11815) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 746130931006 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 792930101107) ^ 47262 = 632081164733 := by
        calc
          (2 : ZMod 792930101107) ^ 47262 = (2 : ZMod 792930101107) ^ (23631 + 23631) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 23631 * (2 : ZMod 792930101107) ^ 23631 := by rw [pow_add]
          _ = 632081164733 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 792930101107) ^ 94524 = 391610647528 := by
        calc
          (2 : ZMod 792930101107) ^ 94524 = (2 : ZMod 792930101107) ^ (47262 + 47262) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 47262 * (2 : ZMod 792930101107) ^ 47262 := by rw [pow_add]
          _ = 391610647528 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 792930101107) ^ 189049 = 196368803297 := by
        calc
          (2 : ZMod 792930101107) ^ 189049 = (2 : ZMod 792930101107) ^ (94524 + 94524 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 94524 * (2 : ZMod 792930101107) ^ 94524) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 196368803297 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 792930101107) ^ 378098 = 219280961547 := by
        calc
          (2 : ZMod 792930101107) ^ 378098 = (2 : ZMod 792930101107) ^ (189049 + 189049) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 189049 * (2 : ZMod 792930101107) ^ 189049 := by rw [pow_add]
          _ = 219280961547 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 792930101107) ^ 756197 = 693741842426 := by
        calc
          (2 : ZMod 792930101107) ^ 756197 = (2 : ZMod 792930101107) ^ (378098 + 378098 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 378098 * (2 : ZMod 792930101107) ^ 378098) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 693741842426 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 792930101107) ^ 1512394 = 405379176422 := by
        calc
          (2 : ZMod 792930101107) ^ 1512394 = (2 : ZMod 792930101107) ^ (756197 + 756197) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 756197 * (2 : ZMod 792930101107) ^ 756197 := by rw [pow_add]
          _ = 405379176422 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 792930101107) ^ 3024788 = 21181282200 := by
        calc
          (2 : ZMod 792930101107) ^ 3024788 = (2 : ZMod 792930101107) ^ (1512394 + 1512394) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1512394 * (2 : ZMod 792930101107) ^ 1512394 := by rw [pow_add]
          _ = 21181282200 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 792930101107) ^ 6049576 = 33810956701 := by
        calc
          (2 : ZMod 792930101107) ^ 6049576 = (2 : ZMod 792930101107) ^ (3024788 + 3024788) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 3024788 * (2 : ZMod 792930101107) ^ 3024788 := by rw [pow_add]
          _ = 33810956701 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 792930101107) ^ 12099153 = 670985707547 := by
        calc
          (2 : ZMod 792930101107) ^ 12099153 = (2 : ZMod 792930101107) ^ (6049576 + 6049576 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 6049576 * (2 : ZMod 792930101107) ^ 6049576) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 670985707547 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 792930101107) ^ 24198306 = 149012778892 := by
        calc
          (2 : ZMod 792930101107) ^ 24198306 = (2 : ZMod 792930101107) ^ (12099153 + 12099153) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 12099153 * (2 : ZMod 792930101107) ^ 12099153 := by rw [pow_add]
          _ = 149012778892 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 792930101107) ^ 48396612 = 69137547896 := by
        calc
          (2 : ZMod 792930101107) ^ 48396612 = (2 : ZMod 792930101107) ^ (24198306 + 24198306) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 24198306 * (2 : ZMod 792930101107) ^ 24198306 := by rw [pow_add]
          _ = 69137547896 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 792930101107) ^ 96793225 = 495682196247 := by
        calc
          (2 : ZMod 792930101107) ^ 96793225 = (2 : ZMod 792930101107) ^ (48396612 + 48396612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 48396612 * (2 : ZMod 792930101107) ^ 48396612) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 495682196247 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 792930101107) ^ 193586450 = 789608885423 := by
        calc
          (2 : ZMod 792930101107) ^ 193586450 = (2 : ZMod 792930101107) ^ (96793225 + 96793225) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 96793225 * (2 : ZMod 792930101107) ^ 96793225 := by rw [pow_add]
          _ = 789608885423 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 792930101107) ^ 387172900 = 781105279860 := by
        calc
          (2 : ZMod 792930101107) ^ 387172900 = (2 : ZMod 792930101107) ^ (193586450 + 193586450) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 193586450 * (2 : ZMod 792930101107) ^ 193586450 := by rw [pow_add]
          _ = 781105279860 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 792930101107) ^ 774345801 = 264117129237 := by
        calc
          (2 : ZMod 792930101107) ^ 774345801 = (2 : ZMod 792930101107) ^ (387172900 + 387172900 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 387172900 * (2 : ZMod 792930101107) ^ 387172900) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 264117129237 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 792930101107) ^ 1548691603 = 727234621058 := by
        calc
          (2 : ZMod 792930101107) ^ 1548691603 = (2 : ZMod 792930101107) ^ (774345801 + 774345801 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 774345801 * (2 : ZMod 792930101107) ^ 774345801) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 727234621058 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 792930101107) ^ 3097383207 = 101755145430 := by
        calc
          (2 : ZMod 792930101107) ^ 3097383207 = (2 : ZMod 792930101107) ^ (1548691603 + 1548691603 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1548691603 * (2 : ZMod 792930101107) ^ 1548691603) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 101755145430 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 792930101107) ^ 6194766414 = 494317590831 := by
        calc
          (2 : ZMod 792930101107) ^ 6194766414 = (2 : ZMod 792930101107) ^ (3097383207 + 3097383207) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 3097383207 * (2 : ZMod 792930101107) ^ 3097383207 := by rw [pow_add]
          _ = 494317590831 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 792930101107) ^ 12389532829 = 670653958432 := by
        calc
          (2 : ZMod 792930101107) ^ 12389532829 = (2 : ZMod 792930101107) ^ (6194766414 + 6194766414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 6194766414 * (2 : ZMod 792930101107) ^ 6194766414) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 670653958432 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 792930101107) ^ 24779065659 = 118313411382 := by
        calc
          (2 : ZMod 792930101107) ^ 24779065659 = (2 : ZMod 792930101107) ^ (12389532829 + 12389532829 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 12389532829 * (2 : ZMod 792930101107) ^ 12389532829) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 118313411382 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 792930101107) ^ 49558131319 = 185821697424 := by
        calc
          (2 : ZMod 792930101107) ^ 49558131319 = (2 : ZMod 792930101107) ^ (24779065659 + 24779065659 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 24779065659 * (2 : ZMod 792930101107) ^ 24779065659) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 185821697424 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 792930101107) ^ 99116262638 = 513004174188 := by
        calc
          (2 : ZMod 792930101107) ^ 99116262638 = (2 : ZMod 792930101107) ^ (49558131319 + 49558131319) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 49558131319 * (2 : ZMod 792930101107) ^ 49558131319 := by rw [pow_add]
          _ = 513004174188 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 792930101107) ^ 198232525276 = 347830259993 := by
        calc
          (2 : ZMod 792930101107) ^ 198232525276 = (2 : ZMod 792930101107) ^ (99116262638 + 99116262638) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 99116262638 * (2 : ZMod 792930101107) ^ 99116262638 := by rw [pow_add]
          _ = 347830259993 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 792930101107) ^ 396465050553 = 792930101106 := by
        calc
          (2 : ZMod 792930101107) ^ 396465050553 = (2 : ZMod 792930101107) ^ (198232525276 + 198232525276 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 198232525276 * (2 : ZMod 792930101107) ^ 198232525276) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 792930101106 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 792930101107) ^ 792930101106 = 1 := by
        calc
          (2 : ZMod 792930101107) ^ 792930101106 = (2 : ZMod 792930101107) ^ (396465050553 + 396465050553) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 396465050553 * (2 : ZMod 792930101107) ^ 396465050553 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (13, 1), (924160957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (13, 1), (924160957, 1)] : List FactorBlock).map factorBlockValue).prod = 792930101107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_924160957) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 792930101107) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 792930101107) ^ 2 = 4 := by
        calc
          (2 : ZMod 792930101107) ^ 2 = (2 : ZMod 792930101107) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1 * (2 : ZMod 792930101107) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 792930101107) ^ 5 = 32 := by
        calc
          (2 : ZMod 792930101107) ^ 5 = (2 : ZMod 792930101107) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 2 * (2 : ZMod 792930101107) ^ 2) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 792930101107) ^ 11 = 2048 := by
        calc
          (2 : ZMod 792930101107) ^ 11 = (2 : ZMod 792930101107) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 5 * (2 : ZMod 792930101107) ^ 5) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 792930101107) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 792930101107) ^ 23 = (2 : ZMod 792930101107) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 11 * (2 : ZMod 792930101107) ^ 11) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 792930101107) ^ 46 = 590895280248 := by
        calc
          (2 : ZMod 792930101107) ^ 46 = (2 : ZMod 792930101107) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 23 * (2 : ZMod 792930101107) ^ 23 := by rw [pow_add]
          _ = 590895280248 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 792930101107) ^ 92 = 227330051889 := by
        calc
          (2 : ZMod 792930101107) ^ 92 = (2 : ZMod 792930101107) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 46 * (2 : ZMod 792930101107) ^ 46 := by rw [pow_add]
          _ = 227330051889 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 792930101107) ^ 184 = 145353411459 := by
        calc
          (2 : ZMod 792930101107) ^ 184 = (2 : ZMod 792930101107) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 92 * (2 : ZMod 792930101107) ^ 92 := by rw [pow_add]
          _ = 145353411459 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 792930101107) ^ 369 = 356567152185 := by
        calc
          (2 : ZMod 792930101107) ^ 369 = (2 : ZMod 792930101107) ^ (184 + 184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 184 * (2 : ZMod 792930101107) ^ 184) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 356567152185 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 792930101107) ^ 738 = 746627362467 := by
        calc
          (2 : ZMod 792930101107) ^ 738 = (2 : ZMod 792930101107) ^ (369 + 369) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 369 * (2 : ZMod 792930101107) ^ 369 := by rw [pow_add]
          _ = 746627362467 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 792930101107) ^ 1476 = 560364548023 := by
        calc
          (2 : ZMod 792930101107) ^ 1476 = (2 : ZMod 792930101107) ^ (738 + 738) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 738 * (2 : ZMod 792930101107) ^ 738 := by rw [pow_add]
          _ = 560364548023 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 792930101107) ^ 2953 = 91270548209 := by
        calc
          (2 : ZMod 792930101107) ^ 2953 = (2 : ZMod 792930101107) ^ (1476 + 1476 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1476 * (2 : ZMod 792930101107) ^ 1476) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 91270548209 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 792930101107) ^ 5907 = 307908048594 := by
        calc
          (2 : ZMod 792930101107) ^ 5907 = (2 : ZMod 792930101107) ^ (2953 + 2953 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 2953 * (2 : ZMod 792930101107) ^ 2953) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 307908048594 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 792930101107) ^ 11815 = 97089585173 := by
        calc
          (2 : ZMod 792930101107) ^ 11815 = (2 : ZMod 792930101107) ^ (5907 + 5907 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 5907 * (2 : ZMod 792930101107) ^ 5907) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 97089585173 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 792930101107) ^ 23631 = 746130931006 := by
        calc
          (2 : ZMod 792930101107) ^ 23631 = (2 : ZMod 792930101107) ^ (11815 + 11815 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 11815 * (2 : ZMod 792930101107) ^ 11815) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 746130931006 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 792930101107) ^ 47262 = 632081164733 := by
        calc
          (2 : ZMod 792930101107) ^ 47262 = (2 : ZMod 792930101107) ^ (23631 + 23631) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 23631 * (2 : ZMod 792930101107) ^ 23631 := by rw [pow_add]
          _ = 632081164733 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 792930101107) ^ 94524 = 391610647528 := by
        calc
          (2 : ZMod 792930101107) ^ 94524 = (2 : ZMod 792930101107) ^ (47262 + 47262) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 47262 * (2 : ZMod 792930101107) ^ 47262 := by rw [pow_add]
          _ = 391610647528 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 792930101107) ^ 189049 = 196368803297 := by
        calc
          (2 : ZMod 792930101107) ^ 189049 = (2 : ZMod 792930101107) ^ (94524 + 94524 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 94524 * (2 : ZMod 792930101107) ^ 94524) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 196368803297 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 792930101107) ^ 378098 = 219280961547 := by
        calc
          (2 : ZMod 792930101107) ^ 378098 = (2 : ZMod 792930101107) ^ (189049 + 189049) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 189049 * (2 : ZMod 792930101107) ^ 189049 := by rw [pow_add]
          _ = 219280961547 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 792930101107) ^ 756197 = 693741842426 := by
        calc
          (2 : ZMod 792930101107) ^ 756197 = (2 : ZMod 792930101107) ^ (378098 + 378098 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 378098 * (2 : ZMod 792930101107) ^ 378098) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 693741842426 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 792930101107) ^ 1512394 = 405379176422 := by
        calc
          (2 : ZMod 792930101107) ^ 1512394 = (2 : ZMod 792930101107) ^ (756197 + 756197) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 756197 * (2 : ZMod 792930101107) ^ 756197 := by rw [pow_add]
          _ = 405379176422 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 792930101107) ^ 3024788 = 21181282200 := by
        calc
          (2 : ZMod 792930101107) ^ 3024788 = (2 : ZMod 792930101107) ^ (1512394 + 1512394) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1512394 * (2 : ZMod 792930101107) ^ 1512394 := by rw [pow_add]
          _ = 21181282200 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 792930101107) ^ 6049576 = 33810956701 := by
        calc
          (2 : ZMod 792930101107) ^ 6049576 = (2 : ZMod 792930101107) ^ (3024788 + 3024788) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 3024788 * (2 : ZMod 792930101107) ^ 3024788 := by rw [pow_add]
          _ = 33810956701 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 792930101107) ^ 12099153 = 670985707547 := by
        calc
          (2 : ZMod 792930101107) ^ 12099153 = (2 : ZMod 792930101107) ^ (6049576 + 6049576 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 6049576 * (2 : ZMod 792930101107) ^ 6049576) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 670985707547 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 792930101107) ^ 24198306 = 149012778892 := by
        calc
          (2 : ZMod 792930101107) ^ 24198306 = (2 : ZMod 792930101107) ^ (12099153 + 12099153) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 12099153 * (2 : ZMod 792930101107) ^ 12099153 := by rw [pow_add]
          _ = 149012778892 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 792930101107) ^ 48396612 = 69137547896 := by
        calc
          (2 : ZMod 792930101107) ^ 48396612 = (2 : ZMod 792930101107) ^ (24198306 + 24198306) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 24198306 * (2 : ZMod 792930101107) ^ 24198306 := by rw [pow_add]
          _ = 69137547896 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 792930101107) ^ 96793225 = 495682196247 := by
        calc
          (2 : ZMod 792930101107) ^ 96793225 = (2 : ZMod 792930101107) ^ (48396612 + 48396612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 48396612 * (2 : ZMod 792930101107) ^ 48396612) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 495682196247 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 792930101107) ^ 193586450 = 789608885423 := by
        calc
          (2 : ZMod 792930101107) ^ 193586450 = (2 : ZMod 792930101107) ^ (96793225 + 96793225) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 96793225 * (2 : ZMod 792930101107) ^ 96793225 := by rw [pow_add]
          _ = 789608885423 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 792930101107) ^ 387172900 = 781105279860 := by
        calc
          (2 : ZMod 792930101107) ^ 387172900 = (2 : ZMod 792930101107) ^ (193586450 + 193586450) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 193586450 * (2 : ZMod 792930101107) ^ 193586450 := by rw [pow_add]
          _ = 781105279860 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 792930101107) ^ 774345801 = 264117129237 := by
        calc
          (2 : ZMod 792930101107) ^ 774345801 = (2 : ZMod 792930101107) ^ (387172900 + 387172900 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 387172900 * (2 : ZMod 792930101107) ^ 387172900) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 264117129237 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 792930101107) ^ 1548691603 = 727234621058 := by
        calc
          (2 : ZMod 792930101107) ^ 1548691603 = (2 : ZMod 792930101107) ^ (774345801 + 774345801 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 774345801 * (2 : ZMod 792930101107) ^ 774345801) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 727234621058 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 792930101107) ^ 3097383207 = 101755145430 := by
        calc
          (2 : ZMod 792930101107) ^ 3097383207 = (2 : ZMod 792930101107) ^ (1548691603 + 1548691603 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1548691603 * (2 : ZMod 792930101107) ^ 1548691603) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 101755145430 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 792930101107) ^ 6194766414 = 494317590831 := by
        calc
          (2 : ZMod 792930101107) ^ 6194766414 = (2 : ZMod 792930101107) ^ (3097383207 + 3097383207) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 3097383207 * (2 : ZMod 792930101107) ^ 3097383207 := by rw [pow_add]
          _ = 494317590831 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 792930101107) ^ 12389532829 = 670653958432 := by
        calc
          (2 : ZMod 792930101107) ^ 12389532829 = (2 : ZMod 792930101107) ^ (6194766414 + 6194766414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 6194766414 * (2 : ZMod 792930101107) ^ 6194766414) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 670653958432 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 792930101107) ^ 24779065659 = 118313411382 := by
        calc
          (2 : ZMod 792930101107) ^ 24779065659 = (2 : ZMod 792930101107) ^ (12389532829 + 12389532829 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 12389532829 * (2 : ZMod 792930101107) ^ 12389532829) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 118313411382 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 792930101107) ^ 49558131319 = 185821697424 := by
        calc
          (2 : ZMod 792930101107) ^ 49558131319 = (2 : ZMod 792930101107) ^ (24779065659 + 24779065659 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 24779065659 * (2 : ZMod 792930101107) ^ 24779065659) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 185821697424 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 792930101107) ^ 99116262638 = 513004174188 := by
        calc
          (2 : ZMod 792930101107) ^ 99116262638 = (2 : ZMod 792930101107) ^ (49558131319 + 49558131319) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 49558131319 * (2 : ZMod 792930101107) ^ 49558131319 := by rw [pow_add]
          _ = 513004174188 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 792930101107) ^ 198232525276 = 347830259993 := by
        calc
          (2 : ZMod 792930101107) ^ 198232525276 = (2 : ZMod 792930101107) ^ (99116262638 + 99116262638) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 99116262638 * (2 : ZMod 792930101107) ^ 99116262638 := by rw [pow_add]
          _ = 347830259993 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 792930101107) ^ 396465050553 = 792930101106 := by
        calc
          (2 : ZMod 792930101107) ^ 396465050553 = (2 : ZMod 792930101107) ^ (198232525276 + 198232525276 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 198232525276 * (2 : ZMod 792930101107) ^ 198232525276) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 792930101106 := by rw [factor_0_37]; decide
      change (2 : ZMod 792930101107) ^ 396465050553 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (2 : ZMod 792930101107) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 792930101107) ^ 3 = 8 := by
        calc
          (2 : ZMod 792930101107) ^ 3 = (2 : ZMod 792930101107) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1 * (2 : ZMod 792930101107) ^ 1) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 792930101107) ^ 7 = 128 := by
        calc
          (2 : ZMod 792930101107) ^ 7 = (2 : ZMod 792930101107) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 3 * (2 : ZMod 792930101107) ^ 3) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 792930101107) ^ 15 = 32768 := by
        calc
          (2 : ZMod 792930101107) ^ 15 = (2 : ZMod 792930101107) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 7 * (2 : ZMod 792930101107) ^ 7) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 792930101107) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 792930101107) ^ 30 = (2 : ZMod 792930101107) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 15 * (2 : ZMod 792930101107) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 792930101107) ^ 61 = 689334335738 := by
        calc
          (2 : ZMod 792930101107) ^ 61 = (2 : ZMod 792930101107) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 30 * (2 : ZMod 792930101107) ^ 30) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 689334335738 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 792930101107) ^ 123 = 65574826667 := by
        calc
          (2 : ZMod 792930101107) ^ 123 = (2 : ZMod 792930101107) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 61 * (2 : ZMod 792930101107) ^ 61) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 65574826667 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 792930101107) ^ 246 = 656424286056 := by
        calc
          (2 : ZMod 792930101107) ^ 246 = (2 : ZMod 792930101107) ^ (123 + 123) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 123 * (2 : ZMod 792930101107) ^ 123 := by rw [pow_add]
          _ = 656424286056 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 792930101107) ^ 492 = 283937121992 := by
        calc
          (2 : ZMod 792930101107) ^ 492 = (2 : ZMod 792930101107) ^ (246 + 246) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 246 * (2 : ZMod 792930101107) ^ 246 := by rw [pow_add]
          _ = 283937121992 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 792930101107) ^ 984 = 446399509596 := by
        calc
          (2 : ZMod 792930101107) ^ 984 = (2 : ZMod 792930101107) ^ (492 + 492) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 492 * (2 : ZMod 792930101107) ^ 492 := by rw [pow_add]
          _ = 446399509596 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 792930101107) ^ 1969 = 350108630353 := by
        calc
          (2 : ZMod 792930101107) ^ 1969 = (2 : ZMod 792930101107) ^ (984 + 984 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 984 * (2 : ZMod 792930101107) ^ 984) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 350108630353 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 792930101107) ^ 3938 = 414883419764 := by
        calc
          (2 : ZMod 792930101107) ^ 3938 = (2 : ZMod 792930101107) ^ (1969 + 1969) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1969 * (2 : ZMod 792930101107) ^ 1969 := by rw [pow_add]
          _ = 414883419764 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 792930101107) ^ 7877 = 433833284250 := by
        calc
          (2 : ZMod 792930101107) ^ 7877 = (2 : ZMod 792930101107) ^ (3938 + 3938 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 3938 * (2 : ZMod 792930101107) ^ 3938) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 433833284250 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 792930101107) ^ 15754 = 47773041870 := by
        calc
          (2 : ZMod 792930101107) ^ 15754 = (2 : ZMod 792930101107) ^ (7877 + 7877) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 7877 * (2 : ZMod 792930101107) ^ 7877 := by rw [pow_add]
          _ = 47773041870 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 792930101107) ^ 31508 = 347430843753 := by
        calc
          (2 : ZMod 792930101107) ^ 31508 = (2 : ZMod 792930101107) ^ (15754 + 15754) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 15754 * (2 : ZMod 792930101107) ^ 15754 := by rw [pow_add]
          _ = 347430843753 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 792930101107) ^ 63016 = 250472295016 := by
        calc
          (2 : ZMod 792930101107) ^ 63016 = (2 : ZMod 792930101107) ^ (31508 + 31508) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 31508 * (2 : ZMod 792930101107) ^ 31508 := by rw [pow_add]
          _ = 250472295016 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 792930101107) ^ 126032 = 644147468374 := by
        calc
          (2 : ZMod 792930101107) ^ 126032 = (2 : ZMod 792930101107) ^ (63016 + 63016) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 63016 * (2 : ZMod 792930101107) ^ 63016 := by rw [pow_add]
          _ = 644147468374 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 792930101107) ^ 252065 = 707083852523 := by
        calc
          (2 : ZMod 792930101107) ^ 252065 = (2 : ZMod 792930101107) ^ (126032 + 126032 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 126032 * (2 : ZMod 792930101107) ^ 126032) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 707083852523 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 792930101107) ^ 504131 = 339546982256 := by
        calc
          (2 : ZMod 792930101107) ^ 504131 = (2 : ZMod 792930101107) ^ (252065 + 252065 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 252065 * (2 : ZMod 792930101107) ^ 252065) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 339546982256 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 792930101107) ^ 1008262 = 554629264446 := by
        calc
          (2 : ZMod 792930101107) ^ 1008262 = (2 : ZMod 792930101107) ^ (504131 + 504131) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 504131 * (2 : ZMod 792930101107) ^ 504131 := by rw [pow_add]
          _ = 554629264446 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 792930101107) ^ 2016525 = 247940898815 := by
        calc
          (2 : ZMod 792930101107) ^ 2016525 = (2 : ZMod 792930101107) ^ (1008262 + 1008262 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1008262 * (2 : ZMod 792930101107) ^ 1008262) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 247940898815 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 792930101107) ^ 4033051 = 202677478783 := by
        calc
          (2 : ZMod 792930101107) ^ 4033051 = (2 : ZMod 792930101107) ^ (2016525 + 2016525 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 2016525 * (2 : ZMod 792930101107) ^ 2016525) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 202677478783 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 792930101107) ^ 8066102 = 525399766166 := by
        calc
          (2 : ZMod 792930101107) ^ 8066102 = (2 : ZMod 792930101107) ^ (4033051 + 4033051) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 4033051 * (2 : ZMod 792930101107) ^ 4033051 := by rw [pow_add]
          _ = 525399766166 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 792930101107) ^ 16132204 = 480606419133 := by
        calc
          (2 : ZMod 792930101107) ^ 16132204 = (2 : ZMod 792930101107) ^ (8066102 + 8066102) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 8066102 * (2 : ZMod 792930101107) ^ 8066102 := by rw [pow_add]
          _ = 480606419133 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 792930101107) ^ 32264408 = 542780841192 := by
        calc
          (2 : ZMod 792930101107) ^ 32264408 = (2 : ZMod 792930101107) ^ (16132204 + 16132204) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 16132204 * (2 : ZMod 792930101107) ^ 16132204 := by rw [pow_add]
          _ = 542780841192 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 792930101107) ^ 64528816 = 462828120764 := by
        calc
          (2 : ZMod 792930101107) ^ 64528816 = (2 : ZMod 792930101107) ^ (32264408 + 32264408) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 32264408 * (2 : ZMod 792930101107) ^ 32264408 := by rw [pow_add]
          _ = 462828120764 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 792930101107) ^ 129057633 = 464948386676 := by
        calc
          (2 : ZMod 792930101107) ^ 129057633 = (2 : ZMod 792930101107) ^ (64528816 + 64528816 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 64528816 * (2 : ZMod 792930101107) ^ 64528816) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 464948386676 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 792930101107) ^ 258115267 = 363882764769 := by
        calc
          (2 : ZMod 792930101107) ^ 258115267 = (2 : ZMod 792930101107) ^ (129057633 + 129057633 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 129057633 * (2 : ZMod 792930101107) ^ 129057633) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 363882764769 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 792930101107) ^ 516230534 = 763049187324 := by
        calc
          (2 : ZMod 792930101107) ^ 516230534 = (2 : ZMod 792930101107) ^ (258115267 + 258115267) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 258115267 * (2 : ZMod 792930101107) ^ 258115267 := by rw [pow_add]
          _ = 763049187324 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 792930101107) ^ 1032461069 = 3046873635 := by
        calc
          (2 : ZMod 792930101107) ^ 1032461069 = (2 : ZMod 792930101107) ^ (516230534 + 516230534 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 516230534 * (2 : ZMod 792930101107) ^ 516230534) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 3046873635 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 792930101107) ^ 2064922138 = 455401218477 := by
        calc
          (2 : ZMod 792930101107) ^ 2064922138 = (2 : ZMod 792930101107) ^ (1032461069 + 1032461069) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1032461069 * (2 : ZMod 792930101107) ^ 1032461069 := by rw [pow_add]
          _ = 455401218477 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 792930101107) ^ 4129844276 = 551507276049 := by
        calc
          (2 : ZMod 792930101107) ^ 4129844276 = (2 : ZMod 792930101107) ^ (2064922138 + 2064922138) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 2064922138 * (2 : ZMod 792930101107) ^ 2064922138 := by rw [pow_add]
          _ = 551507276049 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 792930101107) ^ 8259688553 = 667070464086 := by
        calc
          (2 : ZMod 792930101107) ^ 8259688553 = (2 : ZMod 792930101107) ^ (4129844276 + 4129844276 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 4129844276 * (2 : ZMod 792930101107) ^ 4129844276) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 667070464086 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 792930101107) ^ 16519377106 = 277512622607 := by
        calc
          (2 : ZMod 792930101107) ^ 16519377106 = (2 : ZMod 792930101107) ^ (8259688553 + 8259688553) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 8259688553 * (2 : ZMod 792930101107) ^ 8259688553 := by rw [pow_add]
          _ = 277512622607 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 792930101107) ^ 33038754212 = 456509772006 := by
        calc
          (2 : ZMod 792930101107) ^ 33038754212 = (2 : ZMod 792930101107) ^ (16519377106 + 16519377106) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 16519377106 * (2 : ZMod 792930101107) ^ 16519377106 := by rw [pow_add]
          _ = 456509772006 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 792930101107) ^ 66077508425 = 213428075084 := by
        calc
          (2 : ZMod 792930101107) ^ 66077508425 = (2 : ZMod 792930101107) ^ (33038754212 + 33038754212 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 33038754212 * (2 : ZMod 792930101107) ^ 33038754212) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 213428075084 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 792930101107) ^ 132155016851 = 508135897004 := by
        calc
          (2 : ZMod 792930101107) ^ 132155016851 = (2 : ZMod 792930101107) ^ (66077508425 + 66077508425 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 66077508425 * (2 : ZMod 792930101107) ^ 66077508425) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 508135897004 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 792930101107) ^ 264310033702 = 508135897003 := by
        calc
          (2 : ZMod 792930101107) ^ 264310033702 = (2 : ZMod 792930101107) ^ (132155016851 + 132155016851) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 132155016851 * (2 : ZMod 792930101107) ^ 132155016851 := by rw [pow_add]
          _ = 508135897003 := by rw [factor_1_36]; decide
      change (2 : ZMod 792930101107) ^ 264310033702 ≠ 1
      rw [factor_1_37]
      decide
    ·
      have factor_2_0 : (2 : ZMod 792930101107) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 792930101107) ^ 2 = 4 := by
        calc
          (2 : ZMod 792930101107) ^ 2 = (2 : ZMod 792930101107) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1 * (2 : ZMod 792930101107) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 792930101107) ^ 4 = 16 := by
        calc
          (2 : ZMod 792930101107) ^ 4 = (2 : ZMod 792930101107) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 2 * (2 : ZMod 792930101107) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 792930101107) ^ 8 = 256 := by
        calc
          (2 : ZMod 792930101107) ^ 8 = (2 : ZMod 792930101107) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 4 * (2 : ZMod 792930101107) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 792930101107) ^ 16 = 65536 := by
        calc
          (2 : ZMod 792930101107) ^ 16 = (2 : ZMod 792930101107) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 8 * (2 : ZMod 792930101107) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 792930101107) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 792930101107) ^ 33 = (2 : ZMod 792930101107) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 16 * (2 : ZMod 792930101107) ^ 16) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 792930101107) ^ 67 = 506241926347 := by
        calc
          (2 : ZMod 792930101107) ^ 67 = (2 : ZMod 792930101107) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 33 * (2 : ZMod 792930101107) ^ 33) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 506241926347 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 792930101107) ^ 134 = 292057926933 := by
        calc
          (2 : ZMod 792930101107) ^ 134 = (2 : ZMod 792930101107) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 67 * (2 : ZMod 792930101107) ^ 67 := by rw [pow_add]
          _ = 292057926933 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 792930101107) ^ 268 = 187364156451 := by
        calc
          (2 : ZMod 792930101107) ^ 268 = (2 : ZMod 792930101107) ^ (134 + 134) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 134 * (2 : ZMod 792930101107) ^ 134 := by rw [pow_add]
          _ = 187364156451 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 792930101107) ^ 537 = 650706487965 := by
        calc
          (2 : ZMod 792930101107) ^ 537 = (2 : ZMod 792930101107) ^ (268 + 268 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 268 * (2 : ZMod 792930101107) ^ 268) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 650706487965 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 792930101107) ^ 1074 = 432335999458 := by
        calc
          (2 : ZMod 792930101107) ^ 1074 = (2 : ZMod 792930101107) ^ (537 + 537) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 537 * (2 : ZMod 792930101107) ^ 537 := by rw [pow_add]
          _ = 432335999458 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 792930101107) ^ 2148 = 216267201010 := by
        calc
          (2 : ZMod 792930101107) ^ 2148 = (2 : ZMod 792930101107) ^ (1074 + 1074) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1074 * (2 : ZMod 792930101107) ^ 1074 := by rw [pow_add]
          _ = 216267201010 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 792930101107) ^ 4296 = 458986649503 := by
        calc
          (2 : ZMod 792930101107) ^ 4296 = (2 : ZMod 792930101107) ^ (2148 + 2148) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 2148 * (2 : ZMod 792930101107) ^ 2148 := by rw [pow_add]
          _ = 458986649503 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 792930101107) ^ 8593 = 253009308296 := by
        calc
          (2 : ZMod 792930101107) ^ 8593 = (2 : ZMod 792930101107) ^ (4296 + 4296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 4296 * (2 : ZMod 792930101107) ^ 4296) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 253009308296 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 792930101107) ^ 17186 = 34884204250 := by
        calc
          (2 : ZMod 792930101107) ^ 17186 = (2 : ZMod 792930101107) ^ (8593 + 8593) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 8593 * (2 : ZMod 792930101107) ^ 8593 := by rw [pow_add]
          _ = 34884204250 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 792930101107) ^ 34372 = 281895522618 := by
        calc
          (2 : ZMod 792930101107) ^ 34372 = (2 : ZMod 792930101107) ^ (17186 + 17186) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 17186 * (2 : ZMod 792930101107) ^ 17186 := by rw [pow_add]
          _ = 281895522618 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 792930101107) ^ 68745 = 365579982068 := by
        calc
          (2 : ZMod 792930101107) ^ 68745 = (2 : ZMod 792930101107) ^ (34372 + 34372 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 34372 * (2 : ZMod 792930101107) ^ 34372) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 365579982068 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 792930101107) ^ 137490 = 635207599215 := by
        calc
          (2 : ZMod 792930101107) ^ 137490 = (2 : ZMod 792930101107) ^ (68745 + 68745) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 68745 * (2 : ZMod 792930101107) ^ 68745 := by rw [pow_add]
          _ = 635207599215 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 792930101107) ^ 274980 = 779753407750 := by
        calc
          (2 : ZMod 792930101107) ^ 274980 = (2 : ZMod 792930101107) ^ (137490 + 137490) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 137490 * (2 : ZMod 792930101107) ^ 137490 := by rw [pow_add]
          _ = 779753407750 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 792930101107) ^ 549961 = 594623796905 := by
        calc
          (2 : ZMod 792930101107) ^ 549961 = (2 : ZMod 792930101107) ^ (274980 + 274980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 274980 * (2 : ZMod 792930101107) ^ 274980) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 594623796905 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 792930101107) ^ 1099923 = 224915204257 := by
        calc
          (2 : ZMod 792930101107) ^ 1099923 = (2 : ZMod 792930101107) ^ (549961 + 549961 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 549961 * (2 : ZMod 792930101107) ^ 549961) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 224915204257 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 792930101107) ^ 2199846 = 553799623479 := by
        calc
          (2 : ZMod 792930101107) ^ 2199846 = (2 : ZMod 792930101107) ^ (1099923 + 1099923) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1099923 * (2 : ZMod 792930101107) ^ 1099923 := by rw [pow_add]
          _ = 553799623479 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 792930101107) ^ 4399692 = 261866598110 := by
        calc
          (2 : ZMod 792930101107) ^ 4399692 = (2 : ZMod 792930101107) ^ (2199846 + 2199846) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 2199846 * (2 : ZMod 792930101107) ^ 2199846 := by rw [pow_add]
          _ = 261866598110 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 792930101107) ^ 8799384 = 694331633174 := by
        calc
          (2 : ZMod 792930101107) ^ 8799384 = (2 : ZMod 792930101107) ^ (4399692 + 4399692) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 4399692 * (2 : ZMod 792930101107) ^ 4399692 := by rw [pow_add]
          _ = 694331633174 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 792930101107) ^ 17598768 = 639913828529 := by
        calc
          (2 : ZMod 792930101107) ^ 17598768 = (2 : ZMod 792930101107) ^ (8799384 + 8799384) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 8799384 * (2 : ZMod 792930101107) ^ 8799384 := by rw [pow_add]
          _ = 639913828529 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 792930101107) ^ 35197536 = 533140088169 := by
        calc
          (2 : ZMod 792930101107) ^ 35197536 = (2 : ZMod 792930101107) ^ (17598768 + 17598768) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 17598768 * (2 : ZMod 792930101107) ^ 17598768 := by rw [pow_add]
          _ = 533140088169 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 792930101107) ^ 70395072 = 62754486641 := by
        calc
          (2 : ZMod 792930101107) ^ 70395072 = (2 : ZMod 792930101107) ^ (35197536 + 35197536) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 35197536 * (2 : ZMod 792930101107) ^ 35197536 := by rw [pow_add]
          _ = 62754486641 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 792930101107) ^ 140790145 = 474070335686 := by
        calc
          (2 : ZMod 792930101107) ^ 140790145 = (2 : ZMod 792930101107) ^ (70395072 + 70395072 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 70395072 * (2 : ZMod 792930101107) ^ 70395072) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 474070335686 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 792930101107) ^ 281580291 = 597298841532 := by
        calc
          (2 : ZMod 792930101107) ^ 281580291 = (2 : ZMod 792930101107) ^ (140790145 + 140790145 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 140790145 * (2 : ZMod 792930101107) ^ 140790145) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 597298841532 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 792930101107) ^ 563160583 = 598320865282 := by
        calc
          (2 : ZMod 792930101107) ^ 563160583 = (2 : ZMod 792930101107) ^ (281580291 + 281580291 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 281580291 * (2 : ZMod 792930101107) ^ 281580291) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 598320865282 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 792930101107) ^ 1126321166 = 186965315974 := by
        calc
          (2 : ZMod 792930101107) ^ 1126321166 = (2 : ZMod 792930101107) ^ (563160583 + 563160583) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 563160583 * (2 : ZMod 792930101107) ^ 563160583 := by rw [pow_add]
          _ = 186965315974 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 792930101107) ^ 2252642332 = 240199300363 := by
        calc
          (2 : ZMod 792930101107) ^ 2252642332 = (2 : ZMod 792930101107) ^ (1126321166 + 1126321166) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1126321166 * (2 : ZMod 792930101107) ^ 1126321166 := by rw [pow_add]
          _ = 240199300363 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 792930101107) ^ 4505284665 = 620755904734 := by
        calc
          (2 : ZMod 792930101107) ^ 4505284665 = (2 : ZMod 792930101107) ^ (2252642332 + 2252642332 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 2252642332 * (2 : ZMod 792930101107) ^ 2252642332) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 620755904734 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 792930101107) ^ 9010569330 = 233035087201 := by
        calc
          (2 : ZMod 792930101107) ^ 9010569330 = (2 : ZMod 792930101107) ^ (4505284665 + 4505284665) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 4505284665 * (2 : ZMod 792930101107) ^ 4505284665 := by rw [pow_add]
          _ = 233035087201 := by rw [factor_2_32]; decide
      have factor_2_34 : (2 : ZMod 792930101107) ^ 18021138661 = 216922932148 := by
        calc
          (2 : ZMod 792930101107) ^ 18021138661 = (2 : ZMod 792930101107) ^ (9010569330 + 9010569330 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 9010569330 * (2 : ZMod 792930101107) ^ 9010569330) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 216922932148 := by rw [factor_2_33]; decide
      have factor_2_35 : (2 : ZMod 792930101107) ^ 36042277323 = 590473919740 := by
        calc
          (2 : ZMod 792930101107) ^ 36042277323 = (2 : ZMod 792930101107) ^ (18021138661 + 18021138661 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 18021138661 * (2 : ZMod 792930101107) ^ 18021138661) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 590473919740 := by rw [factor_2_34]; decide
      have factor_2_36 : (2 : ZMod 792930101107) ^ 72084554646 = 172570285264 := by
        calc
          (2 : ZMod 792930101107) ^ 72084554646 = (2 : ZMod 792930101107) ^ (36042277323 + 36042277323) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 36042277323 * (2 : ZMod 792930101107) ^ 36042277323 := by rw [pow_add]
          _ = 172570285264 := by rw [factor_2_35]; decide
      change (2 : ZMod 792930101107) ^ 72084554646 ≠ 1
      rw [factor_2_36]
      decide
    ·
      have factor_3_0 : (2 : ZMod 792930101107) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 792930101107) ^ 3 = 8 := by
        calc
          (2 : ZMod 792930101107) ^ 3 = (2 : ZMod 792930101107) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1 * (2 : ZMod 792930101107) ^ 1) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 792930101107) ^ 7 = 128 := by
        calc
          (2 : ZMod 792930101107) ^ 7 = (2 : ZMod 792930101107) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 3 * (2 : ZMod 792930101107) ^ 3) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 792930101107) ^ 14 = 16384 := by
        calc
          (2 : ZMod 792930101107) ^ 14 = (2 : ZMod 792930101107) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 7 * (2 : ZMod 792930101107) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 792930101107) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 792930101107) ^ 28 = (2 : ZMod 792930101107) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 14 * (2 : ZMod 792930101107) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 792930101107) ^ 56 = 71099829311 := by
        calc
          (2 : ZMod 792930101107) ^ 56 = (2 : ZMod 792930101107) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 28 * (2 : ZMod 792930101107) ^ 28 := by rw [pow_add]
          _ = 71099829311 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 792930101107) ^ 113 = 414339041913 := by
        calc
          (2 : ZMod 792930101107) ^ 113 = (2 : ZMod 792930101107) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 56 * (2 : ZMod 792930101107) ^ 56) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 414339041913 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 792930101107) ^ 227 = 742998148070 := by
        calc
          (2 : ZMod 792930101107) ^ 227 = (2 : ZMod 792930101107) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 113 * (2 : ZMod 792930101107) ^ 113) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 742998148070 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 792930101107) ^ 454 = 779721940570 := by
        calc
          (2 : ZMod 792930101107) ^ 454 = (2 : ZMod 792930101107) ^ (227 + 227) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 227 * (2 : ZMod 792930101107) ^ 227 := by rw [pow_add]
          _ = 779721940570 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 792930101107) ^ 908 = 354916535901 := by
        calc
          (2 : ZMod 792930101107) ^ 908 = (2 : ZMod 792930101107) ^ (454 + 454) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 454 * (2 : ZMod 792930101107) ^ 454 := by rw [pow_add]
          _ = 354916535901 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 792930101107) ^ 1817 = 373238820411 := by
        calc
          (2 : ZMod 792930101107) ^ 1817 = (2 : ZMod 792930101107) ^ (908 + 908 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 908 * (2 : ZMod 792930101107) ^ 908) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 373238820411 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 792930101107) ^ 3635 = 635099633260 := by
        calc
          (2 : ZMod 792930101107) ^ 3635 = (2 : ZMod 792930101107) ^ (1817 + 1817 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1817 * (2 : ZMod 792930101107) ^ 1817) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 635099633260 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 792930101107) ^ 7271 = 169168920184 := by
        calc
          (2 : ZMod 792930101107) ^ 7271 = (2 : ZMod 792930101107) ^ (3635 + 3635 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 3635 * (2 : ZMod 792930101107) ^ 3635) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 169168920184 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 792930101107) ^ 14542 = 543942697282 := by
        calc
          (2 : ZMod 792930101107) ^ 14542 = (2 : ZMod 792930101107) ^ (7271 + 7271) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 7271 * (2 : ZMod 792930101107) ^ 7271 := by rw [pow_add]
          _ = 543942697282 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 792930101107) ^ 29084 = 414673293578 := by
        calc
          (2 : ZMod 792930101107) ^ 29084 = (2 : ZMod 792930101107) ^ (14542 + 14542) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 14542 * (2 : ZMod 792930101107) ^ 14542 := by rw [pow_add]
          _ = 414673293578 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 792930101107) ^ 58169 = 734987283176 := by
        calc
          (2 : ZMod 792930101107) ^ 58169 = (2 : ZMod 792930101107) ^ (29084 + 29084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 29084 * (2 : ZMod 792930101107) ^ 29084) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 734987283176 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 792930101107) ^ 116338 = 283793086052 := by
        calc
          (2 : ZMod 792930101107) ^ 116338 = (2 : ZMod 792930101107) ^ (58169 + 58169) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 58169 * (2 : ZMod 792930101107) ^ 58169 := by rw [pow_add]
          _ = 283793086052 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 792930101107) ^ 232676 = 226562065118 := by
        calc
          (2 : ZMod 792930101107) ^ 232676 = (2 : ZMod 792930101107) ^ (116338 + 116338) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 116338 * (2 : ZMod 792930101107) ^ 116338 := by rw [pow_add]
          _ = 226562065118 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 792930101107) ^ 465352 = 573641950782 := by
        calc
          (2 : ZMod 792930101107) ^ 465352 = (2 : ZMod 792930101107) ^ (232676 + 232676) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 232676 * (2 : ZMod 792930101107) ^ 232676 := by rw [pow_add]
          _ = 573641950782 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 792930101107) ^ 930704 = 611323542073 := by
        calc
          (2 : ZMod 792930101107) ^ 930704 = (2 : ZMod 792930101107) ^ (465352 + 465352) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 465352 * (2 : ZMod 792930101107) ^ 465352 := by rw [pow_add]
          _ = 611323542073 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 792930101107) ^ 1861408 = 572724639253 := by
        calc
          (2 : ZMod 792930101107) ^ 1861408 = (2 : ZMod 792930101107) ^ (930704 + 930704) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 930704 * (2 : ZMod 792930101107) ^ 930704 := by rw [pow_add]
          _ = 572724639253 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 792930101107) ^ 3722816 = 771937007645 := by
        calc
          (2 : ZMod 792930101107) ^ 3722816 = (2 : ZMod 792930101107) ^ (1861408 + 1861408) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 1861408 * (2 : ZMod 792930101107) ^ 1861408 := by rw [pow_add]
          _ = 771937007645 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 792930101107) ^ 7445632 = 162110151340 := by
        calc
          (2 : ZMod 792930101107) ^ 7445632 = (2 : ZMod 792930101107) ^ (3722816 + 3722816) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 3722816 * (2 : ZMod 792930101107) ^ 3722816 := by rw [pow_add]
          _ = 162110151340 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 792930101107) ^ 14891265 = 556842995317 := by
        calc
          (2 : ZMod 792930101107) ^ 14891265 = (2 : ZMod 792930101107) ^ (7445632 + 7445632 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 7445632 * (2 : ZMod 792930101107) ^ 7445632) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 556842995317 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 792930101107) ^ 29782530 = 418558703479 := by
        calc
          (2 : ZMod 792930101107) ^ 29782530 = (2 : ZMod 792930101107) ^ (14891265 + 14891265) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 14891265 * (2 : ZMod 792930101107) ^ 14891265 := by rw [pow_add]
          _ = 418558703479 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 792930101107) ^ 59565061 = 337335038920 := by
        calc
          (2 : ZMod 792930101107) ^ 59565061 = (2 : ZMod 792930101107) ^ (29782530 + 29782530 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 29782530 * (2 : ZMod 792930101107) ^ 29782530) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 337335038920 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 792930101107) ^ 119130123 = 234190416840 := by
        calc
          (2 : ZMod 792930101107) ^ 119130123 = (2 : ZMod 792930101107) ^ (59565061 + 59565061 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 59565061 * (2 : ZMod 792930101107) ^ 59565061) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 234190416840 := by rw [factor_3_25]; decide
      have factor_3_27 : (2 : ZMod 792930101107) ^ 238260246 = 419983606633 := by
        calc
          (2 : ZMod 792930101107) ^ 238260246 = (2 : ZMod 792930101107) ^ (119130123 + 119130123) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 119130123 * (2 : ZMod 792930101107) ^ 119130123 := by rw [pow_add]
          _ = 419983606633 := by rw [factor_3_26]; decide
      have factor_3_28 : (2 : ZMod 792930101107) ^ 476520493 = 493049435056 := by
        calc
          (2 : ZMod 792930101107) ^ 476520493 = (2 : ZMod 792930101107) ^ (238260246 + 238260246 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 238260246 * (2 : ZMod 792930101107) ^ 238260246) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 493049435056 := by rw [factor_3_27]; decide
      have factor_3_29 : (2 : ZMod 792930101107) ^ 953040986 = 29254638533 := by
        calc
          (2 : ZMod 792930101107) ^ 953040986 = (2 : ZMod 792930101107) ^ (476520493 + 476520493) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 476520493 * (2 : ZMod 792930101107) ^ 476520493 := by rw [pow_add]
          _ = 29254638533 := by rw [factor_3_28]; decide
      have factor_3_30 : (2 : ZMod 792930101107) ^ 1906081973 = 164339606262 := by
        calc
          (2 : ZMod 792930101107) ^ 1906081973 = (2 : ZMod 792930101107) ^ (953040986 + 953040986 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 953040986 * (2 : ZMod 792930101107) ^ 953040986) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 164339606262 := by rw [factor_3_29]; decide
      have factor_3_31 : (2 : ZMod 792930101107) ^ 3812163947 = 391122388102 := by
        calc
          (2 : ZMod 792930101107) ^ 3812163947 = (2 : ZMod 792930101107) ^ (1906081973 + 1906081973 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1906081973 * (2 : ZMod 792930101107) ^ 1906081973) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 391122388102 := by rw [factor_3_30]; decide
      have factor_3_32 : (2 : ZMod 792930101107) ^ 7624327895 = 351944655310 := by
        calc
          (2 : ZMod 792930101107) ^ 7624327895 = (2 : ZMod 792930101107) ^ (3812163947 + 3812163947 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 3812163947 * (2 : ZMod 792930101107) ^ 3812163947) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 351944655310 := by rw [factor_3_31]; decide
      have factor_3_33 : (2 : ZMod 792930101107) ^ 15248655790 = 95469357752 := by
        calc
          (2 : ZMod 792930101107) ^ 15248655790 = (2 : ZMod 792930101107) ^ (7624327895 + 7624327895) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 7624327895 * (2 : ZMod 792930101107) ^ 7624327895 := by rw [pow_add]
          _ = 95469357752 := by rw [factor_3_32]; decide
      have factor_3_34 : (2 : ZMod 792930101107) ^ 30497311581 = 211328959253 := by
        calc
          (2 : ZMod 792930101107) ^ 30497311581 = (2 : ZMod 792930101107) ^ (15248655790 + 15248655790 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 15248655790 * (2 : ZMod 792930101107) ^ 15248655790) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 211328959253 := by rw [factor_3_33]; decide
      have factor_3_35 : (2 : ZMod 792930101107) ^ 60994623162 = 403072142241 := by
        calc
          (2 : ZMod 792930101107) ^ 60994623162 = (2 : ZMod 792930101107) ^ (30497311581 + 30497311581) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 30497311581 * (2 : ZMod 792930101107) ^ 30497311581 := by rw [pow_add]
          _ = 403072142241 := by rw [factor_3_34]; decide
      change (2 : ZMod 792930101107) ^ 60994623162 ≠ 1
      rw [factor_3_35]
      decide
    ·
      have factor_4_0 : (2 : ZMod 792930101107) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 792930101107) ^ 3 = 8 := by
        calc
          (2 : ZMod 792930101107) ^ 3 = (2 : ZMod 792930101107) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 1 * (2 : ZMod 792930101107) ^ 1) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 792930101107) ^ 6 = 64 := by
        calc
          (2 : ZMod 792930101107) ^ 6 = (2 : ZMod 792930101107) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 3 * (2 : ZMod 792930101107) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 792930101107) ^ 13 = 8192 := by
        calc
          (2 : ZMod 792930101107) ^ 13 = (2 : ZMod 792930101107) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 6 * (2 : ZMod 792930101107) ^ 6) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 792930101107) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 792930101107) ^ 26 = (2 : ZMod 792930101107) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 13 * (2 : ZMod 792930101107) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 792930101107) ^ 53 = 306236266579 := by
        calc
          (2 : ZMod 792930101107) ^ 53 = (2 : ZMod 792930101107) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 26 * (2 : ZMod 792930101107) ^ 26) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 306236266579 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 792930101107) ^ 107 = 365770499594 := by
        calc
          (2 : ZMod 792930101107) ^ 107 = (2 : ZMod 792930101107) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 53 * (2 : ZMod 792930101107) ^ 53) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 365770499594 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 792930101107) ^ 214 = 222908702502 := by
        calc
          (2 : ZMod 792930101107) ^ 214 = (2 : ZMod 792930101107) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 107 * (2 : ZMod 792930101107) ^ 107 := by rw [pow_add]
          _ = 222908702502 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 792930101107) ^ 429 = 78125814810 := by
        calc
          (2 : ZMod 792930101107) ^ 429 = (2 : ZMod 792930101107) ^ (214 + 214 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = ((2 : ZMod 792930101107) ^ 214 * (2 : ZMod 792930101107) ^ 214) * (2 : ZMod 792930101107) := by rw [pow_succ, pow_add]
          _ = 78125814810 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 792930101107) ^ 858 = 506737704145 := by
        calc
          (2 : ZMod 792930101107) ^ 858 = (2 : ZMod 792930101107) ^ (429 + 429) :=
            congrArg (fun n : ℕ => (2 : ZMod 792930101107) ^ n) (by norm_num)
          _ = (2 : ZMod 792930101107) ^ 429 * (2 : ZMod 792930101107) ^ 429 := by rw [pow_add]
          _ = 506737704145 := by rw [factor_4_8]; decide
      change (2 : ZMod 792930101107) ^ 858 ≠ 1
      rw [factor_4_9]
      decide

#print axioms prime_lucas_792930101107

end TotientTailPeriodKiller
end Erdos249257
