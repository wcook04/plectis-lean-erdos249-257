import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_388181593801 : Nat.Prime 388181593801 := by
  apply lucas_primality 388181593801 (47 : ZMod 388181593801)
  ·
      have fermat_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have fermat_1 : (47 : ZMod 388181593801) ^ 2 = 2209 := by
        calc
          (47 : ZMod 388181593801) ^ 2 = (47 : ZMod 388181593801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [fermat_0]; decide
      have fermat_2 : (47 : ZMod 388181593801) ^ 5 = 229345007 := by
        calc
          (47 : ZMod 388181593801) ^ 5 = (47 : ZMod 388181593801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2 * (47 : ZMod 388181593801) ^ 2) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 229345007 := by rw [fermat_1]; decide
      have fermat_3 : (47 : ZMod 388181593801) ^ 11 = 279521934340 := by
        calc
          (47 : ZMod 388181593801) ^ 11 = (47 : ZMod 388181593801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 5 * (47 : ZMod 388181593801) ^ 5) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 279521934340 := by rw [fermat_2]; decide
      have fermat_4 : (47 : ZMod 388181593801) ^ 22 = 284536499472 := by
        calc
          (47 : ZMod 388181593801) ^ 22 = (47 : ZMod 388181593801) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 11 * (47 : ZMod 388181593801) ^ 11 := by rw [pow_add]
          _ = 284536499472 := by rw [fermat_3]; decide
      have fermat_5 : (47 : ZMod 388181593801) ^ 45 = 224942751116 := by
        calc
          (47 : ZMod 388181593801) ^ 45 = (47 : ZMod 388181593801) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 22 * (47 : ZMod 388181593801) ^ 22) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 224942751116 := by rw [fermat_4]; decide
      have fermat_6 : (47 : ZMod 388181593801) ^ 90 = 58999925203 := by
        calc
          (47 : ZMod 388181593801) ^ 90 = (47 : ZMod 388181593801) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 45 * (47 : ZMod 388181593801) ^ 45 := by rw [pow_add]
          _ = 58999925203 := by rw [fermat_5]; decide
      have fermat_7 : (47 : ZMod 388181593801) ^ 180 = 141546830056 := by
        calc
          (47 : ZMod 388181593801) ^ 180 = (47 : ZMod 388181593801) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 90 * (47 : ZMod 388181593801) ^ 90 := by rw [pow_add]
          _ = 141546830056 := by rw [fermat_6]; decide
      have fermat_8 : (47 : ZMod 388181593801) ^ 361 = 186408932812 := by
        calc
          (47 : ZMod 388181593801) ^ 361 = (47 : ZMod 388181593801) ^ (180 + 180 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 180 * (47 : ZMod 388181593801) ^ 180) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 186408932812 := by rw [fermat_7]; decide
      have fermat_9 : (47 : ZMod 388181593801) ^ 723 = 331392542924 := by
        calc
          (47 : ZMod 388181593801) ^ 723 = (47 : ZMod 388181593801) ^ (361 + 361 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 361 * (47 : ZMod 388181593801) ^ 361) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 331392542924 := by rw [fermat_8]; decide
      have fermat_10 : (47 : ZMod 388181593801) ^ 1446 = 251408058931 := by
        calc
          (47 : ZMod 388181593801) ^ 1446 = (47 : ZMod 388181593801) ^ (723 + 723) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 723 * (47 : ZMod 388181593801) ^ 723 := by rw [pow_add]
          _ = 251408058931 := by rw [fermat_9]; decide
      have fermat_11 : (47 : ZMod 388181593801) ^ 2892 = 252417062560 := by
        calc
          (47 : ZMod 388181593801) ^ 2892 = (47 : ZMod 388181593801) ^ (1446 + 1446) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1446 * (47 : ZMod 388181593801) ^ 1446 := by rw [pow_add]
          _ = 252417062560 := by rw [fermat_10]; decide
      have fermat_12 : (47 : ZMod 388181593801) ^ 5784 = 52059766191 := by
        calc
          (47 : ZMod 388181593801) ^ 5784 = (47 : ZMod 388181593801) ^ (2892 + 2892) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2892 * (47 : ZMod 388181593801) ^ 2892 := by rw [pow_add]
          _ = 52059766191 := by rw [fermat_11]; decide
      have fermat_13 : (47 : ZMod 388181593801) ^ 11568 = 178372514981 := by
        calc
          (47 : ZMod 388181593801) ^ 11568 = (47 : ZMod 388181593801) ^ (5784 + 5784) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 5784 * (47 : ZMod 388181593801) ^ 5784 := by rw [pow_add]
          _ = 178372514981 := by rw [fermat_12]; decide
      have fermat_14 : (47 : ZMod 388181593801) ^ 23137 = 378790868196 := by
        calc
          (47 : ZMod 388181593801) ^ 23137 = (47 : ZMod 388181593801) ^ (11568 + 11568 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 11568 * (47 : ZMod 388181593801) ^ 11568) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 378790868196 := by rw [fermat_13]; decide
      have fermat_15 : (47 : ZMod 388181593801) ^ 46274 = 84264803147 := by
        calc
          (47 : ZMod 388181593801) ^ 46274 = (47 : ZMod 388181593801) ^ (23137 + 23137) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 23137 * (47 : ZMod 388181593801) ^ 23137 := by rw [pow_add]
          _ = 84264803147 := by rw [fermat_14]; decide
      have fermat_16 : (47 : ZMod 388181593801) ^ 92549 = 144233281509 := by
        calc
          (47 : ZMod 388181593801) ^ 92549 = (47 : ZMod 388181593801) ^ (46274 + 46274 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 46274 * (47 : ZMod 388181593801) ^ 46274) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 144233281509 := by rw [fermat_15]; decide
      have fermat_17 : (47 : ZMod 388181593801) ^ 185099 = 330014132283 := by
        calc
          (47 : ZMod 388181593801) ^ 185099 = (47 : ZMod 388181593801) ^ (92549 + 92549 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 92549 * (47 : ZMod 388181593801) ^ 92549) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 330014132283 := by rw [fermat_16]; decide
      have fermat_18 : (47 : ZMod 388181593801) ^ 370198 = 96617862524 := by
        calc
          (47 : ZMod 388181593801) ^ 370198 = (47 : ZMod 388181593801) ^ (185099 + 185099) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 185099 * (47 : ZMod 388181593801) ^ 185099 := by rw [pow_add]
          _ = 96617862524 := by rw [fermat_17]; decide
      have fermat_19 : (47 : ZMod 388181593801) ^ 740397 = 351224195187 := by
        calc
          (47 : ZMod 388181593801) ^ 740397 = (47 : ZMod 388181593801) ^ (370198 + 370198 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 370198 * (47 : ZMod 388181593801) ^ 370198) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 351224195187 := by rw [fermat_18]; decide
      have fermat_20 : (47 : ZMod 388181593801) ^ 1480795 = 324524557191 := by
        calc
          (47 : ZMod 388181593801) ^ 1480795 = (47 : ZMod 388181593801) ^ (740397 + 740397 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 740397 * (47 : ZMod 388181593801) ^ 740397) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 324524557191 := by rw [fermat_19]; decide
      have fermat_21 : (47 : ZMod 388181593801) ^ 2961590 = 79201613981 := by
        calc
          (47 : ZMod 388181593801) ^ 2961590 = (47 : ZMod 388181593801) ^ (1480795 + 1480795) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1480795 * (47 : ZMod 388181593801) ^ 1480795 := by rw [pow_add]
          _ = 79201613981 := by rw [fermat_20]; decide
      have fermat_22 : (47 : ZMod 388181593801) ^ 5923181 = 273220230499 := by
        calc
          (47 : ZMod 388181593801) ^ 5923181 = (47 : ZMod 388181593801) ^ (2961590 + 2961590 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2961590 * (47 : ZMod 388181593801) ^ 2961590) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 273220230499 := by rw [fermat_21]; decide
      have fermat_23 : (47 : ZMod 388181593801) ^ 11846362 = 243526302698 := by
        calc
          (47 : ZMod 388181593801) ^ 11846362 = (47 : ZMod 388181593801) ^ (5923181 + 5923181) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 5923181 * (47 : ZMod 388181593801) ^ 5923181 := by rw [pow_add]
          _ = 243526302698 := by rw [fermat_22]; decide
      have fermat_24 : (47 : ZMod 388181593801) ^ 23692724 = 345038751852 := by
        calc
          (47 : ZMod 388181593801) ^ 23692724 = (47 : ZMod 388181593801) ^ (11846362 + 11846362) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 11846362 * (47 : ZMod 388181593801) ^ 11846362 := by rw [pow_add]
          _ = 345038751852 := by rw [fermat_23]; decide
      have fermat_25 : (47 : ZMod 388181593801) ^ 47385448 = 79246619202 := by
        calc
          (47 : ZMod 388181593801) ^ 47385448 = (47 : ZMod 388181593801) ^ (23692724 + 23692724) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 23692724 * (47 : ZMod 388181593801) ^ 23692724 := by rw [pow_add]
          _ = 79246619202 := by rw [fermat_24]; decide
      have fermat_26 : (47 : ZMod 388181593801) ^ 94770896 = 10388042038 := by
        calc
          (47 : ZMod 388181593801) ^ 94770896 = (47 : ZMod 388181593801) ^ (47385448 + 47385448) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 47385448 * (47 : ZMod 388181593801) ^ 47385448 := by rw [pow_add]
          _ = 10388042038 := by rw [fermat_25]; decide
      have fermat_27 : (47 : ZMod 388181593801) ^ 189541793 = 370386303655 := by
        calc
          (47 : ZMod 388181593801) ^ 189541793 = (47 : ZMod 388181593801) ^ (94770896 + 94770896 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 94770896 * (47 : ZMod 388181593801) ^ 94770896) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 370386303655 := by rw [fermat_26]; decide
      have fermat_28 : (47 : ZMod 388181593801) ^ 379083587 = 6431071065 := by
        calc
          (47 : ZMod 388181593801) ^ 379083587 = (47 : ZMod 388181593801) ^ (189541793 + 189541793 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 189541793 * (47 : ZMod 388181593801) ^ 189541793) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 6431071065 := by rw [fermat_27]; decide
      have fermat_29 : (47 : ZMod 388181593801) ^ 758167175 = 248457464063 := by
        calc
          (47 : ZMod 388181593801) ^ 758167175 = (47 : ZMod 388181593801) ^ (379083587 + 379083587 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 379083587 * (47 : ZMod 388181593801) ^ 379083587) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 248457464063 := by rw [fermat_28]; decide
      have fermat_30 : (47 : ZMod 388181593801) ^ 1516334350 = 144923814027 := by
        calc
          (47 : ZMod 388181593801) ^ 1516334350 = (47 : ZMod 388181593801) ^ (758167175 + 758167175) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 758167175 * (47 : ZMod 388181593801) ^ 758167175 := by rw [pow_add]
          _ = 144923814027 := by rw [fermat_29]; decide
      have fermat_31 : (47 : ZMod 388181593801) ^ 3032668701 = 202558868759 := by
        calc
          (47 : ZMod 388181593801) ^ 3032668701 = (47 : ZMod 388181593801) ^ (1516334350 + 1516334350 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1516334350 * (47 : ZMod 388181593801) ^ 1516334350) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 202558868759 := by rw [fermat_30]; decide
      have fermat_32 : (47 : ZMod 388181593801) ^ 6065337403 = 243525034262 := by
        calc
          (47 : ZMod 388181593801) ^ 6065337403 = (47 : ZMod 388181593801) ^ (3032668701 + 3032668701 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 3032668701 * (47 : ZMod 388181593801) ^ 3032668701) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 243525034262 := by rw [fermat_31]; decide
      have fermat_33 : (47 : ZMod 388181593801) ^ 12130674806 = 231014411598 := by
        calc
          (47 : ZMod 388181593801) ^ 12130674806 = (47 : ZMod 388181593801) ^ (6065337403 + 6065337403) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 6065337403 * (47 : ZMod 388181593801) ^ 6065337403 := by rw [pow_add]
          _ = 231014411598 := by rw [fermat_32]; decide
      have fermat_34 : (47 : ZMod 388181593801) ^ 24261349612 = 278619823611 := by
        calc
          (47 : ZMod 388181593801) ^ 24261349612 = (47 : ZMod 388181593801) ^ (12130674806 + 12130674806) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 12130674806 * (47 : ZMod 388181593801) ^ 12130674806 := by rw [pow_add]
          _ = 278619823611 := by rw [fermat_33]; decide
      have fermat_35 : (47 : ZMod 388181593801) ^ 48522699225 = 258323728338 := by
        calc
          (47 : ZMod 388181593801) ^ 48522699225 = (47 : ZMod 388181593801) ^ (24261349612 + 24261349612 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 24261349612 * (47 : ZMod 388181593801) ^ 24261349612) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 258323728338 := by rw [fermat_34]; decide
      have fermat_36 : (47 : ZMod 388181593801) ^ 97045398450 = 247023597032 := by
        calc
          (47 : ZMod 388181593801) ^ 97045398450 = (47 : ZMod 388181593801) ^ (48522699225 + 48522699225) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 48522699225 * (47 : ZMod 388181593801) ^ 48522699225 := by rw [pow_add]
          _ = 247023597032 := by rw [fermat_35]; decide
      have fermat_37 : (47 : ZMod 388181593801) ^ 194090796900 = 388181593800 := by
        calc
          (47 : ZMod 388181593801) ^ 194090796900 = (47 : ZMod 388181593801) ^ (97045398450 + 97045398450) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 97045398450 * (47 : ZMod 388181593801) ^ 97045398450 := by rw [pow_add]
          _ = 388181593800 := by rw [fermat_36]; decide
      have fermat_38 : (47 : ZMod 388181593801) ^ 388181593800 = 1 := by
        calc
          (47 : ZMod 388181593801) ^ 388181593800 = (47 : ZMod 388181593801) ^ (194090796900 + 194090796900) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 194090796900 * (47 : ZMod 388181593801) ^ 194090796900 := by rw [pow_add]
          _ = 1 := by rw [fermat_37]; decide
      simpa using fermat_38
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 388181593801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_0_1 : (47 : ZMod 388181593801) ^ 2 = 2209 := by
        calc
          (47 : ZMod 388181593801) ^ 2 = (47 : ZMod 388181593801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_0_0]; decide
      have factor_0_2 : (47 : ZMod 388181593801) ^ 5 = 229345007 := by
        calc
          (47 : ZMod 388181593801) ^ 5 = (47 : ZMod 388181593801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2 * (47 : ZMod 388181593801) ^ 2) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 229345007 := by rw [factor_0_1]; decide
      have factor_0_3 : (47 : ZMod 388181593801) ^ 11 = 279521934340 := by
        calc
          (47 : ZMod 388181593801) ^ 11 = (47 : ZMod 388181593801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 5 * (47 : ZMod 388181593801) ^ 5) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 279521934340 := by rw [factor_0_2]; decide
      have factor_0_4 : (47 : ZMod 388181593801) ^ 22 = 284536499472 := by
        calc
          (47 : ZMod 388181593801) ^ 22 = (47 : ZMod 388181593801) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 11 * (47 : ZMod 388181593801) ^ 11 := by rw [pow_add]
          _ = 284536499472 := by rw [factor_0_3]; decide
      have factor_0_5 : (47 : ZMod 388181593801) ^ 45 = 224942751116 := by
        calc
          (47 : ZMod 388181593801) ^ 45 = (47 : ZMod 388181593801) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 22 * (47 : ZMod 388181593801) ^ 22) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 224942751116 := by rw [factor_0_4]; decide
      have factor_0_6 : (47 : ZMod 388181593801) ^ 90 = 58999925203 := by
        calc
          (47 : ZMod 388181593801) ^ 90 = (47 : ZMod 388181593801) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 45 * (47 : ZMod 388181593801) ^ 45 := by rw [pow_add]
          _ = 58999925203 := by rw [factor_0_5]; decide
      have factor_0_7 : (47 : ZMod 388181593801) ^ 180 = 141546830056 := by
        calc
          (47 : ZMod 388181593801) ^ 180 = (47 : ZMod 388181593801) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 90 * (47 : ZMod 388181593801) ^ 90 := by rw [pow_add]
          _ = 141546830056 := by rw [factor_0_6]; decide
      have factor_0_8 : (47 : ZMod 388181593801) ^ 361 = 186408932812 := by
        calc
          (47 : ZMod 388181593801) ^ 361 = (47 : ZMod 388181593801) ^ (180 + 180 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 180 * (47 : ZMod 388181593801) ^ 180) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 186408932812 := by rw [factor_0_7]; decide
      have factor_0_9 : (47 : ZMod 388181593801) ^ 723 = 331392542924 := by
        calc
          (47 : ZMod 388181593801) ^ 723 = (47 : ZMod 388181593801) ^ (361 + 361 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 361 * (47 : ZMod 388181593801) ^ 361) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 331392542924 := by rw [factor_0_8]; decide
      have factor_0_10 : (47 : ZMod 388181593801) ^ 1446 = 251408058931 := by
        calc
          (47 : ZMod 388181593801) ^ 1446 = (47 : ZMod 388181593801) ^ (723 + 723) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 723 * (47 : ZMod 388181593801) ^ 723 := by rw [pow_add]
          _ = 251408058931 := by rw [factor_0_9]; decide
      have factor_0_11 : (47 : ZMod 388181593801) ^ 2892 = 252417062560 := by
        calc
          (47 : ZMod 388181593801) ^ 2892 = (47 : ZMod 388181593801) ^ (1446 + 1446) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1446 * (47 : ZMod 388181593801) ^ 1446 := by rw [pow_add]
          _ = 252417062560 := by rw [factor_0_10]; decide
      have factor_0_12 : (47 : ZMod 388181593801) ^ 5784 = 52059766191 := by
        calc
          (47 : ZMod 388181593801) ^ 5784 = (47 : ZMod 388181593801) ^ (2892 + 2892) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2892 * (47 : ZMod 388181593801) ^ 2892 := by rw [pow_add]
          _ = 52059766191 := by rw [factor_0_11]; decide
      have factor_0_13 : (47 : ZMod 388181593801) ^ 11568 = 178372514981 := by
        calc
          (47 : ZMod 388181593801) ^ 11568 = (47 : ZMod 388181593801) ^ (5784 + 5784) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 5784 * (47 : ZMod 388181593801) ^ 5784 := by rw [pow_add]
          _ = 178372514981 := by rw [factor_0_12]; decide
      have factor_0_14 : (47 : ZMod 388181593801) ^ 23137 = 378790868196 := by
        calc
          (47 : ZMod 388181593801) ^ 23137 = (47 : ZMod 388181593801) ^ (11568 + 11568 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 11568 * (47 : ZMod 388181593801) ^ 11568) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 378790868196 := by rw [factor_0_13]; decide
      have factor_0_15 : (47 : ZMod 388181593801) ^ 46274 = 84264803147 := by
        calc
          (47 : ZMod 388181593801) ^ 46274 = (47 : ZMod 388181593801) ^ (23137 + 23137) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 23137 * (47 : ZMod 388181593801) ^ 23137 := by rw [pow_add]
          _ = 84264803147 := by rw [factor_0_14]; decide
      have factor_0_16 : (47 : ZMod 388181593801) ^ 92549 = 144233281509 := by
        calc
          (47 : ZMod 388181593801) ^ 92549 = (47 : ZMod 388181593801) ^ (46274 + 46274 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 46274 * (47 : ZMod 388181593801) ^ 46274) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 144233281509 := by rw [factor_0_15]; decide
      have factor_0_17 : (47 : ZMod 388181593801) ^ 185099 = 330014132283 := by
        calc
          (47 : ZMod 388181593801) ^ 185099 = (47 : ZMod 388181593801) ^ (92549 + 92549 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 92549 * (47 : ZMod 388181593801) ^ 92549) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 330014132283 := by rw [factor_0_16]; decide
      have factor_0_18 : (47 : ZMod 388181593801) ^ 370198 = 96617862524 := by
        calc
          (47 : ZMod 388181593801) ^ 370198 = (47 : ZMod 388181593801) ^ (185099 + 185099) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 185099 * (47 : ZMod 388181593801) ^ 185099 := by rw [pow_add]
          _ = 96617862524 := by rw [factor_0_17]; decide
      have factor_0_19 : (47 : ZMod 388181593801) ^ 740397 = 351224195187 := by
        calc
          (47 : ZMod 388181593801) ^ 740397 = (47 : ZMod 388181593801) ^ (370198 + 370198 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 370198 * (47 : ZMod 388181593801) ^ 370198) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 351224195187 := by rw [factor_0_18]; decide
      have factor_0_20 : (47 : ZMod 388181593801) ^ 1480795 = 324524557191 := by
        calc
          (47 : ZMod 388181593801) ^ 1480795 = (47 : ZMod 388181593801) ^ (740397 + 740397 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 740397 * (47 : ZMod 388181593801) ^ 740397) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 324524557191 := by rw [factor_0_19]; decide
      have factor_0_21 : (47 : ZMod 388181593801) ^ 2961590 = 79201613981 := by
        calc
          (47 : ZMod 388181593801) ^ 2961590 = (47 : ZMod 388181593801) ^ (1480795 + 1480795) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1480795 * (47 : ZMod 388181593801) ^ 1480795 := by rw [pow_add]
          _ = 79201613981 := by rw [factor_0_20]; decide
      have factor_0_22 : (47 : ZMod 388181593801) ^ 5923181 = 273220230499 := by
        calc
          (47 : ZMod 388181593801) ^ 5923181 = (47 : ZMod 388181593801) ^ (2961590 + 2961590 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2961590 * (47 : ZMod 388181593801) ^ 2961590) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 273220230499 := by rw [factor_0_21]; decide
      have factor_0_23 : (47 : ZMod 388181593801) ^ 11846362 = 243526302698 := by
        calc
          (47 : ZMod 388181593801) ^ 11846362 = (47 : ZMod 388181593801) ^ (5923181 + 5923181) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 5923181 * (47 : ZMod 388181593801) ^ 5923181 := by rw [pow_add]
          _ = 243526302698 := by rw [factor_0_22]; decide
      have factor_0_24 : (47 : ZMod 388181593801) ^ 23692724 = 345038751852 := by
        calc
          (47 : ZMod 388181593801) ^ 23692724 = (47 : ZMod 388181593801) ^ (11846362 + 11846362) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 11846362 * (47 : ZMod 388181593801) ^ 11846362 := by rw [pow_add]
          _ = 345038751852 := by rw [factor_0_23]; decide
      have factor_0_25 : (47 : ZMod 388181593801) ^ 47385448 = 79246619202 := by
        calc
          (47 : ZMod 388181593801) ^ 47385448 = (47 : ZMod 388181593801) ^ (23692724 + 23692724) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 23692724 * (47 : ZMod 388181593801) ^ 23692724 := by rw [pow_add]
          _ = 79246619202 := by rw [factor_0_24]; decide
      have factor_0_26 : (47 : ZMod 388181593801) ^ 94770896 = 10388042038 := by
        calc
          (47 : ZMod 388181593801) ^ 94770896 = (47 : ZMod 388181593801) ^ (47385448 + 47385448) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 47385448 * (47 : ZMod 388181593801) ^ 47385448 := by rw [pow_add]
          _ = 10388042038 := by rw [factor_0_25]; decide
      have factor_0_27 : (47 : ZMod 388181593801) ^ 189541793 = 370386303655 := by
        calc
          (47 : ZMod 388181593801) ^ 189541793 = (47 : ZMod 388181593801) ^ (94770896 + 94770896 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 94770896 * (47 : ZMod 388181593801) ^ 94770896) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 370386303655 := by rw [factor_0_26]; decide
      have factor_0_28 : (47 : ZMod 388181593801) ^ 379083587 = 6431071065 := by
        calc
          (47 : ZMod 388181593801) ^ 379083587 = (47 : ZMod 388181593801) ^ (189541793 + 189541793 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 189541793 * (47 : ZMod 388181593801) ^ 189541793) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 6431071065 := by rw [factor_0_27]; decide
      have factor_0_29 : (47 : ZMod 388181593801) ^ 758167175 = 248457464063 := by
        calc
          (47 : ZMod 388181593801) ^ 758167175 = (47 : ZMod 388181593801) ^ (379083587 + 379083587 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 379083587 * (47 : ZMod 388181593801) ^ 379083587) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 248457464063 := by rw [factor_0_28]; decide
      have factor_0_30 : (47 : ZMod 388181593801) ^ 1516334350 = 144923814027 := by
        calc
          (47 : ZMod 388181593801) ^ 1516334350 = (47 : ZMod 388181593801) ^ (758167175 + 758167175) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 758167175 * (47 : ZMod 388181593801) ^ 758167175 := by rw [pow_add]
          _ = 144923814027 := by rw [factor_0_29]; decide
      have factor_0_31 : (47 : ZMod 388181593801) ^ 3032668701 = 202558868759 := by
        calc
          (47 : ZMod 388181593801) ^ 3032668701 = (47 : ZMod 388181593801) ^ (1516334350 + 1516334350 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1516334350 * (47 : ZMod 388181593801) ^ 1516334350) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 202558868759 := by rw [factor_0_30]; decide
      have factor_0_32 : (47 : ZMod 388181593801) ^ 6065337403 = 243525034262 := by
        calc
          (47 : ZMod 388181593801) ^ 6065337403 = (47 : ZMod 388181593801) ^ (3032668701 + 3032668701 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 3032668701 * (47 : ZMod 388181593801) ^ 3032668701) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 243525034262 := by rw [factor_0_31]; decide
      have factor_0_33 : (47 : ZMod 388181593801) ^ 12130674806 = 231014411598 := by
        calc
          (47 : ZMod 388181593801) ^ 12130674806 = (47 : ZMod 388181593801) ^ (6065337403 + 6065337403) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 6065337403 * (47 : ZMod 388181593801) ^ 6065337403 := by rw [pow_add]
          _ = 231014411598 := by rw [factor_0_32]; decide
      have factor_0_34 : (47 : ZMod 388181593801) ^ 24261349612 = 278619823611 := by
        calc
          (47 : ZMod 388181593801) ^ 24261349612 = (47 : ZMod 388181593801) ^ (12130674806 + 12130674806) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 12130674806 * (47 : ZMod 388181593801) ^ 12130674806 := by rw [pow_add]
          _ = 278619823611 := by rw [factor_0_33]; decide
      have factor_0_35 : (47 : ZMod 388181593801) ^ 48522699225 = 258323728338 := by
        calc
          (47 : ZMod 388181593801) ^ 48522699225 = (47 : ZMod 388181593801) ^ (24261349612 + 24261349612 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 24261349612 * (47 : ZMod 388181593801) ^ 24261349612) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 258323728338 := by rw [factor_0_34]; decide
      have factor_0_36 : (47 : ZMod 388181593801) ^ 97045398450 = 247023597032 := by
        calc
          (47 : ZMod 388181593801) ^ 97045398450 = (47 : ZMod 388181593801) ^ (48522699225 + 48522699225) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 48522699225 * (47 : ZMod 388181593801) ^ 48522699225 := by rw [pow_add]
          _ = 247023597032 := by rw [factor_0_35]; decide
      have factor_0_37 : (47 : ZMod 388181593801) ^ 194090796900 = 388181593800 := by
        calc
          (47 : ZMod 388181593801) ^ 194090796900 = (47 : ZMod 388181593801) ^ (97045398450 + 97045398450) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 97045398450 * (47 : ZMod 388181593801) ^ 97045398450 := by rw [pow_add]
          _ = 388181593800 := by rw [factor_0_36]; decide
      change (47 : ZMod 388181593801) ^ 194090796900 ≠ 1
      rw [factor_0_37]
      decide
    ·
      have factor_1_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_1_1 : (47 : ZMod 388181593801) ^ 3 = 103823 := by
        calc
          (47 : ZMod 388181593801) ^ 3 = (47 : ZMod 388181593801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_1_0]; decide
      have factor_1_2 : (47 : ZMod 388181593801) ^ 7 = 118441526662 := by
        calc
          (47 : ZMod 388181593801) ^ 7 = (47 : ZMod 388181593801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 3 * (47 : ZMod 388181593801) ^ 3) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 118441526662 := by rw [factor_1_1]; decide
      have factor_1_3 : (47 : ZMod 388181593801) ^ 15 = 138684756178 := by
        calc
          (47 : ZMod 388181593801) ^ 15 = (47 : ZMod 388181593801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 7 * (47 : ZMod 388181593801) ^ 7) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 138684756178 := by rw [factor_1_2]; decide
      have factor_1_4 : (47 : ZMod 388181593801) ^ 30 = 386868253098 := by
        calc
          (47 : ZMod 388181593801) ^ 30 = (47 : ZMod 388181593801) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 15 * (47 : ZMod 388181593801) ^ 15 := by rw [pow_add]
          _ = 386868253098 := by rw [factor_1_3]; decide
      have factor_1_5 : (47 : ZMod 388181593801) ^ 60 = 240089449764 := by
        calc
          (47 : ZMod 388181593801) ^ 60 = (47 : ZMod 388181593801) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 30 * (47 : ZMod 388181593801) ^ 30 := by rw [pow_add]
          _ = 240089449764 := by rw [factor_1_4]; decide
      have factor_1_6 : (47 : ZMod 388181593801) ^ 120 = 302544226238 := by
        calc
          (47 : ZMod 388181593801) ^ 120 = (47 : ZMod 388181593801) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 60 * (47 : ZMod 388181593801) ^ 60 := by rw [pow_add]
          _ = 302544226238 := by rw [factor_1_5]; decide
      have factor_1_7 : (47 : ZMod 388181593801) ^ 241 = 364114044377 := by
        calc
          (47 : ZMod 388181593801) ^ 241 = (47 : ZMod 388181593801) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 120 * (47 : ZMod 388181593801) ^ 120) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 364114044377 := by rw [factor_1_6]; decide
      have factor_1_8 : (47 : ZMod 388181593801) ^ 482 = 86377034094 := by
        calc
          (47 : ZMod 388181593801) ^ 482 = (47 : ZMod 388181593801) ^ (241 + 241) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 241 * (47 : ZMod 388181593801) ^ 241 := by rw [pow_add]
          _ = 86377034094 := by rw [factor_1_7]; decide
      have factor_1_9 : (47 : ZMod 388181593801) ^ 964 = 364593022780 := by
        calc
          (47 : ZMod 388181593801) ^ 964 = (47 : ZMod 388181593801) ^ (482 + 482) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 482 * (47 : ZMod 388181593801) ^ 482 := by rw [pow_add]
          _ = 364593022780 := by rw [factor_1_8]; decide
      have factor_1_10 : (47 : ZMod 388181593801) ^ 1928 = 363638520386 := by
        calc
          (47 : ZMod 388181593801) ^ 1928 = (47 : ZMod 388181593801) ^ (964 + 964) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 964 * (47 : ZMod 388181593801) ^ 964 := by rw [pow_add]
          _ = 363638520386 := by rw [factor_1_9]; decide
      have factor_1_11 : (47 : ZMod 388181593801) ^ 3856 = 338885387338 := by
        calc
          (47 : ZMod 388181593801) ^ 3856 = (47 : ZMod 388181593801) ^ (1928 + 1928) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1928 * (47 : ZMod 388181593801) ^ 1928 := by rw [pow_add]
          _ = 338885387338 := by rw [factor_1_10]; decide
      have factor_1_12 : (47 : ZMod 388181593801) ^ 7712 = 76709438033 := by
        calc
          (47 : ZMod 388181593801) ^ 7712 = (47 : ZMod 388181593801) ^ (3856 + 3856) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3856 * (47 : ZMod 388181593801) ^ 3856 := by rw [pow_add]
          _ = 76709438033 := by rw [factor_1_11]; decide
      have factor_1_13 : (47 : ZMod 388181593801) ^ 15424 = 356608828469 := by
        calc
          (47 : ZMod 388181593801) ^ 15424 = (47 : ZMod 388181593801) ^ (7712 + 7712) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 7712 * (47 : ZMod 388181593801) ^ 7712 := by rw [pow_add]
          _ = 356608828469 := by rw [factor_1_12]; decide
      have factor_1_14 : (47 : ZMod 388181593801) ^ 30849 = 48923626848 := by
        calc
          (47 : ZMod 388181593801) ^ 30849 = (47 : ZMod 388181593801) ^ (15424 + 15424 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 15424 * (47 : ZMod 388181593801) ^ 15424) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 48923626848 := by rw [factor_1_13]; decide
      have factor_1_15 : (47 : ZMod 388181593801) ^ 61699 = 159646547640 := by
        calc
          (47 : ZMod 388181593801) ^ 61699 = (47 : ZMod 388181593801) ^ (30849 + 30849 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 30849 * (47 : ZMod 388181593801) ^ 30849) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 159646547640 := by rw [factor_1_14]; decide
      have factor_1_16 : (47 : ZMod 388181593801) ^ 123399 = 148376694008 := by
        calc
          (47 : ZMod 388181593801) ^ 123399 = (47 : ZMod 388181593801) ^ (61699 + 61699 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 61699 * (47 : ZMod 388181593801) ^ 61699) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 148376694008 := by rw [factor_1_15]; decide
      have factor_1_17 : (47 : ZMod 388181593801) ^ 246799 = 321874408559 := by
        calc
          (47 : ZMod 388181593801) ^ 246799 = (47 : ZMod 388181593801) ^ (123399 + 123399 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 123399 * (47 : ZMod 388181593801) ^ 123399) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 321874408559 := by rw [factor_1_16]; decide
      have factor_1_18 : (47 : ZMod 388181593801) ^ 493598 = 318926118491 := by
        calc
          (47 : ZMod 388181593801) ^ 493598 = (47 : ZMod 388181593801) ^ (246799 + 246799) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 246799 * (47 : ZMod 388181593801) ^ 246799 := by rw [pow_add]
          _ = 318926118491 := by rw [factor_1_17]; decide
      have factor_1_19 : (47 : ZMod 388181593801) ^ 987196 = 142161753857 := by
        calc
          (47 : ZMod 388181593801) ^ 987196 = (47 : ZMod 388181593801) ^ (493598 + 493598) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 493598 * (47 : ZMod 388181593801) ^ 493598 := by rw [pow_add]
          _ = 142161753857 := by rw [factor_1_18]; decide
      have factor_1_20 : (47 : ZMod 388181593801) ^ 1974393 = 333386944665 := by
        calc
          (47 : ZMod 388181593801) ^ 1974393 = (47 : ZMod 388181593801) ^ (987196 + 987196 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 987196 * (47 : ZMod 388181593801) ^ 987196) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 333386944665 := by rw [factor_1_19]; decide
      have factor_1_21 : (47 : ZMod 388181593801) ^ 3948787 = 312109499798 := by
        calc
          (47 : ZMod 388181593801) ^ 3948787 = (47 : ZMod 388181593801) ^ (1974393 + 1974393 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1974393 * (47 : ZMod 388181593801) ^ 1974393) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 312109499798 := by rw [factor_1_20]; decide
      have factor_1_22 : (47 : ZMod 388181593801) ^ 7897574 = 121107395327 := by
        calc
          (47 : ZMod 388181593801) ^ 7897574 = (47 : ZMod 388181593801) ^ (3948787 + 3948787) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3948787 * (47 : ZMod 388181593801) ^ 3948787 := by rw [pow_add]
          _ = 121107395327 := by rw [factor_1_21]; decide
      have factor_1_23 : (47 : ZMod 388181593801) ^ 15795149 = 121239449308 := by
        calc
          (47 : ZMod 388181593801) ^ 15795149 = (47 : ZMod 388181593801) ^ (7897574 + 7897574 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 7897574 * (47 : ZMod 388181593801) ^ 7897574) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 121239449308 := by rw [factor_1_22]; decide
      have factor_1_24 : (47 : ZMod 388181593801) ^ 31590298 = 157705403149 := by
        calc
          (47 : ZMod 388181593801) ^ 31590298 = (47 : ZMod 388181593801) ^ (15795149 + 15795149) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 15795149 * (47 : ZMod 388181593801) ^ 15795149 := by rw [pow_add]
          _ = 157705403149 := by rw [factor_1_23]; decide
      have factor_1_25 : (47 : ZMod 388181593801) ^ 63180597 = 27194135243 := by
        calc
          (47 : ZMod 388181593801) ^ 63180597 = (47 : ZMod 388181593801) ^ (31590298 + 31590298 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 31590298 * (47 : ZMod 388181593801) ^ 31590298) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 27194135243 := by rw [factor_1_24]; decide
      have factor_1_26 : (47 : ZMod 388181593801) ^ 126361195 = 356658386286 := by
        calc
          (47 : ZMod 388181593801) ^ 126361195 = (47 : ZMod 388181593801) ^ (63180597 + 63180597 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 63180597 * (47 : ZMod 388181593801) ^ 63180597) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 356658386286 := by rw [factor_1_25]; decide
      have factor_1_27 : (47 : ZMod 388181593801) ^ 252722391 = 93404839311 := by
        calc
          (47 : ZMod 388181593801) ^ 252722391 = (47 : ZMod 388181593801) ^ (126361195 + 126361195 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 126361195 * (47 : ZMod 388181593801) ^ 126361195) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 93404839311 := by rw [factor_1_26]; decide
      have factor_1_28 : (47 : ZMod 388181593801) ^ 505444783 = 166760977681 := by
        calc
          (47 : ZMod 388181593801) ^ 505444783 = (47 : ZMod 388181593801) ^ (252722391 + 252722391 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 252722391 * (47 : ZMod 388181593801) ^ 252722391) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 166760977681 := by rw [factor_1_27]; decide
      have factor_1_29 : (47 : ZMod 388181593801) ^ 1010889567 = 29131152380 := by
        calc
          (47 : ZMod 388181593801) ^ 1010889567 = (47 : ZMod 388181593801) ^ (505444783 + 505444783 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 505444783 * (47 : ZMod 388181593801) ^ 505444783) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 29131152380 := by rw [factor_1_28]; decide
      have factor_1_30 : (47 : ZMod 388181593801) ^ 2021779134 = 298304246817 := by
        calc
          (47 : ZMod 388181593801) ^ 2021779134 = (47 : ZMod 388181593801) ^ (1010889567 + 1010889567) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1010889567 * (47 : ZMod 388181593801) ^ 1010889567 := by rw [pow_add]
          _ = 298304246817 := by rw [factor_1_29]; decide
      have factor_1_31 : (47 : ZMod 388181593801) ^ 4043558268 = 174221760967 := by
        calc
          (47 : ZMod 388181593801) ^ 4043558268 = (47 : ZMod 388181593801) ^ (2021779134 + 2021779134) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2021779134 * (47 : ZMod 388181593801) ^ 2021779134 := by rw [pow_add]
          _ = 174221760967 := by rw [factor_1_30]; decide
      have factor_1_32 : (47 : ZMod 388181593801) ^ 8087116537 = 74508425586 := by
        calc
          (47 : ZMod 388181593801) ^ 8087116537 = (47 : ZMod 388181593801) ^ (4043558268 + 4043558268 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 4043558268 * (47 : ZMod 388181593801) ^ 4043558268) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 74508425586 := by rw [factor_1_31]; decide
      have factor_1_33 : (47 : ZMod 388181593801) ^ 16174233075 = 1956913537 := by
        calc
          (47 : ZMod 388181593801) ^ 16174233075 = (47 : ZMod 388181593801) ^ (8087116537 + 8087116537 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 8087116537 * (47 : ZMod 388181593801) ^ 8087116537) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 1956913537 := by rw [factor_1_32]; decide
      have factor_1_34 : (47 : ZMod 388181593801) ^ 32348466150 = 182140566114 := by
        calc
          (47 : ZMod 388181593801) ^ 32348466150 = (47 : ZMod 388181593801) ^ (16174233075 + 16174233075) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 16174233075 * (47 : ZMod 388181593801) ^ 16174233075 := by rw [pow_add]
          _ = 182140566114 := by rw [factor_1_33]; decide
      have factor_1_35 : (47 : ZMod 388181593801) ^ 64696932300 = 230052947218 := by
        calc
          (47 : ZMod 388181593801) ^ 64696932300 = (47 : ZMod 388181593801) ^ (32348466150 + 32348466150) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 32348466150 * (47 : ZMod 388181593801) ^ 32348466150 := by rw [pow_add]
          _ = 230052947218 := by rw [factor_1_34]; decide
      have factor_1_36 : (47 : ZMod 388181593801) ^ 129393864600 = 230052947217 := by
        calc
          (47 : ZMod 388181593801) ^ 129393864600 = (47 : ZMod 388181593801) ^ (64696932300 + 64696932300) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 64696932300 * (47 : ZMod 388181593801) ^ 64696932300 := by rw [pow_add]
          _ = 230052947217 := by rw [factor_1_35]; decide
      change (47 : ZMod 388181593801) ^ 129393864600 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_2_1 : (47 : ZMod 388181593801) ^ 2 = 2209 := by
        calc
          (47 : ZMod 388181593801) ^ 2 = (47 : ZMod 388181593801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_2_0]; decide
      have factor_2_2 : (47 : ZMod 388181593801) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 388181593801) ^ 4 = (47 : ZMod 388181593801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2 * (47 : ZMod 388181593801) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_2_1]; decide
      have factor_2_3 : (47 : ZMod 388181593801) ^ 9 = 2938174484 := by
        calc
          (47 : ZMod 388181593801) ^ 9 = (47 : ZMod 388181593801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 4 * (47 : ZMod 388181593801) ^ 4) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 2938174484 := by rw [factor_2_2]; decide
      have factor_2_4 : (47 : ZMod 388181593801) ^ 18 = 235763401802 := by
        calc
          (47 : ZMod 388181593801) ^ 18 = (47 : ZMod 388181593801) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 9 * (47 : ZMod 388181593801) ^ 9 := by rw [pow_add]
          _ = 235763401802 := by rw [factor_2_3]; decide
      have factor_2_5 : (47 : ZMod 388181593801) ^ 36 = 186242832397 := by
        calc
          (47 : ZMod 388181593801) ^ 36 = (47 : ZMod 388181593801) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 18 * (47 : ZMod 388181593801) ^ 18 := by rw [pow_add]
          _ = 186242832397 := by rw [factor_2_4]; decide
      have factor_2_6 : (47 : ZMod 388181593801) ^ 72 = 260549569399 := by
        calc
          (47 : ZMod 388181593801) ^ 72 = (47 : ZMod 388181593801) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 36 * (47 : ZMod 388181593801) ^ 36 := by rw [pow_add]
          _ = 260549569399 := by rw [factor_2_5]; decide
      have factor_2_7 : (47 : ZMod 388181593801) ^ 144 = 312858037671 := by
        calc
          (47 : ZMod 388181593801) ^ 144 = (47 : ZMod 388181593801) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 72 * (47 : ZMod 388181593801) ^ 72 := by rw [pow_add]
          _ = 312858037671 := by rw [factor_2_6]; decide
      have factor_2_8 : (47 : ZMod 388181593801) ^ 289 = 107767476260 := by
        calc
          (47 : ZMod 388181593801) ^ 289 = (47 : ZMod 388181593801) ^ (144 + 144 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 144 * (47 : ZMod 388181593801) ^ 144) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 107767476260 := by rw [factor_2_7]; decide
      have factor_2_9 : (47 : ZMod 388181593801) ^ 578 = 252988138823 := by
        calc
          (47 : ZMod 388181593801) ^ 578 = (47 : ZMod 388181593801) ^ (289 + 289) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 289 * (47 : ZMod 388181593801) ^ 289 := by rw [pow_add]
          _ = 252988138823 := by rw [factor_2_8]; decide
      have factor_2_10 : (47 : ZMod 388181593801) ^ 1156 = 225369149668 := by
        calc
          (47 : ZMod 388181593801) ^ 1156 = (47 : ZMod 388181593801) ^ (578 + 578) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 578 * (47 : ZMod 388181593801) ^ 578 := by rw [pow_add]
          _ = 225369149668 := by rw [factor_2_9]; decide
      have factor_2_11 : (47 : ZMod 388181593801) ^ 2313 = 121215082795 := by
        calc
          (47 : ZMod 388181593801) ^ 2313 = (47 : ZMod 388181593801) ^ (1156 + 1156 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1156 * (47 : ZMod 388181593801) ^ 1156) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 121215082795 := by rw [factor_2_10]; decide
      have factor_2_12 : (47 : ZMod 388181593801) ^ 4627 = 236694519890 := by
        calc
          (47 : ZMod 388181593801) ^ 4627 = (47 : ZMod 388181593801) ^ (2313 + 2313 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2313 * (47 : ZMod 388181593801) ^ 2313) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 236694519890 := by rw [factor_2_11]; decide
      have factor_2_13 : (47 : ZMod 388181593801) ^ 9254 = 342711728622 := by
        calc
          (47 : ZMod 388181593801) ^ 9254 = (47 : ZMod 388181593801) ^ (4627 + 4627) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 4627 * (47 : ZMod 388181593801) ^ 4627 := by rw [pow_add]
          _ = 342711728622 := by rw [factor_2_12]; decide
      have factor_2_14 : (47 : ZMod 388181593801) ^ 18509 = 169449566623 := by
        calc
          (47 : ZMod 388181593801) ^ 18509 = (47 : ZMod 388181593801) ^ (9254 + 9254 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 9254 * (47 : ZMod 388181593801) ^ 9254) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 169449566623 := by rw [factor_2_13]; decide
      have factor_2_15 : (47 : ZMod 388181593801) ^ 37019 = 54935282560 := by
        calc
          (47 : ZMod 388181593801) ^ 37019 = (47 : ZMod 388181593801) ^ (18509 + 18509 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 18509 * (47 : ZMod 388181593801) ^ 18509) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 54935282560 := by rw [factor_2_14]; decide
      have factor_2_16 : (47 : ZMod 388181593801) ^ 74039 = 191909252975 := by
        calc
          (47 : ZMod 388181593801) ^ 74039 = (47 : ZMod 388181593801) ^ (37019 + 37019 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 37019 * (47 : ZMod 388181593801) ^ 37019) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 191909252975 := by rw [factor_2_15]; decide
      have factor_2_17 : (47 : ZMod 388181593801) ^ 148079 = 2694293375 := by
        calc
          (47 : ZMod 388181593801) ^ 148079 = (47 : ZMod 388181593801) ^ (74039 + 74039 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 74039 * (47 : ZMod 388181593801) ^ 74039) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 2694293375 := by rw [factor_2_16]; decide
      have factor_2_18 : (47 : ZMod 388181593801) ^ 296159 = 178315219819 := by
        calc
          (47 : ZMod 388181593801) ^ 296159 = (47 : ZMod 388181593801) ^ (148079 + 148079 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 148079 * (47 : ZMod 388181593801) ^ 148079) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 178315219819 := by rw [factor_2_17]; decide
      have factor_2_19 : (47 : ZMod 388181593801) ^ 592318 = 41998384334 := by
        calc
          (47 : ZMod 388181593801) ^ 592318 = (47 : ZMod 388181593801) ^ (296159 + 296159) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 296159 * (47 : ZMod 388181593801) ^ 296159 := by rw [pow_add]
          _ = 41998384334 := by rw [factor_2_18]; decide
      have factor_2_20 : (47 : ZMod 388181593801) ^ 1184636 = 310174817848 := by
        calc
          (47 : ZMod 388181593801) ^ 1184636 = (47 : ZMod 388181593801) ^ (592318 + 592318) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 592318 * (47 : ZMod 388181593801) ^ 592318 := by rw [pow_add]
          _ = 310174817848 := by rw [factor_2_19]; decide
      have factor_2_21 : (47 : ZMod 388181593801) ^ 2369272 = 96770718238 := by
        calc
          (47 : ZMod 388181593801) ^ 2369272 = (47 : ZMod 388181593801) ^ (1184636 + 1184636) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1184636 * (47 : ZMod 388181593801) ^ 1184636 := by rw [pow_add]
          _ = 96770718238 := by rw [factor_2_20]; decide
      have factor_2_22 : (47 : ZMod 388181593801) ^ 4738544 = 85170427172 := by
        calc
          (47 : ZMod 388181593801) ^ 4738544 = (47 : ZMod 388181593801) ^ (2369272 + 2369272) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2369272 * (47 : ZMod 388181593801) ^ 2369272 := by rw [pow_add]
          _ = 85170427172 := by rw [factor_2_21]; decide
      have factor_2_23 : (47 : ZMod 388181593801) ^ 9477089 = 386248662832 := by
        calc
          (47 : ZMod 388181593801) ^ 9477089 = (47 : ZMod 388181593801) ^ (4738544 + 4738544 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 4738544 * (47 : ZMod 388181593801) ^ 4738544) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 386248662832 := by rw [factor_2_22]; decide
      have factor_2_24 : (47 : ZMod 388181593801) ^ 18954179 = 66780238680 := by
        calc
          (47 : ZMod 388181593801) ^ 18954179 = (47 : ZMod 388181593801) ^ (9477089 + 9477089 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 9477089 * (47 : ZMod 388181593801) ^ 9477089) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 66780238680 := by rw [factor_2_23]; decide
      have factor_2_25 : (47 : ZMod 388181593801) ^ 37908358 = 224764978130 := by
        calc
          (47 : ZMod 388181593801) ^ 37908358 = (47 : ZMod 388181593801) ^ (18954179 + 18954179) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 18954179 * (47 : ZMod 388181593801) ^ 18954179 := by rw [pow_add]
          _ = 224764978130 := by rw [factor_2_24]; decide
      have factor_2_26 : (47 : ZMod 388181593801) ^ 75816717 = 333630695674 := by
        calc
          (47 : ZMod 388181593801) ^ 75816717 = (47 : ZMod 388181593801) ^ (37908358 + 37908358 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 37908358 * (47 : ZMod 388181593801) ^ 37908358) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 333630695674 := by rw [factor_2_25]; decide
      have factor_2_27 : (47 : ZMod 388181593801) ^ 151633435 = 190440183839 := by
        calc
          (47 : ZMod 388181593801) ^ 151633435 = (47 : ZMod 388181593801) ^ (75816717 + 75816717 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 75816717 * (47 : ZMod 388181593801) ^ 75816717) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 190440183839 := by rw [factor_2_26]; decide
      have factor_2_28 : (47 : ZMod 388181593801) ^ 303266870 = 68420675925 := by
        calc
          (47 : ZMod 388181593801) ^ 303266870 = (47 : ZMod 388181593801) ^ (151633435 + 151633435) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 151633435 * (47 : ZMod 388181593801) ^ 151633435 := by rw [pow_add]
          _ = 68420675925 := by rw [factor_2_27]; decide
      have factor_2_29 : (47 : ZMod 388181593801) ^ 606533740 = 29647858018 := by
        calc
          (47 : ZMod 388181593801) ^ 606533740 = (47 : ZMod 388181593801) ^ (303266870 + 303266870) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 303266870 * (47 : ZMod 388181593801) ^ 303266870 := by rw [pow_add]
          _ = 29647858018 := by rw [factor_2_28]; decide
      have factor_2_30 : (47 : ZMod 388181593801) ^ 1213067480 = 72635121436 := by
        calc
          (47 : ZMod 388181593801) ^ 1213067480 = (47 : ZMod 388181593801) ^ (606533740 + 606533740) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 606533740 * (47 : ZMod 388181593801) ^ 606533740 := by rw [pow_add]
          _ = 72635121436 := by rw [factor_2_29]; decide
      have factor_2_31 : (47 : ZMod 388181593801) ^ 2426134961 = 355390273366 := by
        calc
          (47 : ZMod 388181593801) ^ 2426134961 = (47 : ZMod 388181593801) ^ (1213067480 + 1213067480 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1213067480 * (47 : ZMod 388181593801) ^ 1213067480) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 355390273366 := by rw [factor_2_30]; decide
      have factor_2_32 : (47 : ZMod 388181593801) ^ 4852269922 = 92882048838 := by
        calc
          (47 : ZMod 388181593801) ^ 4852269922 = (47 : ZMod 388181593801) ^ (2426134961 + 2426134961) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2426134961 * (47 : ZMod 388181593801) ^ 2426134961 := by rw [pow_add]
          _ = 92882048838 := by rw [factor_2_31]; decide
      have factor_2_33 : (47 : ZMod 388181593801) ^ 9704539845 = 276016514484 := by
        calc
          (47 : ZMod 388181593801) ^ 9704539845 = (47 : ZMod 388181593801) ^ (4852269922 + 4852269922 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 4852269922 * (47 : ZMod 388181593801) ^ 4852269922) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 276016514484 := by rw [factor_2_32]; decide
      have factor_2_34 : (47 : ZMod 388181593801) ^ 19409079690 = 18632582370 := by
        calc
          (47 : ZMod 388181593801) ^ 19409079690 = (47 : ZMod 388181593801) ^ (9704539845 + 9704539845) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 9704539845 * (47 : ZMod 388181593801) ^ 9704539845 := by rw [pow_add]
          _ = 18632582370 := by rw [factor_2_33]; decide
      have factor_2_35 : (47 : ZMod 388181593801) ^ 38818159380 = 174233052385 := by
        calc
          (47 : ZMod 388181593801) ^ 38818159380 = (47 : ZMod 388181593801) ^ (19409079690 + 19409079690) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 19409079690 * (47 : ZMod 388181593801) ^ 19409079690 := by rw [pow_add]
          _ = 174233052385 := by rw [factor_2_34]; decide
      have factor_2_36 : (47 : ZMod 388181593801) ^ 77636318760 = 329710327852 := by
        calc
          (47 : ZMod 388181593801) ^ 77636318760 = (47 : ZMod 388181593801) ^ (38818159380 + 38818159380) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 38818159380 * (47 : ZMod 388181593801) ^ 38818159380 := by rw [pow_add]
          _ = 329710327852 := by rw [factor_2_35]; decide
      change (47 : ZMod 388181593801) ^ 77636318760 ≠ 1
      rw [factor_2_36]
      decide
    ·
      have factor_3_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_3_1 : (47 : ZMod 388181593801) ^ 3 = 103823 := by
        calc
          (47 : ZMod 388181593801) ^ 3 = (47 : ZMod 388181593801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_3_0]; decide
      have factor_3_2 : (47 : ZMod 388181593801) ^ 6 = 10779215329 := by
        calc
          (47 : ZMod 388181593801) ^ 6 = (47 : ZMod 388181593801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3 * (47 : ZMod 388181593801) ^ 3 := by rw [pow_add]
          _ = 10779215329 := by rw [factor_3_1]; decide
      have factor_3_3 : (47 : ZMod 388181593801) ^ 12 = 327538318547 := by
        calc
          (47 : ZMod 388181593801) ^ 12 = (47 : ZMod 388181593801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 6 * (47 : ZMod 388181593801) ^ 6 := by rw [pow_add]
          _ = 327538318547 := by rw [factor_3_2]; decide
      have factor_3_4 : (47 : ZMod 388181593801) ^ 25 = 37333237754 := by
        calc
          (47 : ZMod 388181593801) ^ 25 = (47 : ZMod 388181593801) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 12 * (47 : ZMod 388181593801) ^ 12) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 37333237754 := by rw [factor_3_3]; decide
      have factor_3_5 : (47 : ZMod 388181593801) ^ 51 = 77715906827 := by
        calc
          (47 : ZMod 388181593801) ^ 51 = (47 : ZMod 388181593801) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 25 * (47 : ZMod 388181593801) ^ 25) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 77715906827 := by rw [factor_3_4]; decide
      have factor_3_6 : (47 : ZMod 388181593801) ^ 103 = 78384563126 := by
        calc
          (47 : ZMod 388181593801) ^ 103 = (47 : ZMod 388181593801) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 51 * (47 : ZMod 388181593801) ^ 51) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 78384563126 := by rw [factor_3_5]; decide
      have factor_3_7 : (47 : ZMod 388181593801) ^ 206 = 116136761290 := by
        calc
          (47 : ZMod 388181593801) ^ 206 = (47 : ZMod 388181593801) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 103 * (47 : ZMod 388181593801) ^ 103 := by rw [pow_add]
          _ = 116136761290 := by rw [factor_3_6]; decide
      have factor_3_8 : (47 : ZMod 388181593801) ^ 413 = 294986976269 := by
        calc
          (47 : ZMod 388181593801) ^ 413 = (47 : ZMod 388181593801) ^ (206 + 206 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 206 * (47 : ZMod 388181593801) ^ 206) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 294986976269 := by rw [factor_3_7]; decide
      have factor_3_9 : (47 : ZMod 388181593801) ^ 826 = 257885188531 := by
        calc
          (47 : ZMod 388181593801) ^ 826 = (47 : ZMod 388181593801) ^ (413 + 413) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 413 * (47 : ZMod 388181593801) ^ 413 := by rw [pow_add]
          _ = 257885188531 := by rw [factor_3_8]; decide
      have factor_3_10 : (47 : ZMod 388181593801) ^ 1652 = 339940952271 := by
        calc
          (47 : ZMod 388181593801) ^ 1652 = (47 : ZMod 388181593801) ^ (826 + 826) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 826 * (47 : ZMod 388181593801) ^ 826 := by rw [pow_add]
          _ = 339940952271 := by rw [factor_3_9]; decide
      have factor_3_11 : (47 : ZMod 388181593801) ^ 3305 = 234986164775 := by
        calc
          (47 : ZMod 388181593801) ^ 3305 = (47 : ZMod 388181593801) ^ (1652 + 1652 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1652 * (47 : ZMod 388181593801) ^ 1652) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 234986164775 := by rw [factor_3_10]; decide
      have factor_3_12 : (47 : ZMod 388181593801) ^ 6610 = 137181724260 := by
        calc
          (47 : ZMod 388181593801) ^ 6610 = (47 : ZMod 388181593801) ^ (3305 + 3305) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3305 * (47 : ZMod 388181593801) ^ 3305 := by rw [pow_add]
          _ = 137181724260 := by rw [factor_3_11]; decide
      have factor_3_13 : (47 : ZMod 388181593801) ^ 13221 = 55573276258 := by
        calc
          (47 : ZMod 388181593801) ^ 13221 = (47 : ZMod 388181593801) ^ (6610 + 6610 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 6610 * (47 : ZMod 388181593801) ^ 6610) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 55573276258 := by rw [factor_3_12]; decide
      have factor_3_14 : (47 : ZMod 388181593801) ^ 26442 = 30273563241 := by
        calc
          (47 : ZMod 388181593801) ^ 26442 = (47 : ZMod 388181593801) ^ (13221 + 13221) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 13221 * (47 : ZMod 388181593801) ^ 13221 := by rw [pow_add]
          _ = 30273563241 := by rw [factor_3_13]; decide
      have factor_3_15 : (47 : ZMod 388181593801) ^ 52885 = 387629052146 := by
        calc
          (47 : ZMod 388181593801) ^ 52885 = (47 : ZMod 388181593801) ^ (26442 + 26442 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 26442 * (47 : ZMod 388181593801) ^ 26442) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 387629052146 := by rw [factor_3_14]; decide
      have factor_3_16 : (47 : ZMod 388181593801) ^ 105771 = 38256559383 := by
        calc
          (47 : ZMod 388181593801) ^ 105771 = (47 : ZMod 388181593801) ^ (52885 + 52885 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 52885 * (47 : ZMod 388181593801) ^ 52885) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 38256559383 := by rw [factor_3_15]; decide
      have factor_3_17 : (47 : ZMod 388181593801) ^ 211542 = 346259298259 := by
        calc
          (47 : ZMod 388181593801) ^ 211542 = (47 : ZMod 388181593801) ^ (105771 + 105771) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 105771 * (47 : ZMod 388181593801) ^ 105771 := by rw [pow_add]
          _ = 346259298259 := by rw [factor_3_16]; decide
      have factor_3_18 : (47 : ZMod 388181593801) ^ 423084 = 171803540233 := by
        calc
          (47 : ZMod 388181593801) ^ 423084 = (47 : ZMod 388181593801) ^ (211542 + 211542) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 211542 * (47 : ZMod 388181593801) ^ 211542 := by rw [pow_add]
          _ = 171803540233 := by rw [factor_3_17]; decide
      have factor_3_19 : (47 : ZMod 388181593801) ^ 846168 = 362719534748 := by
        calc
          (47 : ZMod 388181593801) ^ 846168 = (47 : ZMod 388181593801) ^ (423084 + 423084) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 423084 * (47 : ZMod 388181593801) ^ 423084 := by rw [pow_add]
          _ = 362719534748 := by rw [factor_3_18]; decide
      have factor_3_20 : (47 : ZMod 388181593801) ^ 1692337 = 177573752371 := by
        calc
          (47 : ZMod 388181593801) ^ 1692337 = (47 : ZMod 388181593801) ^ (846168 + 846168 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 846168 * (47 : ZMod 388181593801) ^ 846168) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 177573752371 := by rw [factor_3_19]; decide
      have factor_3_21 : (47 : ZMod 388181593801) ^ 3384674 = 76548687777 := by
        calc
          (47 : ZMod 388181593801) ^ 3384674 = (47 : ZMod 388181593801) ^ (1692337 + 1692337) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1692337 * (47 : ZMod 388181593801) ^ 1692337 := by rw [pow_add]
          _ = 76548687777 := by rw [factor_3_20]; decide
      have factor_3_22 : (47 : ZMod 388181593801) ^ 6769349 = 8221445217 := by
        calc
          (47 : ZMod 388181593801) ^ 6769349 = (47 : ZMod 388181593801) ^ (3384674 + 3384674 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 3384674 * (47 : ZMod 388181593801) ^ 3384674) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 8221445217 := by rw [factor_3_21]; decide
      have factor_3_23 : (47 : ZMod 388181593801) ^ 13538699 = 351178942367 := by
        calc
          (47 : ZMod 388181593801) ^ 13538699 = (47 : ZMod 388181593801) ^ (6769349 + 6769349 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 6769349 * (47 : ZMod 388181593801) ^ 6769349) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 351178942367 := by rw [factor_3_22]; decide
      have factor_3_24 : (47 : ZMod 388181593801) ^ 27077399 = 205854834216 := by
        calc
          (47 : ZMod 388181593801) ^ 27077399 = (47 : ZMod 388181593801) ^ (13538699 + 13538699 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 13538699 * (47 : ZMod 388181593801) ^ 13538699) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 205854834216 := by rw [factor_3_23]; decide
      have factor_3_25 : (47 : ZMod 388181593801) ^ 54154798 = 139474937657 := by
        calc
          (47 : ZMod 388181593801) ^ 54154798 = (47 : ZMod 388181593801) ^ (27077399 + 27077399) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 27077399 * (47 : ZMod 388181593801) ^ 27077399 := by rw [pow_add]
          _ = 139474937657 := by rw [factor_3_24]; decide
      have factor_3_26 : (47 : ZMod 388181593801) ^ 108309596 = 116039205087 := by
        calc
          (47 : ZMod 388181593801) ^ 108309596 = (47 : ZMod 388181593801) ^ (54154798 + 54154798) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 54154798 * (47 : ZMod 388181593801) ^ 54154798 := by rw [pow_add]
          _ = 116039205087 := by rw [factor_3_25]; decide
      have factor_3_27 : (47 : ZMod 388181593801) ^ 216619192 = 137543016704 := by
        calc
          (47 : ZMod 388181593801) ^ 216619192 = (47 : ZMod 388181593801) ^ (108309596 + 108309596) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 108309596 * (47 : ZMod 388181593801) ^ 108309596 := by rw [pow_add]
          _ = 137543016704 := by rw [factor_3_26]; decide
      have factor_3_28 : (47 : ZMod 388181593801) ^ 433238385 = 366539659684 := by
        calc
          (47 : ZMod 388181593801) ^ 433238385 = (47 : ZMod 388181593801) ^ (216619192 + 216619192 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 216619192 * (47 : ZMod 388181593801) ^ 216619192) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 366539659684 := by rw [factor_3_27]; decide
      have factor_3_29 : (47 : ZMod 388181593801) ^ 866476771 = 47435822343 := by
        calc
          (47 : ZMod 388181593801) ^ 866476771 = (47 : ZMod 388181593801) ^ (433238385 + 433238385 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 433238385 * (47 : ZMod 388181593801) ^ 433238385) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 47435822343 := by rw [factor_3_28]; decide
      have factor_3_30 : (47 : ZMod 388181593801) ^ 1732953543 = 175802198879 := by
        calc
          (47 : ZMod 388181593801) ^ 1732953543 = (47 : ZMod 388181593801) ^ (866476771 + 866476771 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 866476771 * (47 : ZMod 388181593801) ^ 866476771) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 175802198879 := by rw [factor_3_29]; decide
      have factor_3_31 : (47 : ZMod 388181593801) ^ 3465907087 = 283152343452 := by
        calc
          (47 : ZMod 388181593801) ^ 3465907087 = (47 : ZMod 388181593801) ^ (1732953543 + 1732953543 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1732953543 * (47 : ZMod 388181593801) ^ 1732953543) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 283152343452 := by rw [factor_3_30]; decide
      have factor_3_32 : (47 : ZMod 388181593801) ^ 6931814175 = 200434279359 := by
        calc
          (47 : ZMod 388181593801) ^ 6931814175 = (47 : ZMod 388181593801) ^ (3465907087 + 3465907087 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 3465907087 * (47 : ZMod 388181593801) ^ 3465907087) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 200434279359 := by rw [factor_3_31]; decide
      have factor_3_33 : (47 : ZMod 388181593801) ^ 13863628350 = 334067563343 := by
        calc
          (47 : ZMod 388181593801) ^ 13863628350 = (47 : ZMod 388181593801) ^ (6931814175 + 6931814175) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 6931814175 * (47 : ZMod 388181593801) ^ 6931814175 := by rw [pow_add]
          _ = 334067563343 := by rw [factor_3_32]; decide
      have factor_3_34 : (47 : ZMod 388181593801) ^ 27727256700 = 193459152743 := by
        calc
          (47 : ZMod 388181593801) ^ 27727256700 = (47 : ZMod 388181593801) ^ (13863628350 + 13863628350) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 13863628350 * (47 : ZMod 388181593801) ^ 13863628350 := by rw [pow_add]
          _ = 193459152743 := by rw [factor_3_33]; decide
      have factor_3_35 : (47 : ZMod 388181593801) ^ 55454513400 = 38005037153 := by
        calc
          (47 : ZMod 388181593801) ^ 55454513400 = (47 : ZMod 388181593801) ^ (27727256700 + 27727256700) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 27727256700 * (47 : ZMod 388181593801) ^ 27727256700 := by rw [pow_add]
          _ = 38005037153 := by rw [factor_3_34]; decide
      change (47 : ZMod 388181593801) ^ 55454513400 ≠ 1
      rw [factor_3_35]
      decide
    ·
      have factor_4_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_4_1 : (47 : ZMod 388181593801) ^ 2 = 2209 := by
        calc
          (47 : ZMod 388181593801) ^ 2 = (47 : ZMod 388181593801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_4_0]; decide
      have factor_4_2 : (47 : ZMod 388181593801) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 388181593801) ^ 4 = (47 : ZMod 388181593801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2 * (47 : ZMod 388181593801) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_4_1]; decide
      have factor_4_3 : (47 : ZMod 388181593801) ^ 8 = 132209439900 := by
        calc
          (47 : ZMod 388181593801) ^ 8 = (47 : ZMod 388181593801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 4 * (47 : ZMod 388181593801) ^ 4 := by rw [pow_add]
          _ = 132209439900 := by rw [factor_4_2]; decide
      have factor_4_4 : (47 : ZMod 388181593801) ^ 16 = 307278039550 := by
        calc
          (47 : ZMod 388181593801) ^ 16 = (47 : ZMod 388181593801) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 8 * (47 : ZMod 388181593801) ^ 8 := by rw [pow_add]
          _ = 307278039550 := by rw [factor_4_3]; decide
      have factor_4_5 : (47 : ZMod 388181593801) ^ 32 = 204283137481 := by
        calc
          (47 : ZMod 388181593801) ^ 32 = (47 : ZMod 388181593801) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 16 * (47 : ZMod 388181593801) ^ 16 := by rw [pow_add]
          _ = 204283137481 := by rw [factor_4_4]; decide
      have factor_4_6 : (47 : ZMod 388181593801) ^ 65 = 69575003973 := by
        calc
          (47 : ZMod 388181593801) ^ 65 = (47 : ZMod 388181593801) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 32 * (47 : ZMod 388181593801) ^ 32) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 69575003973 := by rw [factor_4_5]; decide
      have factor_4_7 : (47 : ZMod 388181593801) ^ 131 = 257235305997 := by
        calc
          (47 : ZMod 388181593801) ^ 131 = (47 : ZMod 388181593801) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 65 * (47 : ZMod 388181593801) ^ 65) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 257235305997 := by rw [factor_4_6]; decide
      have factor_4_8 : (47 : ZMod 388181593801) ^ 262 = 357457485334 := by
        calc
          (47 : ZMod 388181593801) ^ 262 = (47 : ZMod 388181593801) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 131 * (47 : ZMod 388181593801) ^ 131 := by rw [pow_add]
          _ = 357457485334 := by rw [factor_4_7]; decide
      have factor_4_9 : (47 : ZMod 388181593801) ^ 525 = 91063282496 := by
        calc
          (47 : ZMod 388181593801) ^ 525 = (47 : ZMod 388181593801) ^ (262 + 262 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 262 * (47 : ZMod 388181593801) ^ 262) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 91063282496 := by rw [factor_4_8]; decide
      have factor_4_10 : (47 : ZMod 388181593801) ^ 1051 = 243247055876 := by
        calc
          (47 : ZMod 388181593801) ^ 1051 = (47 : ZMod 388181593801) ^ (525 + 525 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 525 * (47 : ZMod 388181593801) ^ 525) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 243247055876 := by rw [factor_4_9]; decide
      have factor_4_11 : (47 : ZMod 388181593801) ^ 2103 = 30485309845 := by
        calc
          (47 : ZMod 388181593801) ^ 2103 = (47 : ZMod 388181593801) ^ (1051 + 1051 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1051 * (47 : ZMod 388181593801) ^ 1051) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 30485309845 := by rw [factor_4_10]; decide
      have factor_4_12 : (47 : ZMod 388181593801) ^ 4206 = 117083761567 := by
        calc
          (47 : ZMod 388181593801) ^ 4206 = (47 : ZMod 388181593801) ^ (2103 + 2103) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2103 * (47 : ZMod 388181593801) ^ 2103 := by rw [pow_add]
          _ = 117083761567 := by rw [factor_4_11]; decide
      have factor_4_13 : (47 : ZMod 388181593801) ^ 8413 = 109565094427 := by
        calc
          (47 : ZMod 388181593801) ^ 8413 = (47 : ZMod 388181593801) ^ (4206 + 4206 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 4206 * (47 : ZMod 388181593801) ^ 4206) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 109565094427 := by rw [factor_4_12]; decide
      have factor_4_14 : (47 : ZMod 388181593801) ^ 16827 = 194691235169 := by
        calc
          (47 : ZMod 388181593801) ^ 16827 = (47 : ZMod 388181593801) ^ (8413 + 8413 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 8413 * (47 : ZMod 388181593801) ^ 8413) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 194691235169 := by rw [factor_4_13]; decide
      have factor_4_15 : (47 : ZMod 388181593801) ^ 33654 = 32901638086 := by
        calc
          (47 : ZMod 388181593801) ^ 33654 = (47 : ZMod 388181593801) ^ (16827 + 16827) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 16827 * (47 : ZMod 388181593801) ^ 16827 := by rw [pow_add]
          _ = 32901638086 := by rw [factor_4_14]; decide
      have factor_4_16 : (47 : ZMod 388181593801) ^ 67308 = 360472816873 := by
        calc
          (47 : ZMod 388181593801) ^ 67308 = (47 : ZMod 388181593801) ^ (33654 + 33654) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 33654 * (47 : ZMod 388181593801) ^ 33654 := by rw [pow_add]
          _ = 360472816873 := by rw [factor_4_15]; decide
      have factor_4_17 : (47 : ZMod 388181593801) ^ 134617 = 133601856391 := by
        calc
          (47 : ZMod 388181593801) ^ 134617 = (47 : ZMod 388181593801) ^ (67308 + 67308 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 67308 * (47 : ZMod 388181593801) ^ 67308) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 133601856391 := by rw [factor_4_16]; decide
      have factor_4_18 : (47 : ZMod 388181593801) ^ 269235 = 100793988466 := by
        calc
          (47 : ZMod 388181593801) ^ 269235 = (47 : ZMod 388181593801) ^ (134617 + 134617 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 134617 * (47 : ZMod 388181593801) ^ 134617) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 100793988466 := by rw [factor_4_17]; decide
      have factor_4_19 : (47 : ZMod 388181593801) ^ 538471 = 65482775828 := by
        calc
          (47 : ZMod 388181593801) ^ 538471 = (47 : ZMod 388181593801) ^ (269235 + 269235 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 269235 * (47 : ZMod 388181593801) ^ 269235) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 65482775828 := by rw [factor_4_18]; decide
      have factor_4_20 : (47 : ZMod 388181593801) ^ 1076942 = 352477905013 := by
        calc
          (47 : ZMod 388181593801) ^ 1076942 = (47 : ZMod 388181593801) ^ (538471 + 538471) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 538471 * (47 : ZMod 388181593801) ^ 538471 := by rw [pow_add]
          _ = 352477905013 := by rw [factor_4_19]; decide
      have factor_4_21 : (47 : ZMod 388181593801) ^ 2153884 = 214937002208 := by
        calc
          (47 : ZMod 388181593801) ^ 2153884 = (47 : ZMod 388181593801) ^ (1076942 + 1076942) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1076942 * (47 : ZMod 388181593801) ^ 1076942 := by rw [pow_add]
          _ = 214937002208 := by rw [factor_4_20]; decide
      have factor_4_22 : (47 : ZMod 388181593801) ^ 4307768 = 165002524235 := by
        calc
          (47 : ZMod 388181593801) ^ 4307768 = (47 : ZMod 388181593801) ^ (2153884 + 2153884) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2153884 * (47 : ZMod 388181593801) ^ 2153884 := by rw [pow_add]
          _ = 165002524235 := by rw [factor_4_21]; decide
      have factor_4_23 : (47 : ZMod 388181593801) ^ 8615536 = 195757707151 := by
        calc
          (47 : ZMod 388181593801) ^ 8615536 = (47 : ZMod 388181593801) ^ (4307768 + 4307768) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 4307768 * (47 : ZMod 388181593801) ^ 4307768 := by rw [pow_add]
          _ = 195757707151 := by rw [factor_4_22]; decide
      have factor_4_24 : (47 : ZMod 388181593801) ^ 17231072 = 200467986937 := by
        calc
          (47 : ZMod 388181593801) ^ 17231072 = (47 : ZMod 388181593801) ^ (8615536 + 8615536) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 8615536 * (47 : ZMod 388181593801) ^ 8615536 := by rw [pow_add]
          _ = 200467986937 := by rw [factor_4_23]; decide
      have factor_4_25 : (47 : ZMod 388181593801) ^ 34462144 = 334982208659 := by
        calc
          (47 : ZMod 388181593801) ^ 34462144 = (47 : ZMod 388181593801) ^ (17231072 + 17231072) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 17231072 * (47 : ZMod 388181593801) ^ 17231072 := by rw [pow_add]
          _ = 334982208659 := by rw [factor_4_24]; decide
      have factor_4_26 : (47 : ZMod 388181593801) ^ 68924288 = 69659185487 := by
        calc
          (47 : ZMod 388181593801) ^ 68924288 = (47 : ZMod 388181593801) ^ (34462144 + 34462144) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 34462144 * (47 : ZMod 388181593801) ^ 34462144 := by rw [pow_add]
          _ = 69659185487 := by rw [factor_4_25]; decide
      have factor_4_27 : (47 : ZMod 388181593801) ^ 137848577 = 117161060493 := by
        calc
          (47 : ZMod 388181593801) ^ 137848577 = (47 : ZMod 388181593801) ^ (68924288 + 68924288 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 68924288 * (47 : ZMod 388181593801) ^ 68924288) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 117161060493 := by rw [factor_4_26]; decide
      have factor_4_28 : (47 : ZMod 388181593801) ^ 275697154 = 304433624049 := by
        calc
          (47 : ZMod 388181593801) ^ 275697154 = (47 : ZMod 388181593801) ^ (137848577 + 137848577) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 137848577 * (47 : ZMod 388181593801) ^ 137848577 := by rw [pow_add]
          _ = 304433624049 := by rw [factor_4_27]; decide
      have factor_4_29 : (47 : ZMod 388181593801) ^ 551394309 = 70516897753 := by
        calc
          (47 : ZMod 388181593801) ^ 551394309 = (47 : ZMod 388181593801) ^ (275697154 + 275697154 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 275697154 * (47 : ZMod 388181593801) ^ 275697154) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 70516897753 := by rw [factor_4_28]; decide
      have factor_4_30 : (47 : ZMod 388181593801) ^ 1102788618 = 344379259951 := by
        calc
          (47 : ZMod 388181593801) ^ 1102788618 = (47 : ZMod 388181593801) ^ (551394309 + 551394309) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 551394309 * (47 : ZMod 388181593801) ^ 551394309 := by rw [pow_add]
          _ = 344379259951 := by rw [factor_4_29]; decide
      have factor_4_31 : (47 : ZMod 388181593801) ^ 2205577237 = 2705658972 := by
        calc
          (47 : ZMod 388181593801) ^ 2205577237 = (47 : ZMod 388181593801) ^ (1102788618 + 1102788618 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1102788618 * (47 : ZMod 388181593801) ^ 1102788618) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 2705658972 := by rw [factor_4_30]; decide
      have factor_4_32 : (47 : ZMod 388181593801) ^ 4411154475 = 180673648929 := by
        calc
          (47 : ZMod 388181593801) ^ 4411154475 = (47 : ZMod 388181593801) ^ (2205577237 + 2205577237 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2205577237 * (47 : ZMod 388181593801) ^ 2205577237) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 180673648929 := by rw [factor_4_31]; decide
      have factor_4_33 : (47 : ZMod 388181593801) ^ 8822308950 = 309058519100 := by
        calc
          (47 : ZMod 388181593801) ^ 8822308950 = (47 : ZMod 388181593801) ^ (4411154475 + 4411154475) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 4411154475 * (47 : ZMod 388181593801) ^ 4411154475 := by rw [pow_add]
          _ = 309058519100 := by rw [factor_4_32]; decide
      have factor_4_34 : (47 : ZMod 388181593801) ^ 17644617900 = 344043961120 := by
        calc
          (47 : ZMod 388181593801) ^ 17644617900 = (47 : ZMod 388181593801) ^ (8822308950 + 8822308950) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 8822308950 * (47 : ZMod 388181593801) ^ 8822308950 := by rw [pow_add]
          _ = 344043961120 := by rw [factor_4_33]; decide
      have factor_4_35 : (47 : ZMod 388181593801) ^ 35289235800 = 92791322993 := by
        calc
          (47 : ZMod 388181593801) ^ 35289235800 = (47 : ZMod 388181593801) ^ (17644617900 + 17644617900) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 17644617900 * (47 : ZMod 388181593801) ^ 17644617900 := by rw [pow_add]
          _ = 92791322993 := by rw [factor_4_34]; decide
      change (47 : ZMod 388181593801) ^ 35289235800 ≠ 1
      rw [factor_4_35]
      decide
    ·
      have factor_5_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_5_1 : (47 : ZMod 388181593801) ^ 3 = 103823 := by
        calc
          (47 : ZMod 388181593801) ^ 3 = (47 : ZMod 388181593801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_5_0]; decide
      have factor_5_2 : (47 : ZMod 388181593801) ^ 6 = 10779215329 := by
        calc
          (47 : ZMod 388181593801) ^ 6 = (47 : ZMod 388181593801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3 * (47 : ZMod 388181593801) ^ 3 := by rw [pow_add]
          _ = 10779215329 := by rw [factor_5_1]; decide
      have factor_5_3 : (47 : ZMod 388181593801) ^ 13 = 255218813470 := by
        calc
          (47 : ZMod 388181593801) ^ 13 = (47 : ZMod 388181593801) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 6 * (47 : ZMod 388181593801) ^ 6) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 255218813470 := by rw [factor_5_2]; decide
      have factor_5_4 : (47 : ZMod 388181593801) ^ 27 = 174624312774 := by
        calc
          (47 : ZMod 388181593801) ^ 27 = (47 : ZMod 388181593801) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 13 * (47 : ZMod 388181593801) ^ 13) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 174624312774 := by rw [factor_5_3]; decide
      have factor_5_5 : (47 : ZMod 388181593801) ^ 55 = 260419908451 := by
        calc
          (47 : ZMod 388181593801) ^ 55 = (47 : ZMod 388181593801) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 27 * (47 : ZMod 388181593801) ^ 27) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 260419908451 := by rw [factor_5_4]; decide
      have factor_5_6 : (47 : ZMod 388181593801) ^ 111 = 217856586634 := by
        calc
          (47 : ZMod 388181593801) ^ 111 = (47 : ZMod 388181593801) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 55 * (47 : ZMod 388181593801) ^ 55) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 217856586634 := by rw [factor_5_5]; decide
      have factor_5_7 : (47 : ZMod 388181593801) ^ 222 = 255280417766 := by
        calc
          (47 : ZMod 388181593801) ^ 222 = (47 : ZMod 388181593801) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 111 * (47 : ZMod 388181593801) ^ 111 := by rw [pow_add]
          _ = 255280417766 := by rw [factor_5_6]; decide
      have factor_5_8 : (47 : ZMod 388181593801) ^ 444 = 327403782224 := by
        calc
          (47 : ZMod 388181593801) ^ 444 = (47 : ZMod 388181593801) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 222 * (47 : ZMod 388181593801) ^ 222 := by rw [pow_add]
          _ = 327403782224 := by rw [factor_5_7]; decide
      have factor_5_9 : (47 : ZMod 388181593801) ^ 889 = 339573306823 := by
        calc
          (47 : ZMod 388181593801) ^ 889 = (47 : ZMod 388181593801) ^ (444 + 444 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 444 * (47 : ZMod 388181593801) ^ 444) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 339573306823 := by rw [factor_5_8]; decide
      have factor_5_10 : (47 : ZMod 388181593801) ^ 1779 = 155606901181 := by
        calc
          (47 : ZMod 388181593801) ^ 1779 = (47 : ZMod 388181593801) ^ (889 + 889 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 889 * (47 : ZMod 388181593801) ^ 889) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 155606901181 := by rw [factor_5_9]; decide
      have factor_5_11 : (47 : ZMod 388181593801) ^ 3559 = 198387738507 := by
        calc
          (47 : ZMod 388181593801) ^ 3559 = (47 : ZMod 388181593801) ^ (1779 + 1779 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1779 * (47 : ZMod 388181593801) ^ 1779) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 198387738507 := by rw [factor_5_10]; decide
      have factor_5_12 : (47 : ZMod 388181593801) ^ 7119 = 211330442639 := by
        calc
          (47 : ZMod 388181593801) ^ 7119 = (47 : ZMod 388181593801) ^ (3559 + 3559 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 3559 * (47 : ZMod 388181593801) ^ 3559) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 211330442639 := by rw [factor_5_11]; decide
      have factor_5_13 : (47 : ZMod 388181593801) ^ 14238 = 23908305808 := by
        calc
          (47 : ZMod 388181593801) ^ 14238 = (47 : ZMod 388181593801) ^ (7119 + 7119) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 7119 * (47 : ZMod 388181593801) ^ 7119 := by rw [pow_add]
          _ = 23908305808 := by rw [factor_5_12]; decide
      have factor_5_14 : (47 : ZMod 388181593801) ^ 28476 = 336111166103 := by
        calc
          (47 : ZMod 388181593801) ^ 28476 = (47 : ZMod 388181593801) ^ (14238 + 14238) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 14238 * (47 : ZMod 388181593801) ^ 14238 := by rw [pow_add]
          _ = 336111166103 := by rw [factor_5_13]; decide
      have factor_5_15 : (47 : ZMod 388181593801) ^ 56953 = 325065523231 := by
        calc
          (47 : ZMod 388181593801) ^ 56953 = (47 : ZMod 388181593801) ^ (28476 + 28476 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 28476 * (47 : ZMod 388181593801) ^ 28476) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 325065523231 := by rw [factor_5_14]; decide
      have factor_5_16 : (47 : ZMod 388181593801) ^ 113907 = 121734705425 := by
        calc
          (47 : ZMod 388181593801) ^ 113907 = (47 : ZMod 388181593801) ^ (56953 + 56953 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 56953 * (47 : ZMod 388181593801) ^ 56953) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 121734705425 := by rw [factor_5_15]; decide
      have factor_5_17 : (47 : ZMod 388181593801) ^ 227814 = 320926086496 := by
        calc
          (47 : ZMod 388181593801) ^ 227814 = (47 : ZMod 388181593801) ^ (113907 + 113907) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 113907 * (47 : ZMod 388181593801) ^ 113907 := by rw [pow_add]
          _ = 320926086496 := by rw [factor_5_16]; decide
      have factor_5_18 : (47 : ZMod 388181593801) ^ 455629 = 59558005670 := by
        calc
          (47 : ZMod 388181593801) ^ 455629 = (47 : ZMod 388181593801) ^ (227814 + 227814 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 227814 * (47 : ZMod 388181593801) ^ 227814) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 59558005670 := by rw [factor_5_17]; decide
      have factor_5_19 : (47 : ZMod 388181593801) ^ 911258 = 375926559318 := by
        calc
          (47 : ZMod 388181593801) ^ 911258 = (47 : ZMod 388181593801) ^ (455629 + 455629) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 455629 * (47 : ZMod 388181593801) ^ 455629 := by rw [pow_add]
          _ = 375926559318 := by rw [factor_5_18]; decide
      have factor_5_20 : (47 : ZMod 388181593801) ^ 1822517 = 83263297510 := by
        calc
          (47 : ZMod 388181593801) ^ 1822517 = (47 : ZMod 388181593801) ^ (911258 + 911258 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 911258 * (47 : ZMod 388181593801) ^ 911258) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 83263297510 := by rw [factor_5_19]; decide
      have factor_5_21 : (47 : ZMod 388181593801) ^ 3645034 = 255472642038 := by
        calc
          (47 : ZMod 388181593801) ^ 3645034 = (47 : ZMod 388181593801) ^ (1822517 + 1822517) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1822517 * (47 : ZMod 388181593801) ^ 1822517 := by rw [pow_add]
          _ = 255472642038 := by rw [factor_5_20]; decide
      have factor_5_22 : (47 : ZMod 388181593801) ^ 7290068 = 220539161277 := by
        calc
          (47 : ZMod 388181593801) ^ 7290068 = (47 : ZMod 388181593801) ^ (3645034 + 3645034) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3645034 * (47 : ZMod 388181593801) ^ 3645034 := by rw [pow_add]
          _ = 220539161277 := by rw [factor_5_21]; decide
      have factor_5_23 : (47 : ZMod 388181593801) ^ 14580137 = 348073521735 := by
        calc
          (47 : ZMod 388181593801) ^ 14580137 = (47 : ZMod 388181593801) ^ (7290068 + 7290068 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 7290068 * (47 : ZMod 388181593801) ^ 7290068) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 348073521735 := by rw [factor_5_22]; decide
      have factor_5_24 : (47 : ZMod 388181593801) ^ 29160275 = 169314581449 := by
        calc
          (47 : ZMod 388181593801) ^ 29160275 = (47 : ZMod 388181593801) ^ (14580137 + 14580137 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 14580137 * (47 : ZMod 388181593801) ^ 14580137) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 169314581449 := by rw [factor_5_23]; decide
      have factor_5_25 : (47 : ZMod 388181593801) ^ 58320551 = 369416219604 := by
        calc
          (47 : ZMod 388181593801) ^ 58320551 = (47 : ZMod 388181593801) ^ (29160275 + 29160275 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 29160275 * (47 : ZMod 388181593801) ^ 29160275) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 369416219604 := by rw [factor_5_24]; decide
      have factor_5_26 : (47 : ZMod 388181593801) ^ 116641103 = 134097244149 := by
        calc
          (47 : ZMod 388181593801) ^ 116641103 = (47 : ZMod 388181593801) ^ (58320551 + 58320551 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 58320551 * (47 : ZMod 388181593801) ^ 58320551) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 134097244149 := by rw [factor_5_25]; decide
      have factor_5_27 : (47 : ZMod 388181593801) ^ 233282207 = 130093996576 := by
        calc
          (47 : ZMod 388181593801) ^ 233282207 = (47 : ZMod 388181593801) ^ (116641103 + 116641103 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 116641103 * (47 : ZMod 388181593801) ^ 116641103) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 130093996576 := by rw [factor_5_26]; decide
      have factor_5_28 : (47 : ZMod 388181593801) ^ 466564415 = 130414815620 := by
        calc
          (47 : ZMod 388181593801) ^ 466564415 = (47 : ZMod 388181593801) ^ (233282207 + 233282207 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 233282207 * (47 : ZMod 388181593801) ^ 233282207) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 130414815620 := by rw [factor_5_27]; decide
      have factor_5_29 : (47 : ZMod 388181593801) ^ 933128831 = 59047354691 := by
        calc
          (47 : ZMod 388181593801) ^ 933128831 = (47 : ZMod 388181593801) ^ (466564415 + 466564415 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 466564415 * (47 : ZMod 388181593801) ^ 466564415) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 59047354691 := by rw [factor_5_28]; decide
      have factor_5_30 : (47 : ZMod 388181593801) ^ 1866257662 = 107605379067 := by
        calc
          (47 : ZMod 388181593801) ^ 1866257662 = (47 : ZMod 388181593801) ^ (933128831 + 933128831) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 933128831 * (47 : ZMod 388181593801) ^ 933128831 := by rw [pow_add]
          _ = 107605379067 := by rw [factor_5_29]; decide
      have factor_5_31 : (47 : ZMod 388181593801) ^ 3732515325 = 257338322514 := by
        calc
          (47 : ZMod 388181593801) ^ 3732515325 = (47 : ZMod 388181593801) ^ (1866257662 + 1866257662 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1866257662 * (47 : ZMod 388181593801) ^ 1866257662) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 257338322514 := by rw [factor_5_30]; decide
      have factor_5_32 : (47 : ZMod 388181593801) ^ 7465030650 = 176961731597 := by
        calc
          (47 : ZMod 388181593801) ^ 7465030650 = (47 : ZMod 388181593801) ^ (3732515325 + 3732515325) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3732515325 * (47 : ZMod 388181593801) ^ 3732515325 := by rw [pow_add]
          _ = 176961731597 := by rw [factor_5_31]; decide
      have factor_5_33 : (47 : ZMod 388181593801) ^ 14930061300 = 39685491277 := by
        calc
          (47 : ZMod 388181593801) ^ 14930061300 = (47 : ZMod 388181593801) ^ (7465030650 + 7465030650) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 7465030650 * (47 : ZMod 388181593801) ^ 7465030650 := by rw [pow_add]
          _ = 39685491277 := by rw [factor_5_32]; decide
      have factor_5_34 : (47 : ZMod 388181593801) ^ 29860122600 = 284693733693 := by
        calc
          (47 : ZMod 388181593801) ^ 29860122600 = (47 : ZMod 388181593801) ^ (14930061300 + 14930061300) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 14930061300 * (47 : ZMod 388181593801) ^ 14930061300 := by rw [pow_add]
          _ = 284693733693 := by rw [factor_5_33]; decide
      change (47 : ZMod 388181593801) ^ 29860122600 ≠ 1
      rw [factor_5_34]
      decide
    ·
      have factor_6_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_6_1 : (47 : ZMod 388181593801) ^ 2 = 2209 := by
        calc
          (47 : ZMod 388181593801) ^ 2 = (47 : ZMod 388181593801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_6_0]; decide
      have factor_6_2 : (47 : ZMod 388181593801) ^ 5 = 229345007 := by
        calc
          (47 : ZMod 388181593801) ^ 5 = (47 : ZMod 388181593801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2 * (47 : ZMod 388181593801) ^ 2) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 229345007 := by rw [factor_6_1]; decide
      have factor_6_3 : (47 : ZMod 388181593801) ^ 10 = 138094200748 := by
        calc
          (47 : ZMod 388181593801) ^ 10 = (47 : ZMod 388181593801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 5 * (47 : ZMod 388181593801) ^ 5 := by rw [pow_add]
          _ = 138094200748 := by rw [factor_6_2]; decide
      have factor_6_4 : (47 : ZMod 388181593801) ^ 21 = 96904979389 := by
        calc
          (47 : ZMod 388181593801) ^ 21 = (47 : ZMod 388181593801) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 10 * (47 : ZMod 388181593801) ^ 10) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 96904979389 := by rw [factor_6_3]; decide
      have factor_6_5 : (47 : ZMod 388181593801) ^ 42 = 192625453645 := by
        calc
          (47 : ZMod 388181593801) ^ 42 = (47 : ZMod 388181593801) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 21 * (47 : ZMod 388181593801) ^ 21 := by rw [pow_add]
          _ = 192625453645 := by rw [factor_6_4]; decide
      have factor_6_6 : (47 : ZMod 388181593801) ^ 85 = 154450296393 := by
        calc
          (47 : ZMod 388181593801) ^ 85 = (47 : ZMod 388181593801) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 42 * (47 : ZMod 388181593801) ^ 42) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 154450296393 := by rw [factor_6_5]; decide
      have factor_6_7 : (47 : ZMod 388181593801) ^ 170 = 79321864259 := by
        calc
          (47 : ZMod 388181593801) ^ 170 = (47 : ZMod 388181593801) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 85 * (47 : ZMod 388181593801) ^ 85 := by rw [pow_add]
          _ = 79321864259 := by rw [factor_6_6]; decide
      have factor_6_8 : (47 : ZMod 388181593801) ^ 340 = 26310119226 := by
        calc
          (47 : ZMod 388181593801) ^ 340 = (47 : ZMod 388181593801) ^ (170 + 170) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 170 * (47 : ZMod 388181593801) ^ 170 := by rw [pow_add]
          _ = 26310119226 := by rw [factor_6_7]; decide
      have factor_6_9 : (47 : ZMod 388181593801) ^ 680 = 236556005197 := by
        calc
          (47 : ZMod 388181593801) ^ 680 = (47 : ZMod 388181593801) ^ (340 + 340) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 340 * (47 : ZMod 388181593801) ^ 340 := by rw [pow_add]
          _ = 236556005197 := by rw [factor_6_8]; decide
      have factor_6_10 : (47 : ZMod 388181593801) ^ 1361 = 345972786890 := by
        calc
          (47 : ZMod 388181593801) ^ 1361 = (47 : ZMod 388181593801) ^ (680 + 680 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 680 * (47 : ZMod 388181593801) ^ 680) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 345972786890 := by rw [factor_6_9]; decide
      have factor_6_11 : (47 : ZMod 388181593801) ^ 2722 = 249693620808 := by
        calc
          (47 : ZMod 388181593801) ^ 2722 = (47 : ZMod 388181593801) ^ (1361 + 1361) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1361 * (47 : ZMod 388181593801) ^ 1361 := by rw [pow_add]
          _ = 249693620808 := by rw [factor_6_10]; decide
      have factor_6_12 : (47 : ZMod 388181593801) ^ 5444 = 201611975069 := by
        calc
          (47 : ZMod 388181593801) ^ 5444 = (47 : ZMod 388181593801) ^ (2722 + 2722) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2722 * (47 : ZMod 388181593801) ^ 2722 := by rw [pow_add]
          _ = 201611975069 := by rw [factor_6_11]; decide
      have factor_6_13 : (47 : ZMod 388181593801) ^ 10888 = 285195406420 := by
        calc
          (47 : ZMod 388181593801) ^ 10888 = (47 : ZMod 388181593801) ^ (5444 + 5444) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 5444 * (47 : ZMod 388181593801) ^ 5444 := by rw [pow_add]
          _ = 285195406420 := by rw [factor_6_12]; decide
      have factor_6_14 : (47 : ZMod 388181593801) ^ 21776 = 235876711565 := by
        calc
          (47 : ZMod 388181593801) ^ 21776 = (47 : ZMod 388181593801) ^ (10888 + 10888) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 10888 * (47 : ZMod 388181593801) ^ 10888 := by rw [pow_add]
          _ = 235876711565 := by rw [factor_6_13]; decide
      have factor_6_15 : (47 : ZMod 388181593801) ^ 43552 = 323020159009 := by
        calc
          (47 : ZMod 388181593801) ^ 43552 = (47 : ZMod 388181593801) ^ (21776 + 21776) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 21776 * (47 : ZMod 388181593801) ^ 21776 := by rw [pow_add]
          _ = 323020159009 := by rw [factor_6_14]; decide
      have factor_6_16 : (47 : ZMod 388181593801) ^ 87105 = 3406052791 := by
        calc
          (47 : ZMod 388181593801) ^ 87105 = (47 : ZMod 388181593801) ^ (43552 + 43552 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 43552 * (47 : ZMod 388181593801) ^ 43552) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 3406052791 := by rw [factor_6_15]; decide
      have factor_6_17 : (47 : ZMod 388181593801) ^ 174211 = 337987944947 := by
        calc
          (47 : ZMod 388181593801) ^ 174211 = (47 : ZMod 388181593801) ^ (87105 + 87105 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 87105 * (47 : ZMod 388181593801) ^ 87105) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 337987944947 := by rw [factor_6_16]; decide
      have factor_6_18 : (47 : ZMod 388181593801) ^ 348422 = 216552589209 := by
        calc
          (47 : ZMod 388181593801) ^ 348422 = (47 : ZMod 388181593801) ^ (174211 + 174211) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 174211 * (47 : ZMod 388181593801) ^ 174211 := by rw [pow_add]
          _ = 216552589209 := by rw [factor_6_17]; decide
      have factor_6_19 : (47 : ZMod 388181593801) ^ 696844 = 196298612731 := by
        calc
          (47 : ZMod 388181593801) ^ 696844 = (47 : ZMod 388181593801) ^ (348422 + 348422) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 348422 * (47 : ZMod 388181593801) ^ 348422 := by rw [pow_add]
          _ = 196298612731 := by rw [factor_6_18]; decide
      have factor_6_20 : (47 : ZMod 388181593801) ^ 1393689 = 37654924177 := by
        calc
          (47 : ZMod 388181593801) ^ 1393689 = (47 : ZMod 388181593801) ^ (696844 + 696844 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 696844 * (47 : ZMod 388181593801) ^ 696844) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 37654924177 := by rw [factor_6_19]; decide
      have factor_6_21 : (47 : ZMod 388181593801) ^ 2787379 = 28520782165 := by
        calc
          (47 : ZMod 388181593801) ^ 2787379 = (47 : ZMod 388181593801) ^ (1393689 + 1393689 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1393689 * (47 : ZMod 388181593801) ^ 1393689) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 28520782165 := by rw [factor_6_20]; decide
      have factor_6_22 : (47 : ZMod 388181593801) ^ 5574758 = 266394335975 := by
        calc
          (47 : ZMod 388181593801) ^ 5574758 = (47 : ZMod 388181593801) ^ (2787379 + 2787379) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2787379 * (47 : ZMod 388181593801) ^ 2787379 := by rw [pow_add]
          _ = 266394335975 := by rw [factor_6_21]; decide
      have factor_6_23 : (47 : ZMod 388181593801) ^ 11149517 = 316258403201 := by
        calc
          (47 : ZMod 388181593801) ^ 11149517 = (47 : ZMod 388181593801) ^ (5574758 + 5574758 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 5574758 * (47 : ZMod 388181593801) ^ 5574758) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 316258403201 := by rw [factor_6_22]; decide
      have factor_6_24 : (47 : ZMod 388181593801) ^ 22299034 = 175254442784 := by
        calc
          (47 : ZMod 388181593801) ^ 22299034 = (47 : ZMod 388181593801) ^ (11149517 + 11149517) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 11149517 * (47 : ZMod 388181593801) ^ 11149517 := by rw [pow_add]
          _ = 175254442784 := by rw [factor_6_23]; decide
      have factor_6_25 : (47 : ZMod 388181593801) ^ 44598069 = 274272368733 := by
        calc
          (47 : ZMod 388181593801) ^ 44598069 = (47 : ZMod 388181593801) ^ (22299034 + 22299034 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 22299034 * (47 : ZMod 388181593801) ^ 22299034) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 274272368733 := by rw [factor_6_24]; decide
      have factor_6_26 : (47 : ZMod 388181593801) ^ 89196138 = 157779044353 := by
        calc
          (47 : ZMod 388181593801) ^ 89196138 = (47 : ZMod 388181593801) ^ (44598069 + 44598069) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 44598069 * (47 : ZMod 388181593801) ^ 44598069 := by rw [pow_add]
          _ = 157779044353 := by rw [factor_6_25]; decide
      have factor_6_27 : (47 : ZMod 388181593801) ^ 178392276 = 201262477794 := by
        calc
          (47 : ZMod 388181593801) ^ 178392276 = (47 : ZMod 388181593801) ^ (89196138 + 89196138) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 89196138 * (47 : ZMod 388181593801) ^ 89196138 := by rw [pow_add]
          _ = 201262477794 := by rw [factor_6_26]; decide
      have factor_6_28 : (47 : ZMod 388181593801) ^ 356784553 = 194106794793 := by
        calc
          (47 : ZMod 388181593801) ^ 356784553 = (47 : ZMod 388181593801) ^ (178392276 + 178392276 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 178392276 * (47 : ZMod 388181593801) ^ 178392276) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 194106794793 := by rw [factor_6_27]; decide
      have factor_6_29 : (47 : ZMod 388181593801) ^ 713569106 = 23848728247 := by
        calc
          (47 : ZMod 388181593801) ^ 713569106 = (47 : ZMod 388181593801) ^ (356784553 + 356784553) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 356784553 * (47 : ZMod 388181593801) ^ 356784553 := by rw [pow_add]
          _ = 23848728247 := by rw [factor_6_28]; decide
      have factor_6_30 : (47 : ZMod 388181593801) ^ 1427138212 = 367334827530 := by
        calc
          (47 : ZMod 388181593801) ^ 1427138212 = (47 : ZMod 388181593801) ^ (713569106 + 713569106) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 713569106 * (47 : ZMod 388181593801) ^ 713569106 := by rw [pow_add]
          _ = 367334827530 := by rw [factor_6_29]; decide
      have factor_6_31 : (47 : ZMod 388181593801) ^ 2854276425 = 137157166373 := by
        calc
          (47 : ZMod 388181593801) ^ 2854276425 = (47 : ZMod 388181593801) ^ (1427138212 + 1427138212 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1427138212 * (47 : ZMod 388181593801) ^ 1427138212) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 137157166373 := by rw [factor_6_30]; decide
      have factor_6_32 : (47 : ZMod 388181593801) ^ 5708552850 = 345172410581 := by
        calc
          (47 : ZMod 388181593801) ^ 5708552850 = (47 : ZMod 388181593801) ^ (2854276425 + 2854276425) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2854276425 * (47 : ZMod 388181593801) ^ 2854276425 := by rw [pow_add]
          _ = 345172410581 := by rw [factor_6_31]; decide
      have factor_6_33 : (47 : ZMod 388181593801) ^ 11417105700 = 170195707876 := by
        calc
          (47 : ZMod 388181593801) ^ 11417105700 = (47 : ZMod 388181593801) ^ (5708552850 + 5708552850) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 5708552850 * (47 : ZMod 388181593801) ^ 5708552850 := by rw [pow_add]
          _ = 170195707876 := by rw [factor_6_32]; decide
      have factor_6_34 : (47 : ZMod 388181593801) ^ 22834211400 = 198341260596 := by
        calc
          (47 : ZMod 388181593801) ^ 22834211400 = (47 : ZMod 388181593801) ^ (11417105700 + 11417105700) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 11417105700 * (47 : ZMod 388181593801) ^ 11417105700 := by rw [pow_add]
          _ = 198341260596 := by rw [factor_6_33]; decide
      change (47 : ZMod 388181593801) ^ 22834211400 ≠ 1
      rw [factor_6_34]
      decide
    ·
      have factor_7_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_7_1 : (47 : ZMod 388181593801) ^ 2 = 2209 := by
        calc
          (47 : ZMod 388181593801) ^ 2 = (47 : ZMod 388181593801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_7_0]; decide
      have factor_7_2 : (47 : ZMod 388181593801) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 388181593801) ^ 4 = (47 : ZMod 388181593801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2 * (47 : ZMod 388181593801) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_7_1]; decide
      have factor_7_3 : (47 : ZMod 388181593801) ^ 9 = 2938174484 := by
        calc
          (47 : ZMod 388181593801) ^ 9 = (47 : ZMod 388181593801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 4 * (47 : ZMod 388181593801) ^ 4) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 2938174484 := by rw [factor_7_2]; decide
      have factor_7_4 : (47 : ZMod 388181593801) ^ 19 = 211795258266 := by
        calc
          (47 : ZMod 388181593801) ^ 19 = (47 : ZMod 388181593801) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 9 * (47 : ZMod 388181593801) ^ 9) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 211795258266 := by rw [factor_7_3]; decide
      have factor_7_5 : (47 : ZMod 388181593801) ^ 38 = 326108929714 := by
        calc
          (47 : ZMod 388181593801) ^ 38 = (47 : ZMod 388181593801) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 19 * (47 : ZMod 388181593801) ^ 19 := by rw [pow_add]
          _ = 326108929714 := by rw [factor_7_4]; decide
      have factor_7_6 : (47 : ZMod 388181593801) ^ 76 = 30989068051 := by
        calc
          (47 : ZMod 388181593801) ^ 76 = (47 : ZMod 388181593801) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 38 * (47 : ZMod 388181593801) ^ 38 := by rw [pow_add]
          _ = 30989068051 := by rw [factor_7_5]; decide
      have factor_7_7 : (47 : ZMod 388181593801) ^ 152 = 126971740075 := by
        calc
          (47 : ZMod 388181593801) ^ 152 = (47 : ZMod 388181593801) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 76 * (47 : ZMod 388181593801) ^ 76 := by rw [pow_add]
          _ = 126971740075 := by rw [factor_7_6]; decide
      have factor_7_8 : (47 : ZMod 388181593801) ^ 304 = 18456734054 := by
        calc
          (47 : ZMod 388181593801) ^ 304 = (47 : ZMod 388181593801) ^ (152 + 152) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 152 * (47 : ZMod 388181593801) ^ 152 := by rw [pow_add]
          _ = 18456734054 := by rw [factor_7_7]; decide
      have factor_7_9 : (47 : ZMod 388181593801) ^ 608 = 332239238658 := by
        calc
          (47 : ZMod 388181593801) ^ 608 = (47 : ZMod 388181593801) ^ (304 + 304) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 304 * (47 : ZMod 388181593801) ^ 304 := by rw [pow_add]
          _ = 332239238658 := by rw [factor_7_8]; decide
      have factor_7_10 : (47 : ZMod 388181593801) ^ 1217 = 321428687352 := by
        calc
          (47 : ZMod 388181593801) ^ 1217 = (47 : ZMod 388181593801) ^ (608 + 608 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 608 * (47 : ZMod 388181593801) ^ 608) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 321428687352 := by rw [factor_7_9]; decide
      have factor_7_11 : (47 : ZMod 388181593801) ^ 2435 = 33814042662 := by
        calc
          (47 : ZMod 388181593801) ^ 2435 = (47 : ZMod 388181593801) ^ (1217 + 1217 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1217 * (47 : ZMod 388181593801) ^ 1217) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 33814042662 := by rw [factor_7_10]; decide
      have factor_7_12 : (47 : ZMod 388181593801) ^ 4871 = 217967458233 := by
        calc
          (47 : ZMod 388181593801) ^ 4871 = (47 : ZMod 388181593801) ^ (2435 + 2435 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2435 * (47 : ZMod 388181593801) ^ 2435) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 217967458233 := by rw [factor_7_11]; decide
      have factor_7_13 : (47 : ZMod 388181593801) ^ 9742 = 361244201765 := by
        calc
          (47 : ZMod 388181593801) ^ 9742 = (47 : ZMod 388181593801) ^ (4871 + 4871) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 4871 * (47 : ZMod 388181593801) ^ 4871 := by rw [pow_add]
          _ = 361244201765 := by rw [factor_7_12]; decide
      have factor_7_14 : (47 : ZMod 388181593801) ^ 19484 = 173466051168 := by
        calc
          (47 : ZMod 388181593801) ^ 19484 = (47 : ZMod 388181593801) ^ (9742 + 9742) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 9742 * (47 : ZMod 388181593801) ^ 9742 := by rw [pow_add]
          _ = 173466051168 := by rw [factor_7_13]; decide
      have factor_7_15 : (47 : ZMod 388181593801) ^ 38968 = 303216163824 := by
        calc
          (47 : ZMod 388181593801) ^ 38968 = (47 : ZMod 388181593801) ^ (19484 + 19484) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 19484 * (47 : ZMod 388181593801) ^ 19484 := by rw [pow_add]
          _ = 303216163824 := by rw [factor_7_14]; decide
      have factor_7_16 : (47 : ZMod 388181593801) ^ 77936 = 135383268288 := by
        calc
          (47 : ZMod 388181593801) ^ 77936 = (47 : ZMod 388181593801) ^ (38968 + 38968) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 38968 * (47 : ZMod 388181593801) ^ 38968 := by rw [pow_add]
          _ = 135383268288 := by rw [factor_7_15]; decide
      have factor_7_17 : (47 : ZMod 388181593801) ^ 155873 = 18404032715 := by
        calc
          (47 : ZMod 388181593801) ^ 155873 = (47 : ZMod 388181593801) ^ (77936 + 77936 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 77936 * (47 : ZMod 388181593801) ^ 77936) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 18404032715 := by rw [factor_7_16]; decide
      have factor_7_18 : (47 : ZMod 388181593801) ^ 311746 = 264966427556 := by
        calc
          (47 : ZMod 388181593801) ^ 311746 = (47 : ZMod 388181593801) ^ (155873 + 155873) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 155873 * (47 : ZMod 388181593801) ^ 155873 := by rw [pow_add]
          _ = 264966427556 := by rw [factor_7_17]; decide
      have factor_7_19 : (47 : ZMod 388181593801) ^ 623492 = 304081960331 := by
        calc
          (47 : ZMod 388181593801) ^ 623492 = (47 : ZMod 388181593801) ^ (311746 + 311746) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 311746 * (47 : ZMod 388181593801) ^ 311746 := by rw [pow_add]
          _ = 304081960331 := by rw [factor_7_18]; decide
      have factor_7_20 : (47 : ZMod 388181593801) ^ 1246985 = 280284487936 := by
        calc
          (47 : ZMod 388181593801) ^ 1246985 = (47 : ZMod 388181593801) ^ (623492 + 623492 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 623492 * (47 : ZMod 388181593801) ^ 623492) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 280284487936 := by rw [factor_7_19]; decide
      have factor_7_21 : (47 : ZMod 388181593801) ^ 2493970 = 204243159482 := by
        calc
          (47 : ZMod 388181593801) ^ 2493970 = (47 : ZMod 388181593801) ^ (1246985 + 1246985) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1246985 * (47 : ZMod 388181593801) ^ 1246985 := by rw [pow_add]
          _ = 204243159482 := by rw [factor_7_20]; decide
      have factor_7_22 : (47 : ZMod 388181593801) ^ 4987941 = 122454706105 := by
        calc
          (47 : ZMod 388181593801) ^ 4987941 = (47 : ZMod 388181593801) ^ (2493970 + 2493970 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2493970 * (47 : ZMod 388181593801) ^ 2493970) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 122454706105 := by rw [factor_7_21]; decide
      have factor_7_23 : (47 : ZMod 388181593801) ^ 9975883 = 126920673049 := by
        calc
          (47 : ZMod 388181593801) ^ 9975883 = (47 : ZMod 388181593801) ^ (4987941 + 4987941 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 4987941 * (47 : ZMod 388181593801) ^ 4987941) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 126920673049 := by rw [factor_7_22]; decide
      have factor_7_24 : (47 : ZMod 388181593801) ^ 19951767 = 379932124722 := by
        calc
          (47 : ZMod 388181593801) ^ 19951767 = (47 : ZMod 388181593801) ^ (9975883 + 9975883 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 9975883 * (47 : ZMod 388181593801) ^ 9975883) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 379932124722 := by rw [factor_7_23]; decide
      have factor_7_25 : (47 : ZMod 388181593801) ^ 39903535 = 271962077592 := by
        calc
          (47 : ZMod 388181593801) ^ 39903535 = (47 : ZMod 388181593801) ^ (19951767 + 19951767 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 19951767 * (47 : ZMod 388181593801) ^ 19951767) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 271962077592 := by rw [factor_7_24]; decide
      have factor_7_26 : (47 : ZMod 388181593801) ^ 79807071 = 90720694561 := by
        calc
          (47 : ZMod 388181593801) ^ 79807071 = (47 : ZMod 388181593801) ^ (39903535 + 39903535 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 39903535 * (47 : ZMod 388181593801) ^ 39903535) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 90720694561 := by rw [factor_7_25]; decide
      have factor_7_27 : (47 : ZMod 388181593801) ^ 159614142 = 94740738656 := by
        calc
          (47 : ZMod 388181593801) ^ 159614142 = (47 : ZMod 388181593801) ^ (79807071 + 79807071) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 79807071 * (47 : ZMod 388181593801) ^ 79807071 := by rw [pow_add]
          _ = 94740738656 := by rw [factor_7_26]; decide
      have factor_7_28 : (47 : ZMod 388181593801) ^ 319228284 = 19973508303 := by
        calc
          (47 : ZMod 388181593801) ^ 319228284 = (47 : ZMod 388181593801) ^ (159614142 + 159614142) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 159614142 * (47 : ZMod 388181593801) ^ 159614142 := by rw [pow_add]
          _ = 19973508303 := by rw [factor_7_27]; decide
      have factor_7_29 : (47 : ZMod 388181593801) ^ 638456568 = 111022188866 := by
        calc
          (47 : ZMod 388181593801) ^ 638456568 = (47 : ZMod 388181593801) ^ (319228284 + 319228284) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 319228284 * (47 : ZMod 388181593801) ^ 319228284 := by rw [pow_add]
          _ = 111022188866 := by rw [factor_7_28]; decide
      have factor_7_30 : (47 : ZMod 388181593801) ^ 1276913137 = 180486591232 := by
        calc
          (47 : ZMod 388181593801) ^ 1276913137 = (47 : ZMod 388181593801) ^ (638456568 + 638456568 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 638456568 * (47 : ZMod 388181593801) ^ 638456568) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 180486591232 := by rw [factor_7_29]; decide
      have factor_7_31 : (47 : ZMod 388181593801) ^ 2553826275 = 386774048023 := by
        calc
          (47 : ZMod 388181593801) ^ 2553826275 = (47 : ZMod 388181593801) ^ (1276913137 + 1276913137 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1276913137 * (47 : ZMod 388181593801) ^ 1276913137) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 386774048023 := by rw [factor_7_30]; decide
      have factor_7_32 : (47 : ZMod 388181593801) ^ 5107652550 = 202351021126 := by
        calc
          (47 : ZMod 388181593801) ^ 5107652550 = (47 : ZMod 388181593801) ^ (2553826275 + 2553826275) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2553826275 * (47 : ZMod 388181593801) ^ 2553826275 := by rw [pow_add]
          _ = 202351021126 := by rw [factor_7_31]; decide
      have factor_7_33 : (47 : ZMod 388181593801) ^ 10215305100 = 55542292989 := by
        calc
          (47 : ZMod 388181593801) ^ 10215305100 = (47 : ZMod 388181593801) ^ (5107652550 + 5107652550) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 5107652550 * (47 : ZMod 388181593801) ^ 5107652550 := by rw [pow_add]
          _ = 55542292989 := by rw [factor_7_32]; decide
      have factor_7_34 : (47 : ZMod 388181593801) ^ 20430610200 = 10024446046 := by
        calc
          (47 : ZMod 388181593801) ^ 20430610200 = (47 : ZMod 388181593801) ^ (10215305100 + 10215305100) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 10215305100 * (47 : ZMod 388181593801) ^ 10215305100 := by rw [pow_add]
          _ = 10024446046 := by rw [factor_7_33]; decide
      change (47 : ZMod 388181593801) ^ 20430610200 ≠ 1
      rw [factor_7_34]
      decide
    ·
      have factor_8_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_8_1 : (47 : ZMod 388181593801) ^ 3 = 103823 := by
        calc
          (47 : ZMod 388181593801) ^ 3 = (47 : ZMod 388181593801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_8_0]; decide
      have factor_8_2 : (47 : ZMod 388181593801) ^ 7 = 118441526662 := by
        calc
          (47 : ZMod 388181593801) ^ 7 = (47 : ZMod 388181593801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 3 * (47 : ZMod 388181593801) ^ 3) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 118441526662 := by rw [factor_8_1]; decide
      have factor_8_3 : (47 : ZMod 388181593801) ^ 15 = 138684756178 := by
        calc
          (47 : ZMod 388181593801) ^ 15 = (47 : ZMod 388181593801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 7 * (47 : ZMod 388181593801) ^ 7) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 138684756178 := by rw [factor_8_2]; decide
      have factor_8_4 : (47 : ZMod 388181593801) ^ 31 = 326454580760 := by
        calc
          (47 : ZMod 388181593801) ^ 31 = (47 : ZMod 388181593801) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 15 * (47 : ZMod 388181593801) ^ 15) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 326454580760 := by rw [factor_8_3]; decide
      have factor_8_5 : (47 : ZMod 388181593801) ^ 62 = 101537396510 := by
        calc
          (47 : ZMod 388181593801) ^ 62 = (47 : ZMod 388181593801) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 31 * (47 : ZMod 388181593801) ^ 31 := by rw [pow_add]
          _ = 101537396510 := by rw [factor_8_4]; decide
      have factor_8_6 : (47 : ZMod 388181593801) ^ 125 = 23991721831 := by
        calc
          (47 : ZMod 388181593801) ^ 125 = (47 : ZMod 388181593801) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 62 * (47 : ZMod 388181593801) ^ 62) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 23991721831 := by rw [factor_8_5]; decide
      have factor_8_7 : (47 : ZMod 388181593801) ^ 251 = 293770428678 := by
        calc
          (47 : ZMod 388181593801) ^ 251 = (47 : ZMod 388181593801) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 125 * (47 : ZMod 388181593801) ^ 125) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 293770428678 := by rw [factor_8_6]; decide
      have factor_8_8 : (47 : ZMod 388181593801) ^ 502 = 175557792049 := by
        calc
          (47 : ZMod 388181593801) ^ 502 = (47 : ZMod 388181593801) ^ (251 + 251) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 251 * (47 : ZMod 388181593801) ^ 251 := by rw [pow_add]
          _ = 175557792049 := by rw [factor_8_7]; decide
      have factor_8_9 : (47 : ZMod 388181593801) ^ 1005 = 305842544845 := by
        calc
          (47 : ZMod 388181593801) ^ 1005 = (47 : ZMod 388181593801) ^ (502 + 502 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 502 * (47 : ZMod 388181593801) ^ 502) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 305842544845 := by rw [factor_8_8]; decide
      have factor_8_10 : (47 : ZMod 388181593801) ^ 2011 = 3282041017 := by
        calc
          (47 : ZMod 388181593801) ^ 2011 = (47 : ZMod 388181593801) ^ (1005 + 1005 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1005 * (47 : ZMod 388181593801) ^ 1005) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 3282041017 := by rw [factor_8_9]; decide
      have factor_8_11 : (47 : ZMod 388181593801) ^ 4023 = 37344050567 := by
        calc
          (47 : ZMod 388181593801) ^ 4023 = (47 : ZMod 388181593801) ^ (2011 + 2011 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2011 * (47 : ZMod 388181593801) ^ 2011) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 37344050567 := by rw [factor_8_10]; decide
      have factor_8_12 : (47 : ZMod 388181593801) ^ 8047 = 336318429640 := by
        calc
          (47 : ZMod 388181593801) ^ 8047 = (47 : ZMod 388181593801) ^ (4023 + 4023 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 4023 * (47 : ZMod 388181593801) ^ 4023) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 336318429640 := by rw [factor_8_11]; decide
      have factor_8_13 : (47 : ZMod 388181593801) ^ 16095 = 20556305155 := by
        calc
          (47 : ZMod 388181593801) ^ 16095 = (47 : ZMod 388181593801) ^ (8047 + 8047 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 8047 * (47 : ZMod 388181593801) ^ 8047) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 20556305155 := by rw [factor_8_12]; decide
      have factor_8_14 : (47 : ZMod 388181593801) ^ 32191 = 11180389533 := by
        calc
          (47 : ZMod 388181593801) ^ 32191 = (47 : ZMod 388181593801) ^ (16095 + 16095 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 16095 * (47 : ZMod 388181593801) ^ 16095) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 11180389533 := by rw [factor_8_13]; decide
      have factor_8_15 : (47 : ZMod 388181593801) ^ 64382 = 164984742392 := by
        calc
          (47 : ZMod 388181593801) ^ 64382 = (47 : ZMod 388181593801) ^ (32191 + 32191) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 32191 * (47 : ZMod 388181593801) ^ 32191 := by rw [pow_add]
          _ = 164984742392 := by rw [factor_8_14]; decide
      have factor_8_16 : (47 : ZMod 388181593801) ^ 128764 = 125931110864 := by
        calc
          (47 : ZMod 388181593801) ^ 128764 = (47 : ZMod 388181593801) ^ (64382 + 64382) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 64382 * (47 : ZMod 388181593801) ^ 64382 := by rw [pow_add]
          _ = 125931110864 := by rw [factor_8_15]; decide
      have factor_8_17 : (47 : ZMod 388181593801) ^ 257529 = 229880906585 := by
        calc
          (47 : ZMod 388181593801) ^ 257529 = (47 : ZMod 388181593801) ^ (128764 + 128764 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 128764 * (47 : ZMod 388181593801) ^ 128764) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 229880906585 := by rw [factor_8_16]; decide
      have factor_8_18 : (47 : ZMod 388181593801) ^ 515059 = 248399775755 := by
        calc
          (47 : ZMod 388181593801) ^ 515059 = (47 : ZMod 388181593801) ^ (257529 + 257529 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 257529 * (47 : ZMod 388181593801) ^ 257529) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 248399775755 := by rw [factor_8_17]; decide
      have factor_8_19 : (47 : ZMod 388181593801) ^ 1030118 = 26086599858 := by
        calc
          (47 : ZMod 388181593801) ^ 1030118 = (47 : ZMod 388181593801) ^ (515059 + 515059) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 515059 * (47 : ZMod 388181593801) ^ 515059 := by rw [pow_add]
          _ = 26086599858 := by rw [factor_8_18]; decide
      have factor_8_20 : (47 : ZMod 388181593801) ^ 2060236 = 99081910 := by
        calc
          (47 : ZMod 388181593801) ^ 2060236 = (47 : ZMod 388181593801) ^ (1030118 + 1030118) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1030118 * (47 : ZMod 388181593801) ^ 1030118 := by rw [pow_add]
          _ = 99081910 := by rw [factor_8_19]; decide
      have factor_8_21 : (47 : ZMod 388181593801) ^ 4120473 = 235594258657 := by
        calc
          (47 : ZMod 388181593801) ^ 4120473 = (47 : ZMod 388181593801) ^ (2060236 + 2060236 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 2060236 * (47 : ZMod 388181593801) ^ 2060236) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 235594258657 := by rw [factor_8_20]; decide
      have factor_8_22 : (47 : ZMod 388181593801) ^ 8240947 = 168747703067 := by
        calc
          (47 : ZMod 388181593801) ^ 8240947 = (47 : ZMod 388181593801) ^ (4120473 + 4120473 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 4120473 * (47 : ZMod 388181593801) ^ 4120473) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 168747703067 := by rw [factor_8_21]; decide
      have factor_8_23 : (47 : ZMod 388181593801) ^ 16481895 = 188873686257 := by
        calc
          (47 : ZMod 388181593801) ^ 16481895 = (47 : ZMod 388181593801) ^ (8240947 + 8240947 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 8240947 * (47 : ZMod 388181593801) ^ 8240947) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 188873686257 := by rw [factor_8_22]; decide
      have factor_8_24 : (47 : ZMod 388181593801) ^ 32963790 = 43360697347 := by
        calc
          (47 : ZMod 388181593801) ^ 32963790 = (47 : ZMod 388181593801) ^ (16481895 + 16481895) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 16481895 * (47 : ZMod 388181593801) ^ 16481895 := by rw [pow_add]
          _ = 43360697347 := by rw [factor_8_23]; decide
      have factor_8_25 : (47 : ZMod 388181593801) ^ 65927580 = 55941164266 := by
        calc
          (47 : ZMod 388181593801) ^ 65927580 = (47 : ZMod 388181593801) ^ (32963790 + 32963790) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 32963790 * (47 : ZMod 388181593801) ^ 32963790 := by rw [pow_add]
          _ = 55941164266 := by rw [factor_8_24]; decide
      have factor_8_26 : (47 : ZMod 388181593801) ^ 131855160 = 21484577410 := by
        calc
          (47 : ZMod 388181593801) ^ 131855160 = (47 : ZMod 388181593801) ^ (65927580 + 65927580) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 65927580 * (47 : ZMod 388181593801) ^ 65927580 := by rw [pow_add]
          _ = 21484577410 := by rw [factor_8_25]; decide
      have factor_8_27 : (47 : ZMod 388181593801) ^ 263710321 = 303084535146 := by
        calc
          (47 : ZMod 388181593801) ^ 263710321 = (47 : ZMod 388181593801) ^ (131855160 + 131855160 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 131855160 * (47 : ZMod 388181593801) ^ 131855160) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 303084535146 := by rw [factor_8_26]; decide
      have factor_8_28 : (47 : ZMod 388181593801) ^ 527420643 = 149016765302 := by
        calc
          (47 : ZMod 388181593801) ^ 527420643 = (47 : ZMod 388181593801) ^ (263710321 + 263710321 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 263710321 * (47 : ZMod 388181593801) ^ 263710321) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 149016765302 := by rw [factor_8_27]; decide
      have factor_8_29 : (47 : ZMod 388181593801) ^ 1054841287 = 247435994918 := by
        calc
          (47 : ZMod 388181593801) ^ 1054841287 = (47 : ZMod 388181593801) ^ (527420643 + 527420643 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 527420643 * (47 : ZMod 388181593801) ^ 527420643) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 247435994918 := by rw [factor_8_28]; decide
      have factor_8_30 : (47 : ZMod 388181593801) ^ 2109682575 = 51608421871 := by
        calc
          (47 : ZMod 388181593801) ^ 2109682575 = (47 : ZMod 388181593801) ^ (1054841287 + 1054841287 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1054841287 * (47 : ZMod 388181593801) ^ 1054841287) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 51608421871 := by rw [factor_8_29]; decide
      have factor_8_31 : (47 : ZMod 388181593801) ^ 4219365150 = 295820087034 := by
        calc
          (47 : ZMod 388181593801) ^ 4219365150 = (47 : ZMod 388181593801) ^ (2109682575 + 2109682575) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 2109682575 * (47 : ZMod 388181593801) ^ 2109682575 := by rw [pow_add]
          _ = 295820087034 := by rw [factor_8_30]; decide
      have factor_8_32 : (47 : ZMod 388181593801) ^ 8438730300 = 383840960365 := by
        calc
          (47 : ZMod 388181593801) ^ 8438730300 = (47 : ZMod 388181593801) ^ (4219365150 + 4219365150) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 4219365150 * (47 : ZMod 388181593801) ^ 4219365150 := by rw [pow_add]
          _ = 383840960365 := by rw [factor_8_31]; decide
      have factor_8_33 : (47 : ZMod 388181593801) ^ 16877460600 = 32815288480 := by
        calc
          (47 : ZMod 388181593801) ^ 16877460600 = (47 : ZMod 388181593801) ^ (8438730300 + 8438730300) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 8438730300 * (47 : ZMod 388181593801) ^ 8438730300 := by rw [pow_add]
          _ = 32815288480 := by rw [factor_8_32]; decide
      change (47 : ZMod 388181593801) ^ 16877460600 ≠ 1
      rw [factor_8_33]
      decide
    ·
      have factor_9_0 : (47 : ZMod 388181593801) ^ 1 = 47 := by norm_num
      have factor_9_1 : (47 : ZMod 388181593801) ^ 3 = 103823 := by
        calc
          (47 : ZMod 388181593801) ^ 3 = (47 : ZMod 388181593801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1 * (47 : ZMod 388181593801) ^ 1) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_9_0]; decide
      have factor_9_2 : (47 : ZMod 388181593801) ^ 6 = 10779215329 := by
        calc
          (47 : ZMod 388181593801) ^ 6 = (47 : ZMod 388181593801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3 * (47 : ZMod 388181593801) ^ 3 := by rw [pow_add]
          _ = 10779215329 := by rw [factor_9_1]; decide
      have factor_9_3 : (47 : ZMod 388181593801) ^ 12 = 327538318547 := by
        calc
          (47 : ZMod 388181593801) ^ 12 = (47 : ZMod 388181593801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 6 * (47 : ZMod 388181593801) ^ 6 := by rw [pow_add]
          _ = 327538318547 := by rw [factor_9_2]; decide
      have factor_9_4 : (47 : ZMod 388181593801) ^ 24 = 75126969829 := by
        calc
          (47 : ZMod 388181593801) ^ 24 = (47 : ZMod 388181593801) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 12 * (47 : ZMod 388181593801) ^ 12 := by rw [pow_add]
          _ = 75126969829 := by rw [factor_9_3]; decide
      have factor_9_5 : (47 : ZMod 388181593801) ^ 49 = 197728387928 := by
        calc
          (47 : ZMod 388181593801) ^ 49 = (47 : ZMod 388181593801) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 24 * (47 : ZMod 388181593801) ^ 24) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 197728387928 := by rw [factor_9_4]; decide
      have factor_9_6 : (47 : ZMod 388181593801) ^ 99 = 262157217363 := by
        calc
          (47 : ZMod 388181593801) ^ 99 = (47 : ZMod 388181593801) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 49 * (47 : ZMod 388181593801) ^ 49) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 262157217363 := by rw [factor_9_5]; decide
      have factor_9_7 : (47 : ZMod 388181593801) ^ 199 = 95993992681 := by
        calc
          (47 : ZMod 388181593801) ^ 199 = (47 : ZMod 388181593801) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 99 * (47 : ZMod 388181593801) ^ 99) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 95993992681 := by rw [factor_9_6]; decide
      have factor_9_8 : (47 : ZMod 388181593801) ^ 398 = 229064191858 := by
        calc
          (47 : ZMod 388181593801) ^ 398 = (47 : ZMod 388181593801) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 199 * (47 : ZMod 388181593801) ^ 199 := by rw [pow_add]
          _ = 229064191858 := by rw [factor_9_7]; decide
      have factor_9_9 : (47 : ZMod 388181593801) ^ 797 = 171277644947 := by
        calc
          (47 : ZMod 388181593801) ^ 797 = (47 : ZMod 388181593801) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 398 * (47 : ZMod 388181593801) ^ 398) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 171277644947 := by rw [factor_9_8]; decide
      have factor_9_10 : (47 : ZMod 388181593801) ^ 1595 = 63628544753 := by
        calc
          (47 : ZMod 388181593801) ^ 1595 = (47 : ZMod 388181593801) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 797 * (47 : ZMod 388181593801) ^ 797) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 63628544753 := by rw [factor_9_9]; decide
      have factor_9_11 : (47 : ZMod 388181593801) ^ 3191 = 90777600663 := by
        calc
          (47 : ZMod 388181593801) ^ 3191 = (47 : ZMod 388181593801) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1595 * (47 : ZMod 388181593801) ^ 1595) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 90777600663 := by rw [factor_9_10]; decide
      have factor_9_12 : (47 : ZMod 388181593801) ^ 6382 = 119327993071 := by
        calc
          (47 : ZMod 388181593801) ^ 6382 = (47 : ZMod 388181593801) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3191 * (47 : ZMod 388181593801) ^ 3191 := by rw [pow_add]
          _ = 119327993071 := by rw [factor_9_11]; decide
      have factor_9_13 : (47 : ZMod 388181593801) ^ 12765 = 138277300135 := by
        calc
          (47 : ZMod 388181593801) ^ 12765 = (47 : ZMod 388181593801) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 6382 * (47 : ZMod 388181593801) ^ 6382) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 138277300135 := by rw [factor_9_12]; decide
      have factor_9_14 : (47 : ZMod 388181593801) ^ 25530 = 315216585341 := by
        calc
          (47 : ZMod 388181593801) ^ 25530 = (47 : ZMod 388181593801) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 12765 * (47 : ZMod 388181593801) ^ 12765 := by rw [pow_add]
          _ = 315216585341 := by rw [factor_9_13]; decide
      have factor_9_15 : (47 : ZMod 388181593801) ^ 51061 = 386462190630 := by
        calc
          (47 : ZMod 388181593801) ^ 51061 = (47 : ZMod 388181593801) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 25530 * (47 : ZMod 388181593801) ^ 25530) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 386462190630 := by rw [factor_9_14]; decide
      have factor_9_16 : (47 : ZMod 388181593801) ^ 102123 = 150736602025 := by
        calc
          (47 : ZMod 388181593801) ^ 102123 = (47 : ZMod 388181593801) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 51061 * (47 : ZMod 388181593801) ^ 51061) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 150736602025 := by rw [factor_9_15]; decide
      have factor_9_17 : (47 : ZMod 388181593801) ^ 204247 = 202045637046 := by
        calc
          (47 : ZMod 388181593801) ^ 204247 = (47 : ZMod 388181593801) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 102123 * (47 : ZMod 388181593801) ^ 102123) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 202045637046 := by rw [factor_9_16]; decide
      have factor_9_18 : (47 : ZMod 388181593801) ^ 408495 = 115293221481 := by
        calc
          (47 : ZMod 388181593801) ^ 408495 = (47 : ZMod 388181593801) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 204247 * (47 : ZMod 388181593801) ^ 204247) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 115293221481 := by rw [factor_9_17]; decide
      have factor_9_19 : (47 : ZMod 388181593801) ^ 816990 = 378043319782 := by
        calc
          (47 : ZMod 388181593801) ^ 816990 = (47 : ZMod 388181593801) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 408495 * (47 : ZMod 388181593801) ^ 408495 := by rw [pow_add]
          _ = 378043319782 := by rw [factor_9_18]; decide
      have factor_9_20 : (47 : ZMod 388181593801) ^ 1633980 = 43332416924 := by
        calc
          (47 : ZMod 388181593801) ^ 1633980 = (47 : ZMod 388181593801) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 816990 * (47 : ZMod 388181593801) ^ 816990 := by rw [pow_add]
          _ = 43332416924 := by rw [factor_9_19]; decide
      have factor_9_21 : (47 : ZMod 388181593801) ^ 3267961 = 31190605664 := by
        calc
          (47 : ZMod 388181593801) ^ 3267961 = (47 : ZMod 388181593801) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 1633980 * (47 : ZMod 388181593801) ^ 1633980) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 31190605664 := by rw [factor_9_20]; decide
      have factor_9_22 : (47 : ZMod 388181593801) ^ 6535923 = 174822262713 := by
        calc
          (47 : ZMod 388181593801) ^ 6535923 = (47 : ZMod 388181593801) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 3267961 * (47 : ZMod 388181593801) ^ 3267961) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 174822262713 := by rw [factor_9_21]; decide
      have factor_9_23 : (47 : ZMod 388181593801) ^ 13071847 = 185972976739 := by
        calc
          (47 : ZMod 388181593801) ^ 13071847 = (47 : ZMod 388181593801) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 6535923 * (47 : ZMod 388181593801) ^ 6535923) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 185972976739 := by rw [factor_9_22]; decide
      have factor_9_24 : (47 : ZMod 388181593801) ^ 26143695 = 259788254102 := by
        calc
          (47 : ZMod 388181593801) ^ 26143695 = (47 : ZMod 388181593801) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 13071847 * (47 : ZMod 388181593801) ^ 13071847) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 259788254102 := by rw [factor_9_23]; decide
      have factor_9_25 : (47 : ZMod 388181593801) ^ 52287391 = 190601001990 := by
        calc
          (47 : ZMod 388181593801) ^ 52287391 = (47 : ZMod 388181593801) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 26143695 * (47 : ZMod 388181593801) ^ 26143695) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 190601001990 := by rw [factor_9_24]; decide
      have factor_9_26 : (47 : ZMod 388181593801) ^ 104574782 = 6312280323 := by
        calc
          (47 : ZMod 388181593801) ^ 104574782 = (47 : ZMod 388181593801) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 52287391 * (47 : ZMod 388181593801) ^ 52287391 := by rw [pow_add]
          _ = 6312280323 := by rw [factor_9_25]; decide
      have factor_9_27 : (47 : ZMod 388181593801) ^ 209149565 = 206085521100 := by
        calc
          (47 : ZMod 388181593801) ^ 209149565 = (47 : ZMod 388181593801) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 104574782 * (47 : ZMod 388181593801) ^ 104574782) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 206085521100 := by rw [factor_9_26]; decide
      have factor_9_28 : (47 : ZMod 388181593801) ^ 418299131 = 353215740328 := by
        calc
          (47 : ZMod 388181593801) ^ 418299131 = (47 : ZMod 388181593801) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 209149565 * (47 : ZMod 388181593801) ^ 209149565) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 353215740328 := by rw [factor_9_27]; decide
      have factor_9_29 : (47 : ZMod 388181593801) ^ 836598262 = 287210516371 := by
        calc
          (47 : ZMod 388181593801) ^ 836598262 = (47 : ZMod 388181593801) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 418299131 * (47 : ZMod 388181593801) ^ 418299131 := by rw [pow_add]
          _ = 287210516371 := by rw [factor_9_28]; decide
      have factor_9_30 : (47 : ZMod 388181593801) ^ 1673196525 = 165434605387 := by
        calc
          (47 : ZMod 388181593801) ^ 1673196525 = (47 : ZMod 388181593801) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = ((47 : ZMod 388181593801) ^ 836598262 * (47 : ZMod 388181593801) ^ 836598262) * (47 : ZMod 388181593801) := by rw [pow_succ, pow_add]
          _ = 165434605387 := by rw [factor_9_29]; decide
      have factor_9_31 : (47 : ZMod 388181593801) ^ 3346393050 = 285094761544 := by
        calc
          (47 : ZMod 388181593801) ^ 3346393050 = (47 : ZMod 388181593801) ^ (1673196525 + 1673196525) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 1673196525 * (47 : ZMod 388181593801) ^ 1673196525 := by rw [pow_add]
          _ = 285094761544 := by rw [factor_9_30]; decide
      have factor_9_32 : (47 : ZMod 388181593801) ^ 6692786100 = 162754183552 := by
        calc
          (47 : ZMod 388181593801) ^ 6692786100 = (47 : ZMod 388181593801) ^ (3346393050 + 3346393050) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 3346393050 * (47 : ZMod 388181593801) ^ 3346393050 := by rw [pow_add]
          _ = 162754183552 := by rw [factor_9_31]; decide
      have factor_9_33 : (47 : ZMod 388181593801) ^ 13385572200 = 314523799480 := by
        calc
          (47 : ZMod 388181593801) ^ 13385572200 = (47 : ZMod 388181593801) ^ (6692786100 + 6692786100) :=
            congrArg (fun n : ℕ => (47 : ZMod 388181593801) ^ n) (by norm_num)
          _ = (47 : ZMod 388181593801) ^ 6692786100 * (47 : ZMod 388181593801) ^ 6692786100 := by rw [pow_add]
          _ = 314523799480 := by rw [factor_9_32]; decide
      change (47 : ZMod 388181593801) ^ 13385572200 ≠ 1
      rw [factor_9_33]
      decide

#print axioms prime_lucas_388181593801

end TotientTailPeriodKiller
end Erdos249257
