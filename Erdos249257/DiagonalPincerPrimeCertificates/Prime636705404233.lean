import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_636705404233 : Nat.Prime 636705404233 := by
  apply lucas_primality 636705404233 (5 : ZMod 636705404233)
  ·
      have fermat_0 : (5 : ZMod 636705404233) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 636705404233) ^ 2 = 25 := by
        calc
          (5 : ZMod 636705404233) ^ 2 = (5 : ZMod 636705404233) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1 * (5 : ZMod 636705404233) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 636705404233) ^ 4 = 625 := by
        calc
          (5 : ZMod 636705404233) ^ 4 = (5 : ZMod 636705404233) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 2 * (5 : ZMod 636705404233) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 636705404233) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 636705404233) ^ 9 = (5 : ZMod 636705404233) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 4 * (5 : ZMod 636705404233) ^ 4) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 636705404233) ^ 18 = 631170244460 := by
        calc
          (5 : ZMod 636705404233) ^ 18 = (5 : ZMod 636705404233) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 9 * (5 : ZMod 636705404233) ^ 9 := by rw [pow_add]
          _ = 631170244460 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 636705404233) ^ 37 = 30300444304 := by
        calc
          (5 : ZMod 636705404233) ^ 37 = (5 : ZMod 636705404233) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 18 * (5 : ZMod 636705404233) ^ 18) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 30300444304 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 636705404233) ^ 74 = 155548805860 := by
        calc
          (5 : ZMod 636705404233) ^ 74 = (5 : ZMod 636705404233) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 37 * (5 : ZMod 636705404233) ^ 37 := by rw [pow_add]
          _ = 155548805860 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 636705404233) ^ 148 = 333430483742 := by
        calc
          (5 : ZMod 636705404233) ^ 148 = (5 : ZMod 636705404233) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 74 * (5 : ZMod 636705404233) ^ 74 := by rw [pow_add]
          _ = 333430483742 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 636705404233) ^ 296 = 402457534299 := by
        calc
          (5 : ZMod 636705404233) ^ 296 = (5 : ZMod 636705404233) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 148 * (5 : ZMod 636705404233) ^ 148 := by rw [pow_add]
          _ = 402457534299 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 636705404233) ^ 592 = 516541594659 := by
        calc
          (5 : ZMod 636705404233) ^ 592 = (5 : ZMod 636705404233) ^ (296 + 296) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 296 * (5 : ZMod 636705404233) ^ 296 := by rw [pow_add]
          _ = 516541594659 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 636705404233) ^ 1185 = 492392735378 := by
        calc
          (5 : ZMod 636705404233) ^ 1185 = (5 : ZMod 636705404233) ^ (592 + 592 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 592 * (5 : ZMod 636705404233) ^ 592) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 492392735378 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 636705404233) ^ 2371 = 26641078471 := by
        calc
          (5 : ZMod 636705404233) ^ 2371 = (5 : ZMod 636705404233) ^ (1185 + 1185 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1185 * (5 : ZMod 636705404233) ^ 1185) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 26641078471 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 636705404233) ^ 4743 = 367690119600 := by
        calc
          (5 : ZMod 636705404233) ^ 4743 = (5 : ZMod 636705404233) ^ (2371 + 2371 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 2371 * (5 : ZMod 636705404233) ^ 2371) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 367690119600 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 636705404233) ^ 9487 = 326452977500 := by
        calc
          (5 : ZMod 636705404233) ^ 9487 = (5 : ZMod 636705404233) ^ (4743 + 4743 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 4743 * (5 : ZMod 636705404233) ^ 4743) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 326452977500 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 636705404233) ^ 18975 = 103374295958 := by
        calc
          (5 : ZMod 636705404233) ^ 18975 = (5 : ZMod 636705404233) ^ (9487 + 9487 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 9487 * (5 : ZMod 636705404233) ^ 9487) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 103374295958 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 636705404233) ^ 37950 = 418881991171 := by
        calc
          (5 : ZMod 636705404233) ^ 37950 = (5 : ZMod 636705404233) ^ (18975 + 18975) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 18975 * (5 : ZMod 636705404233) ^ 18975 := by rw [pow_add]
          _ = 418881991171 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 636705404233) ^ 75901 = 154609922063 := by
        calc
          (5 : ZMod 636705404233) ^ 75901 = (5 : ZMod 636705404233) ^ (37950 + 37950 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 37950 * (5 : ZMod 636705404233) ^ 37950) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 154609922063 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 636705404233) ^ 151802 = 466481348081 := by
        calc
          (5 : ZMod 636705404233) ^ 151802 = (5 : ZMod 636705404233) ^ (75901 + 75901) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 75901 * (5 : ZMod 636705404233) ^ 75901 := by rw [pow_add]
          _ = 466481348081 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 636705404233) ^ 303604 = 524432048046 := by
        calc
          (5 : ZMod 636705404233) ^ 303604 = (5 : ZMod 636705404233) ^ (151802 + 151802) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 151802 * (5 : ZMod 636705404233) ^ 151802 := by rw [pow_add]
          _ = 524432048046 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 636705404233) ^ 607209 = 94931019494 := by
        calc
          (5 : ZMod 636705404233) ^ 607209 = (5 : ZMod 636705404233) ^ (303604 + 303604 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 303604 * (5 : ZMod 636705404233) ^ 303604) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 94931019494 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 636705404233) ^ 1214419 = 249160851964 := by
        calc
          (5 : ZMod 636705404233) ^ 1214419 = (5 : ZMod 636705404233) ^ (607209 + 607209 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 607209 * (5 : ZMod 636705404233) ^ 607209) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 249160851964 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 636705404233) ^ 2428838 = 366288254383 := by
        calc
          (5 : ZMod 636705404233) ^ 2428838 = (5 : ZMod 636705404233) ^ (1214419 + 1214419) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1214419 * (5 : ZMod 636705404233) ^ 1214419 := by rw [pow_add]
          _ = 366288254383 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 636705404233) ^ 4857676 = 310520856909 := by
        calc
          (5 : ZMod 636705404233) ^ 4857676 = (5 : ZMod 636705404233) ^ (2428838 + 2428838) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 2428838 * (5 : ZMod 636705404233) ^ 2428838 := by rw [pow_add]
          _ = 310520856909 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 636705404233) ^ 9715353 = 196217697409 := by
        calc
          (5 : ZMod 636705404233) ^ 9715353 = (5 : ZMod 636705404233) ^ (4857676 + 4857676 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 4857676 * (5 : ZMod 636705404233) ^ 4857676) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 196217697409 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 636705404233) ^ 19430706 = 508699255611 := by
        calc
          (5 : ZMod 636705404233) ^ 19430706 = (5 : ZMod 636705404233) ^ (9715353 + 9715353) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 9715353 * (5 : ZMod 636705404233) ^ 9715353 := by rw [pow_add]
          _ = 508699255611 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 636705404233) ^ 38861413 = 137029295875 := by
        calc
          (5 : ZMod 636705404233) ^ 38861413 = (5 : ZMod 636705404233) ^ (19430706 + 19430706 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 19430706 * (5 : ZMod 636705404233) ^ 19430706) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 137029295875 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 636705404233) ^ 77722827 = 453930921837 := by
        calc
          (5 : ZMod 636705404233) ^ 77722827 = (5 : ZMod 636705404233) ^ (38861413 + 38861413 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 38861413 * (5 : ZMod 636705404233) ^ 38861413) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 453930921837 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 636705404233) ^ 155445655 = 371248802098 := by
        calc
          (5 : ZMod 636705404233) ^ 155445655 = (5 : ZMod 636705404233) ^ (77722827 + 77722827 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 77722827 * (5 : ZMod 636705404233) ^ 77722827) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 371248802098 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 636705404233) ^ 310891310 = 155895206225 := by
        calc
          (5 : ZMod 636705404233) ^ 310891310 = (5 : ZMod 636705404233) ^ (155445655 + 155445655) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 155445655 * (5 : ZMod 636705404233) ^ 155445655 := by rw [pow_add]
          _ = 155895206225 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 636705404233) ^ 621782621 = 133321892471 := by
        calc
          (5 : ZMod 636705404233) ^ 621782621 = (5 : ZMod 636705404233) ^ (310891310 + 310891310 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 310891310 * (5 : ZMod 636705404233) ^ 310891310) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 133321892471 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 636705404233) ^ 1243565242 = 37800871713 := by
        calc
          (5 : ZMod 636705404233) ^ 1243565242 = (5 : ZMod 636705404233) ^ (621782621 + 621782621) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 621782621 * (5 : ZMod 636705404233) ^ 621782621 := by rw [pow_add]
          _ = 37800871713 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 636705404233) ^ 2487130485 = 372488640732 := by
        calc
          (5 : ZMod 636705404233) ^ 2487130485 = (5 : ZMod 636705404233) ^ (1243565242 + 1243565242 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1243565242 * (5 : ZMod 636705404233) ^ 1243565242) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 372488640732 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 636705404233) ^ 4974260970 = 528112603155 := by
        calc
          (5 : ZMod 636705404233) ^ 4974260970 = (5 : ZMod 636705404233) ^ (2487130485 + 2487130485) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 2487130485 * (5 : ZMod 636705404233) ^ 2487130485 := by rw [pow_add]
          _ = 528112603155 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 636705404233) ^ 9948521941 = 629543904991 := by
        calc
          (5 : ZMod 636705404233) ^ 9948521941 = (5 : ZMod 636705404233) ^ (4974260970 + 4974260970 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 4974260970 * (5 : ZMod 636705404233) ^ 4974260970) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 629543904991 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 636705404233) ^ 19897043882 = 294772227600 := by
        calc
          (5 : ZMod 636705404233) ^ 19897043882 = (5 : ZMod 636705404233) ^ (9948521941 + 9948521941) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 9948521941 * (5 : ZMod 636705404233) ^ 9948521941 := by rw [pow_add]
          _ = 294772227600 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 636705404233) ^ 39794087764 = 537239008881 := by
        calc
          (5 : ZMod 636705404233) ^ 39794087764 = (5 : ZMod 636705404233) ^ (19897043882 + 19897043882) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 19897043882 * (5 : ZMod 636705404233) ^ 19897043882 := by rw [pow_add]
          _ = 537239008881 := by rw [fermat_34]; decide
      have fermat_36 : (5 : ZMod 636705404233) ^ 79588175529 = 627386643538 := by
        calc
          (5 : ZMod 636705404233) ^ 79588175529 = (5 : ZMod 636705404233) ^ (39794087764 + 39794087764 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 39794087764 * (5 : ZMod 636705404233) ^ 39794087764) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 627386643538 := by rw [fermat_35]; decide
      have fermat_37 : (5 : ZMod 636705404233) ^ 159176351058 = 135095724428 := by
        calc
          (5 : ZMod 636705404233) ^ 159176351058 = (5 : ZMod 636705404233) ^ (79588175529 + 79588175529) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 79588175529 * (5 : ZMod 636705404233) ^ 79588175529 := by rw [pow_add]
          _ = 135095724428 := by rw [fermat_36]; decide
      have fermat_38 : (5 : ZMod 636705404233) ^ 318352702116 = 636705404232 := by
        calc
          (5 : ZMod 636705404233) ^ 318352702116 = (5 : ZMod 636705404233) ^ (159176351058 + 159176351058) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 159176351058 * (5 : ZMod 636705404233) ^ 159176351058 := by rw [pow_add]
          _ = 636705404232 := by rw [fermat_37]; decide
      have fermat_39 : (5 : ZMod 636705404233) ^ 636705404232 = 1 := by
        calc
          (5 : ZMod 636705404233) ^ 636705404232 = (5 : ZMod 636705404233) ^ (318352702116 + 318352702116) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 318352702116 * (5 : ZMod 636705404233) ^ 318352702116 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (43, 1), (61, 1), (10114141, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (43, 1), (61, 1), (10114141, 1)] : List FactorBlock).map factorBlockValue).prod = 636705404233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 636705404233) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 636705404233) ^ 2 = 25 := by
        calc
          (5 : ZMod 636705404233) ^ 2 = (5 : ZMod 636705404233) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1 * (5 : ZMod 636705404233) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 636705404233) ^ 4 = 625 := by
        calc
          (5 : ZMod 636705404233) ^ 4 = (5 : ZMod 636705404233) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 2 * (5 : ZMod 636705404233) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 636705404233) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 636705404233) ^ 9 = (5 : ZMod 636705404233) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 4 * (5 : ZMod 636705404233) ^ 4) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 636705404233) ^ 18 = 631170244460 := by
        calc
          (5 : ZMod 636705404233) ^ 18 = (5 : ZMod 636705404233) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 9 * (5 : ZMod 636705404233) ^ 9 := by rw [pow_add]
          _ = 631170244460 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 636705404233) ^ 37 = 30300444304 := by
        calc
          (5 : ZMod 636705404233) ^ 37 = (5 : ZMod 636705404233) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 18 * (5 : ZMod 636705404233) ^ 18) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 30300444304 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 636705404233) ^ 74 = 155548805860 := by
        calc
          (5 : ZMod 636705404233) ^ 74 = (5 : ZMod 636705404233) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 37 * (5 : ZMod 636705404233) ^ 37 := by rw [pow_add]
          _ = 155548805860 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 636705404233) ^ 148 = 333430483742 := by
        calc
          (5 : ZMod 636705404233) ^ 148 = (5 : ZMod 636705404233) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 74 * (5 : ZMod 636705404233) ^ 74 := by rw [pow_add]
          _ = 333430483742 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 636705404233) ^ 296 = 402457534299 := by
        calc
          (5 : ZMod 636705404233) ^ 296 = (5 : ZMod 636705404233) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 148 * (5 : ZMod 636705404233) ^ 148 := by rw [pow_add]
          _ = 402457534299 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 636705404233) ^ 592 = 516541594659 := by
        calc
          (5 : ZMod 636705404233) ^ 592 = (5 : ZMod 636705404233) ^ (296 + 296) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 296 * (5 : ZMod 636705404233) ^ 296 := by rw [pow_add]
          _ = 516541594659 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 636705404233) ^ 1185 = 492392735378 := by
        calc
          (5 : ZMod 636705404233) ^ 1185 = (5 : ZMod 636705404233) ^ (592 + 592 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 592 * (5 : ZMod 636705404233) ^ 592) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 492392735378 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 636705404233) ^ 2371 = 26641078471 := by
        calc
          (5 : ZMod 636705404233) ^ 2371 = (5 : ZMod 636705404233) ^ (1185 + 1185 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1185 * (5 : ZMod 636705404233) ^ 1185) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 26641078471 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 636705404233) ^ 4743 = 367690119600 := by
        calc
          (5 : ZMod 636705404233) ^ 4743 = (5 : ZMod 636705404233) ^ (2371 + 2371 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 2371 * (5 : ZMod 636705404233) ^ 2371) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 367690119600 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 636705404233) ^ 9487 = 326452977500 := by
        calc
          (5 : ZMod 636705404233) ^ 9487 = (5 : ZMod 636705404233) ^ (4743 + 4743 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 4743 * (5 : ZMod 636705404233) ^ 4743) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 326452977500 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 636705404233) ^ 18975 = 103374295958 := by
        calc
          (5 : ZMod 636705404233) ^ 18975 = (5 : ZMod 636705404233) ^ (9487 + 9487 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 9487 * (5 : ZMod 636705404233) ^ 9487) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 103374295958 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 636705404233) ^ 37950 = 418881991171 := by
        calc
          (5 : ZMod 636705404233) ^ 37950 = (5 : ZMod 636705404233) ^ (18975 + 18975) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 18975 * (5 : ZMod 636705404233) ^ 18975 := by rw [pow_add]
          _ = 418881991171 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 636705404233) ^ 75901 = 154609922063 := by
        calc
          (5 : ZMod 636705404233) ^ 75901 = (5 : ZMod 636705404233) ^ (37950 + 37950 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 37950 * (5 : ZMod 636705404233) ^ 37950) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 154609922063 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 636705404233) ^ 151802 = 466481348081 := by
        calc
          (5 : ZMod 636705404233) ^ 151802 = (5 : ZMod 636705404233) ^ (75901 + 75901) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 75901 * (5 : ZMod 636705404233) ^ 75901 := by rw [pow_add]
          _ = 466481348081 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 636705404233) ^ 303604 = 524432048046 := by
        calc
          (5 : ZMod 636705404233) ^ 303604 = (5 : ZMod 636705404233) ^ (151802 + 151802) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 151802 * (5 : ZMod 636705404233) ^ 151802 := by rw [pow_add]
          _ = 524432048046 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 636705404233) ^ 607209 = 94931019494 := by
        calc
          (5 : ZMod 636705404233) ^ 607209 = (5 : ZMod 636705404233) ^ (303604 + 303604 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 303604 * (5 : ZMod 636705404233) ^ 303604) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 94931019494 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 636705404233) ^ 1214419 = 249160851964 := by
        calc
          (5 : ZMod 636705404233) ^ 1214419 = (5 : ZMod 636705404233) ^ (607209 + 607209 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 607209 * (5 : ZMod 636705404233) ^ 607209) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 249160851964 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 636705404233) ^ 2428838 = 366288254383 := by
        calc
          (5 : ZMod 636705404233) ^ 2428838 = (5 : ZMod 636705404233) ^ (1214419 + 1214419) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1214419 * (5 : ZMod 636705404233) ^ 1214419 := by rw [pow_add]
          _ = 366288254383 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 636705404233) ^ 4857676 = 310520856909 := by
        calc
          (5 : ZMod 636705404233) ^ 4857676 = (5 : ZMod 636705404233) ^ (2428838 + 2428838) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 2428838 * (5 : ZMod 636705404233) ^ 2428838 := by rw [pow_add]
          _ = 310520856909 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 636705404233) ^ 9715353 = 196217697409 := by
        calc
          (5 : ZMod 636705404233) ^ 9715353 = (5 : ZMod 636705404233) ^ (4857676 + 4857676 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 4857676 * (5 : ZMod 636705404233) ^ 4857676) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 196217697409 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 636705404233) ^ 19430706 = 508699255611 := by
        calc
          (5 : ZMod 636705404233) ^ 19430706 = (5 : ZMod 636705404233) ^ (9715353 + 9715353) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 9715353 * (5 : ZMod 636705404233) ^ 9715353 := by rw [pow_add]
          _ = 508699255611 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 636705404233) ^ 38861413 = 137029295875 := by
        calc
          (5 : ZMod 636705404233) ^ 38861413 = (5 : ZMod 636705404233) ^ (19430706 + 19430706 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 19430706 * (5 : ZMod 636705404233) ^ 19430706) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 137029295875 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 636705404233) ^ 77722827 = 453930921837 := by
        calc
          (5 : ZMod 636705404233) ^ 77722827 = (5 : ZMod 636705404233) ^ (38861413 + 38861413 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 38861413 * (5 : ZMod 636705404233) ^ 38861413) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 453930921837 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 636705404233) ^ 155445655 = 371248802098 := by
        calc
          (5 : ZMod 636705404233) ^ 155445655 = (5 : ZMod 636705404233) ^ (77722827 + 77722827 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 77722827 * (5 : ZMod 636705404233) ^ 77722827) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 371248802098 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 636705404233) ^ 310891310 = 155895206225 := by
        calc
          (5 : ZMod 636705404233) ^ 310891310 = (5 : ZMod 636705404233) ^ (155445655 + 155445655) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 155445655 * (5 : ZMod 636705404233) ^ 155445655 := by rw [pow_add]
          _ = 155895206225 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 636705404233) ^ 621782621 = 133321892471 := by
        calc
          (5 : ZMod 636705404233) ^ 621782621 = (5 : ZMod 636705404233) ^ (310891310 + 310891310 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 310891310 * (5 : ZMod 636705404233) ^ 310891310) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 133321892471 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 636705404233) ^ 1243565242 = 37800871713 := by
        calc
          (5 : ZMod 636705404233) ^ 1243565242 = (5 : ZMod 636705404233) ^ (621782621 + 621782621) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 621782621 * (5 : ZMod 636705404233) ^ 621782621 := by rw [pow_add]
          _ = 37800871713 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 636705404233) ^ 2487130485 = 372488640732 := by
        calc
          (5 : ZMod 636705404233) ^ 2487130485 = (5 : ZMod 636705404233) ^ (1243565242 + 1243565242 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1243565242 * (5 : ZMod 636705404233) ^ 1243565242) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 372488640732 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 636705404233) ^ 4974260970 = 528112603155 := by
        calc
          (5 : ZMod 636705404233) ^ 4974260970 = (5 : ZMod 636705404233) ^ (2487130485 + 2487130485) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 2487130485 * (5 : ZMod 636705404233) ^ 2487130485 := by rw [pow_add]
          _ = 528112603155 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 636705404233) ^ 9948521941 = 629543904991 := by
        calc
          (5 : ZMod 636705404233) ^ 9948521941 = (5 : ZMod 636705404233) ^ (4974260970 + 4974260970 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 4974260970 * (5 : ZMod 636705404233) ^ 4974260970) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 629543904991 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 636705404233) ^ 19897043882 = 294772227600 := by
        calc
          (5 : ZMod 636705404233) ^ 19897043882 = (5 : ZMod 636705404233) ^ (9948521941 + 9948521941) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 9948521941 * (5 : ZMod 636705404233) ^ 9948521941 := by rw [pow_add]
          _ = 294772227600 := by rw [factor_0_33]; decide
      have factor_0_35 : (5 : ZMod 636705404233) ^ 39794087764 = 537239008881 := by
        calc
          (5 : ZMod 636705404233) ^ 39794087764 = (5 : ZMod 636705404233) ^ (19897043882 + 19897043882) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 19897043882 * (5 : ZMod 636705404233) ^ 19897043882 := by rw [pow_add]
          _ = 537239008881 := by rw [factor_0_34]; decide
      have factor_0_36 : (5 : ZMod 636705404233) ^ 79588175529 = 627386643538 := by
        calc
          (5 : ZMod 636705404233) ^ 79588175529 = (5 : ZMod 636705404233) ^ (39794087764 + 39794087764 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 39794087764 * (5 : ZMod 636705404233) ^ 39794087764) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 627386643538 := by rw [factor_0_35]; decide
      have factor_0_37 : (5 : ZMod 636705404233) ^ 159176351058 = 135095724428 := by
        calc
          (5 : ZMod 636705404233) ^ 159176351058 = (5 : ZMod 636705404233) ^ (79588175529 + 79588175529) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 79588175529 * (5 : ZMod 636705404233) ^ 79588175529 := by rw [pow_add]
          _ = 135095724428 := by rw [factor_0_36]; decide
      have factor_0_38 : (5 : ZMod 636705404233) ^ 318352702116 = 636705404232 := by
        calc
          (5 : ZMod 636705404233) ^ 318352702116 = (5 : ZMod 636705404233) ^ (159176351058 + 159176351058) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 159176351058 * (5 : ZMod 636705404233) ^ 159176351058 := by rw [pow_add]
          _ = 636705404232 := by rw [factor_0_37]; decide
      change (5 : ZMod 636705404233) ^ 318352702116 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (5 : ZMod 636705404233) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 636705404233) ^ 3 = 125 := by
        calc
          (5 : ZMod 636705404233) ^ 3 = (5 : ZMod 636705404233) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1 * (5 : ZMod 636705404233) ^ 1) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 636705404233) ^ 6 = 15625 := by
        calc
          (5 : ZMod 636705404233) ^ 6 = (5 : ZMod 636705404233) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 3 * (5 : ZMod 636705404233) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 636705404233) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 636705404233) ^ 12 = (5 : ZMod 636705404233) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 6 * (5 : ZMod 636705404233) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 636705404233) ^ 24 = 105063522563 := by
        calc
          (5 : ZMod 636705404233) ^ 24 = (5 : ZMod 636705404233) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 12 * (5 : ZMod 636705404233) ^ 12 := by rw [pow_add]
          _ = 105063522563 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 636705404233) ^ 49 = 30610288704 := by
        calc
          (5 : ZMod 636705404233) ^ 49 = (5 : ZMod 636705404233) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 24 * (5 : ZMod 636705404233) ^ 24) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 30610288704 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 636705404233) ^ 98 = 558359651365 := by
        calc
          (5 : ZMod 636705404233) ^ 98 = (5 : ZMod 636705404233) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 49 * (5 : ZMod 636705404233) ^ 49 := by rw [pow_add]
          _ = 558359651365 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 636705404233) ^ 197 = 207710206375 := by
        calc
          (5 : ZMod 636705404233) ^ 197 = (5 : ZMod 636705404233) ^ (98 + 98 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 98 * (5 : ZMod 636705404233) ^ 98) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 207710206375 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 636705404233) ^ 395 = 53845106916 := by
        calc
          (5 : ZMod 636705404233) ^ 395 = (5 : ZMod 636705404233) ^ (197 + 197 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 197 * (5 : ZMod 636705404233) ^ 197) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 53845106916 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 636705404233) ^ 790 = 130022184282 := by
        calc
          (5 : ZMod 636705404233) ^ 790 = (5 : ZMod 636705404233) ^ (395 + 395) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 395 * (5 : ZMod 636705404233) ^ 395 := by rw [pow_add]
          _ = 130022184282 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 636705404233) ^ 1581 = 215848259261 := by
        calc
          (5 : ZMod 636705404233) ^ 1581 = (5 : ZMod 636705404233) ^ (790 + 790 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 790 * (5 : ZMod 636705404233) ^ 790) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 215848259261 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 636705404233) ^ 3162 = 245544578141 := by
        calc
          (5 : ZMod 636705404233) ^ 3162 = (5 : ZMod 636705404233) ^ (1581 + 1581) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1581 * (5 : ZMod 636705404233) ^ 1581 := by rw [pow_add]
          _ = 245544578141 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 636705404233) ^ 6325 = 93219048265 := by
        calc
          (5 : ZMod 636705404233) ^ 6325 = (5 : ZMod 636705404233) ^ (3162 + 3162 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 3162 * (5 : ZMod 636705404233) ^ 3162) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 93219048265 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 636705404233) ^ 12650 = 441032417797 := by
        calc
          (5 : ZMod 636705404233) ^ 12650 = (5 : ZMod 636705404233) ^ (6325 + 6325) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 6325 * (5 : ZMod 636705404233) ^ 6325 := by rw [pow_add]
          _ = 441032417797 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 636705404233) ^ 25300 = 470910552617 := by
        calc
          (5 : ZMod 636705404233) ^ 25300 = (5 : ZMod 636705404233) ^ (12650 + 12650) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 12650 * (5 : ZMod 636705404233) ^ 12650 := by rw [pow_add]
          _ = 470910552617 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 636705404233) ^ 50600 = 611207077794 := by
        calc
          (5 : ZMod 636705404233) ^ 50600 = (5 : ZMod 636705404233) ^ (25300 + 25300) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 25300 * (5 : ZMod 636705404233) ^ 25300 := by rw [pow_add]
          _ = 611207077794 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 636705404233) ^ 101201 = 267838050192 := by
        calc
          (5 : ZMod 636705404233) ^ 101201 = (5 : ZMod 636705404233) ^ (50600 + 50600 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 50600 * (5 : ZMod 636705404233) ^ 50600) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 267838050192 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 636705404233) ^ 202403 = 153921169886 := by
        calc
          (5 : ZMod 636705404233) ^ 202403 = (5 : ZMod 636705404233) ^ (101201 + 101201 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 101201 * (5 : ZMod 636705404233) ^ 101201) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 153921169886 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 636705404233) ^ 404806 = 613349841034 := by
        calc
          (5 : ZMod 636705404233) ^ 404806 = (5 : ZMod 636705404233) ^ (202403 + 202403) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 202403 * (5 : ZMod 636705404233) ^ 202403 := by rw [pow_add]
          _ = 613349841034 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 636705404233) ^ 809612 = 329873241236 := by
        calc
          (5 : ZMod 636705404233) ^ 809612 = (5 : ZMod 636705404233) ^ (404806 + 404806) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 404806 * (5 : ZMod 636705404233) ^ 404806 := by rw [pow_add]
          _ = 329873241236 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 636705404233) ^ 1619225 = 57972852279 := by
        calc
          (5 : ZMod 636705404233) ^ 1619225 = (5 : ZMod 636705404233) ^ (809612 + 809612 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 809612 * (5 : ZMod 636705404233) ^ 809612) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 57972852279 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 636705404233) ^ 3238451 = 254539128901 := by
        calc
          (5 : ZMod 636705404233) ^ 3238451 = (5 : ZMod 636705404233) ^ (1619225 + 1619225 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1619225 * (5 : ZMod 636705404233) ^ 1619225) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 254539128901 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 636705404233) ^ 6476902 = 92682523826 := by
        calc
          (5 : ZMod 636705404233) ^ 6476902 = (5 : ZMod 636705404233) ^ (3238451 + 3238451) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 3238451 * (5 : ZMod 636705404233) ^ 3238451 := by rw [pow_add]
          _ = 92682523826 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 636705404233) ^ 12953804 = 59574985311 := by
        calc
          (5 : ZMod 636705404233) ^ 12953804 = (5 : ZMod 636705404233) ^ (6476902 + 6476902) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 6476902 * (5 : ZMod 636705404233) ^ 6476902 := by rw [pow_add]
          _ = 59574985311 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 636705404233) ^ 25907609 = 217830261340 := by
        calc
          (5 : ZMod 636705404233) ^ 25907609 = (5 : ZMod 636705404233) ^ (12953804 + 12953804 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 12953804 * (5 : ZMod 636705404233) ^ 12953804) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 217830261340 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 636705404233) ^ 51815218 = 10925270757 := by
        calc
          (5 : ZMod 636705404233) ^ 51815218 = (5 : ZMod 636705404233) ^ (25907609 + 25907609) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 25907609 * (5 : ZMod 636705404233) ^ 25907609 := by rw [pow_add]
          _ = 10925270757 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 636705404233) ^ 103630436 = 34158020267 := by
        calc
          (5 : ZMod 636705404233) ^ 103630436 = (5 : ZMod 636705404233) ^ (51815218 + 51815218) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 51815218 * (5 : ZMod 636705404233) ^ 51815218 := by rw [pow_add]
          _ = 34158020267 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 636705404233) ^ 207260873 = 411473456255 := by
        calc
          (5 : ZMod 636705404233) ^ 207260873 = (5 : ZMod 636705404233) ^ (103630436 + 103630436 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 103630436 * (5 : ZMod 636705404233) ^ 103630436) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 411473456255 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 636705404233) ^ 414521747 = 507712042004 := by
        calc
          (5 : ZMod 636705404233) ^ 414521747 = (5 : ZMod 636705404233) ^ (207260873 + 207260873 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 207260873 * (5 : ZMod 636705404233) ^ 207260873) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 507712042004 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 636705404233) ^ 829043495 = 466104803859 := by
        calc
          (5 : ZMod 636705404233) ^ 829043495 = (5 : ZMod 636705404233) ^ (414521747 + 414521747 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 414521747 * (5 : ZMod 636705404233) ^ 414521747) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 466104803859 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 636705404233) ^ 1658086990 = 180022588487 := by
        calc
          (5 : ZMod 636705404233) ^ 1658086990 = (5 : ZMod 636705404233) ^ (829043495 + 829043495) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 829043495 * (5 : ZMod 636705404233) ^ 829043495 := by rw [pow_add]
          _ = 180022588487 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 636705404233) ^ 3316173980 = 261175575817 := by
        calc
          (5 : ZMod 636705404233) ^ 3316173980 = (5 : ZMod 636705404233) ^ (1658086990 + 1658086990) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1658086990 * (5 : ZMod 636705404233) ^ 1658086990 := by rw [pow_add]
          _ = 261175575817 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 636705404233) ^ 6632347960 = 446067258254 := by
        calc
          (5 : ZMod 636705404233) ^ 6632347960 = (5 : ZMod 636705404233) ^ (3316173980 + 3316173980) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 3316173980 * (5 : ZMod 636705404233) ^ 3316173980 := by rw [pow_add]
          _ = 446067258254 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 636705404233) ^ 13264695921 = 612016371034 := by
        calc
          (5 : ZMod 636705404233) ^ 13264695921 = (5 : ZMod 636705404233) ^ (6632347960 + 6632347960 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 6632347960 * (5 : ZMod 636705404233) ^ 6632347960) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 612016371034 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 636705404233) ^ 26529391843 = 431750525692 := by
        calc
          (5 : ZMod 636705404233) ^ 26529391843 = (5 : ZMod 636705404233) ^ (13264695921 + 13264695921 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 13264695921 * (5 : ZMod 636705404233) ^ 13264695921) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 431750525692 := by rw [factor_1_33]; decide
      have factor_1_35 : (5 : ZMod 636705404233) ^ 53058783686 = 463978620692 := by
        calc
          (5 : ZMod 636705404233) ^ 53058783686 = (5 : ZMod 636705404233) ^ (26529391843 + 26529391843) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 26529391843 * (5 : ZMod 636705404233) ^ 26529391843 := by rw [pow_add]
          _ = 463978620692 := by rw [factor_1_34]; decide
      have factor_1_36 : (5 : ZMod 636705404233) ^ 106117567372 = 449191485067 := by
        calc
          (5 : ZMod 636705404233) ^ 106117567372 = (5 : ZMod 636705404233) ^ (53058783686 + 53058783686) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 53058783686 * (5 : ZMod 636705404233) ^ 53058783686 := by rw [pow_add]
          _ = 449191485067 := by rw [factor_1_35]; decide
      have factor_1_37 : (5 : ZMod 636705404233) ^ 212235134744 = 449191485066 := by
        calc
          (5 : ZMod 636705404233) ^ 212235134744 = (5 : ZMod 636705404233) ^ (106117567372 + 106117567372) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 106117567372 * (5 : ZMod 636705404233) ^ 106117567372 := by rw [pow_add]
          _ = 449191485066 := by rw [factor_1_36]; decide
      change (5 : ZMod 636705404233) ^ 212235134744 ≠ 1
      rw [factor_1_37]
      decide
    ·
      have factor_2_0 : (5 : ZMod 636705404233) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 636705404233) ^ 3 = 125 := by
        calc
          (5 : ZMod 636705404233) ^ 3 = (5 : ZMod 636705404233) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1 * (5 : ZMod 636705404233) ^ 1) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 636705404233) ^ 6 = 15625 := by
        calc
          (5 : ZMod 636705404233) ^ 6 = (5 : ZMod 636705404233) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 3 * (5 : ZMod 636705404233) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 636705404233) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 636705404233) ^ 13 = (5 : ZMod 636705404233) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 6 * (5 : ZMod 636705404233) ^ 6) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 636705404233) ^ 27 = 398832235715 := by
        calc
          (5 : ZMod 636705404233) ^ 27 = (5 : ZMod 636705404233) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 13 * (5 : ZMod 636705404233) ^ 13) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 398832235715 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 636705404233) ^ 55 = 120002421017 := by
        calc
          (5 : ZMod 636705404233) ^ 55 = (5 : ZMod 636705404233) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 27 * (5 : ZMod 636705404233) ^ 27) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 120002421017 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 636705404233) ^ 110 = 584247252440 := by
        calc
          (5 : ZMod 636705404233) ^ 110 = (5 : ZMod 636705404233) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 55 * (5 : ZMod 636705404233) ^ 55 := by rw [pow_add]
          _ = 584247252440 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 636705404233) ^ 220 = 535588346680 := by
        calc
          (5 : ZMod 636705404233) ^ 220 = (5 : ZMod 636705404233) ^ (110 + 110) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 110 * (5 : ZMod 636705404233) ^ 110 := by rw [pow_add]
          _ = 535588346680 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 636705404233) ^ 441 = 425921507339 := by
        calc
          (5 : ZMod 636705404233) ^ 441 = (5 : ZMod 636705404233) ^ (220 + 220 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 220 * (5 : ZMod 636705404233) ^ 220) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 425921507339 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 636705404233) ^ 882 = 62665038506 := by
        calc
          (5 : ZMod 636705404233) ^ 882 = (5 : ZMod 636705404233) ^ (441 + 441) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 441 * (5 : ZMod 636705404233) ^ 441 := by rw [pow_add]
          _ = 62665038506 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 636705404233) ^ 1765 = 441503550703 := by
        calc
          (5 : ZMod 636705404233) ^ 1765 = (5 : ZMod 636705404233) ^ (882 + 882 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 882 * (5 : ZMod 636705404233) ^ 882) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 441503550703 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 636705404233) ^ 3530 = 319865993814 := by
        calc
          (5 : ZMod 636705404233) ^ 3530 = (5 : ZMod 636705404233) ^ (1765 + 1765) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1765 * (5 : ZMod 636705404233) ^ 1765 := by rw [pow_add]
          _ = 319865993814 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 636705404233) ^ 7060 = 541033164688 := by
        calc
          (5 : ZMod 636705404233) ^ 7060 = (5 : ZMod 636705404233) ^ (3530 + 3530) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 3530 * (5 : ZMod 636705404233) ^ 3530 := by rw [pow_add]
          _ = 541033164688 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 636705404233) ^ 14121 = 117553217677 := by
        calc
          (5 : ZMod 636705404233) ^ 14121 = (5 : ZMod 636705404233) ^ (7060 + 7060 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 7060 * (5 : ZMod 636705404233) ^ 7060) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 117553217677 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 636705404233) ^ 28242 = 604332037965 := by
        calc
          (5 : ZMod 636705404233) ^ 28242 = (5 : ZMod 636705404233) ^ (14121 + 14121) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 14121 * (5 : ZMod 636705404233) ^ 14121 := by rw [pow_add]
          _ = 604332037965 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 636705404233) ^ 56484 = 628124657182 := by
        calc
          (5 : ZMod 636705404233) ^ 56484 = (5 : ZMod 636705404233) ^ (28242 + 28242) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 28242 * (5 : ZMod 636705404233) ^ 28242 := by rw [pow_add]
          _ = 628124657182 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 636705404233) ^ 112969 = 500748808527 := by
        calc
          (5 : ZMod 636705404233) ^ 112969 = (5 : ZMod 636705404233) ^ (56484 + 56484 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 56484 * (5 : ZMod 636705404233) ^ 56484) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 500748808527 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 636705404233) ^ 225938 = 55863025330 := by
        calc
          (5 : ZMod 636705404233) ^ 225938 = (5 : ZMod 636705404233) ^ (112969 + 112969) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 112969 * (5 : ZMod 636705404233) ^ 112969 := by rw [pow_add]
          _ = 55863025330 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 636705404233) ^ 451876 = 67828179712 := by
        calc
          (5 : ZMod 636705404233) ^ 451876 = (5 : ZMod 636705404233) ^ (225938 + 225938) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 225938 * (5 : ZMod 636705404233) ^ 225938 := by rw [pow_add]
          _ = 67828179712 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 636705404233) ^ 903753 = 358250673816 := by
        calc
          (5 : ZMod 636705404233) ^ 903753 = (5 : ZMod 636705404233) ^ (451876 + 451876 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 451876 * (5 : ZMod 636705404233) ^ 451876) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 358250673816 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 636705404233) ^ 1807507 = 175906648954 := by
        calc
          (5 : ZMod 636705404233) ^ 1807507 = (5 : ZMod 636705404233) ^ (903753 + 903753 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 903753 * (5 : ZMod 636705404233) ^ 903753) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 175906648954 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 636705404233) ^ 3615015 = 132860845841 := by
        calc
          (5 : ZMod 636705404233) ^ 3615015 = (5 : ZMod 636705404233) ^ (1807507 + 1807507 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1807507 * (5 : ZMod 636705404233) ^ 1807507) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 132860845841 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 636705404233) ^ 7230030 = 363469363130 := by
        calc
          (5 : ZMod 636705404233) ^ 7230030 = (5 : ZMod 636705404233) ^ (3615015 + 3615015) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 3615015 * (5 : ZMod 636705404233) ^ 3615015 := by rw [pow_add]
          _ = 363469363130 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 636705404233) ^ 14460060 = 624933450517 := by
        calc
          (5 : ZMod 636705404233) ^ 14460060 = (5 : ZMod 636705404233) ^ (7230030 + 7230030) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 7230030 * (5 : ZMod 636705404233) ^ 7230030 := by rw [pow_add]
          _ = 624933450517 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 636705404233) ^ 28920121 = 582941425083 := by
        calc
          (5 : ZMod 636705404233) ^ 28920121 = (5 : ZMod 636705404233) ^ (14460060 + 14460060 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 14460060 * (5 : ZMod 636705404233) ^ 14460060) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 582941425083 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 636705404233) ^ 57840243 = 177426102429 := by
        calc
          (5 : ZMod 636705404233) ^ 57840243 = (5 : ZMod 636705404233) ^ (28920121 + 28920121 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 28920121 * (5 : ZMod 636705404233) ^ 28920121) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 177426102429 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 636705404233) ^ 115680487 = 385647387748 := by
        calc
          (5 : ZMod 636705404233) ^ 115680487 = (5 : ZMod 636705404233) ^ (57840243 + 57840243 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 57840243 * (5 : ZMod 636705404233) ^ 57840243) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 385647387748 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 636705404233) ^ 231360975 = 543906726438 := by
        calc
          (5 : ZMod 636705404233) ^ 231360975 = (5 : ZMod 636705404233) ^ (115680487 + 115680487 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 115680487 * (5 : ZMod 636705404233) ^ 115680487) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 543906726438 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 636705404233) ^ 462721950 = 35608971286 := by
        calc
          (5 : ZMod 636705404233) ^ 462721950 = (5 : ZMod 636705404233) ^ (231360975 + 231360975) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 231360975 * (5 : ZMod 636705404233) ^ 231360975 := by rw [pow_add]
          _ = 35608971286 := by rw [factor_2_27]; decide
      have factor_2_29 : (5 : ZMod 636705404233) ^ 925443901 = 431970590108 := by
        calc
          (5 : ZMod 636705404233) ^ 925443901 = (5 : ZMod 636705404233) ^ (462721950 + 462721950 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 462721950 * (5 : ZMod 636705404233) ^ 462721950) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 431970590108 := by rw [factor_2_28]; decide
      have factor_2_30 : (5 : ZMod 636705404233) ^ 1850887803 = 438591424345 := by
        calc
          (5 : ZMod 636705404233) ^ 1850887803 = (5 : ZMod 636705404233) ^ (925443901 + 925443901 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 925443901 * (5 : ZMod 636705404233) ^ 925443901) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 438591424345 := by rw [factor_2_29]; decide
      have factor_2_31 : (5 : ZMod 636705404233) ^ 3701775606 = 270354994596 := by
        calc
          (5 : ZMod 636705404233) ^ 3701775606 = (5 : ZMod 636705404233) ^ (1850887803 + 1850887803) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1850887803 * (5 : ZMod 636705404233) ^ 1850887803 := by rw [pow_add]
          _ = 270354994596 := by rw [factor_2_30]; decide
      have factor_2_32 : (5 : ZMod 636705404233) ^ 7403551212 = 141701315079 := by
        calc
          (5 : ZMod 636705404233) ^ 7403551212 = (5 : ZMod 636705404233) ^ (3701775606 + 3701775606) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 3701775606 * (5 : ZMod 636705404233) ^ 3701775606 := by rw [pow_add]
          _ = 141701315079 := by rw [factor_2_31]; decide
      have factor_2_33 : (5 : ZMod 636705404233) ^ 14807102424 = 240351488223 := by
        calc
          (5 : ZMod 636705404233) ^ 14807102424 = (5 : ZMod 636705404233) ^ (7403551212 + 7403551212) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 7403551212 * (5 : ZMod 636705404233) ^ 7403551212 := by rw [pow_add]
          _ = 240351488223 := by rw [factor_2_32]; decide
      change (5 : ZMod 636705404233) ^ 14807102424 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (5 : ZMod 636705404233) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 636705404233) ^ 2 = 25 := by
        calc
          (5 : ZMod 636705404233) ^ 2 = (5 : ZMod 636705404233) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1 * (5 : ZMod 636705404233) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 636705404233) ^ 4 = 625 := by
        calc
          (5 : ZMod 636705404233) ^ 4 = (5 : ZMod 636705404233) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 2 * (5 : ZMod 636705404233) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 636705404233) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 636705404233) ^ 9 = (5 : ZMod 636705404233) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 4 * (5 : ZMod 636705404233) ^ 4) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 636705404233) ^ 19 = 609029605368 := by
        calc
          (5 : ZMod 636705404233) ^ 19 = (5 : ZMod 636705404233) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 9 * (5 : ZMod 636705404233) ^ 9) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 609029605368 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 636705404233) ^ 38 = 151502221520 := by
        calc
          (5 : ZMod 636705404233) ^ 38 = (5 : ZMod 636705404233) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 19 * (5 : ZMod 636705404233) ^ 19 := by rw [pow_add]
          _ = 151502221520 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 636705404233) ^ 77 = 342438605510 := by
        calc
          (5 : ZMod 636705404233) ^ 77 = (5 : ZMod 636705404233) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 38 * (5 : ZMod 636705404233) ^ 38) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 342438605510 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 636705404233) ^ 155 = 365044363254 := by
        calc
          (5 : ZMod 636705404233) ^ 155 = (5 : ZMod 636705404233) ^ (77 + 77 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 77 * (5 : ZMod 636705404233) ^ 77) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 365044363254 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 636705404233) ^ 311 = 155334297450 := by
        calc
          (5 : ZMod 636705404233) ^ 311 = (5 : ZMod 636705404233) ^ (155 + 155 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 155 * (5 : ZMod 636705404233) ^ 155) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 155334297450 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 636705404233) ^ 622 = 25603799519 := by
        calc
          (5 : ZMod 636705404233) ^ 622 = (5 : ZMod 636705404233) ^ (311 + 311) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 311 * (5 : ZMod 636705404233) ^ 311 := by rw [pow_add]
          _ = 25603799519 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 636705404233) ^ 1244 = 362025712023 := by
        calc
          (5 : ZMod 636705404233) ^ 1244 = (5 : ZMod 636705404233) ^ (622 + 622) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 622 * (5 : ZMod 636705404233) ^ 622 := by rw [pow_add]
          _ = 362025712023 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 636705404233) ^ 2488 = 497584203595 := by
        calc
          (5 : ZMod 636705404233) ^ 2488 = (5 : ZMod 636705404233) ^ (1244 + 1244) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1244 * (5 : ZMod 636705404233) ^ 1244 := by rw [pow_add]
          _ = 497584203595 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 636705404233) ^ 4977 = 511243980312 := by
        calc
          (5 : ZMod 636705404233) ^ 4977 = (5 : ZMod 636705404233) ^ (2488 + 2488 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 2488 * (5 : ZMod 636705404233) ^ 2488) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 511243980312 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 636705404233) ^ 9954 = 85533347624 := by
        calc
          (5 : ZMod 636705404233) ^ 9954 = (5 : ZMod 636705404233) ^ (4977 + 4977) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 4977 * (5 : ZMod 636705404233) ^ 4977 := by rw [pow_add]
          _ = 85533347624 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 636705404233) ^ 19908 = 597983540011 := by
        calc
          (5 : ZMod 636705404233) ^ 19908 = (5 : ZMod 636705404233) ^ (9954 + 9954) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 9954 * (5 : ZMod 636705404233) ^ 9954 := by rw [pow_add]
          _ = 597983540011 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 636705404233) ^ 39817 = 367953761264 := by
        calc
          (5 : ZMod 636705404233) ^ 39817 = (5 : ZMod 636705404233) ^ (19908 + 19908 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 19908 * (5 : ZMod 636705404233) ^ 19908) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 367953761264 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 636705404233) ^ 79634 = 262054018257 := by
        calc
          (5 : ZMod 636705404233) ^ 79634 = (5 : ZMod 636705404233) ^ (39817 + 39817) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 39817 * (5 : ZMod 636705404233) ^ 39817 := by rw [pow_add]
          _ = 262054018257 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 636705404233) ^ 159268 = 681395391 := by
        calc
          (5 : ZMod 636705404233) ^ 159268 = (5 : ZMod 636705404233) ^ (79634 + 79634) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 79634 * (5 : ZMod 636705404233) ^ 79634 := by rw [pow_add]
          _ = 681395391 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 636705404233) ^ 318536 = 90590446155 := by
        calc
          (5 : ZMod 636705404233) ^ 318536 = (5 : ZMod 636705404233) ^ (159268 + 159268) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 159268 * (5 : ZMod 636705404233) ^ 159268 := by rw [pow_add]
          _ = 90590446155 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 636705404233) ^ 637072 = 295616200810 := by
        calc
          (5 : ZMod 636705404233) ^ 637072 = (5 : ZMod 636705404233) ^ (318536 + 318536) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 318536 * (5 : ZMod 636705404233) ^ 318536 := by rw [pow_add]
          _ = 295616200810 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 636705404233) ^ 1274144 = 119240733511 := by
        calc
          (5 : ZMod 636705404233) ^ 1274144 = (5 : ZMod 636705404233) ^ (637072 + 637072) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 637072 * (5 : ZMod 636705404233) ^ 637072 := by rw [pow_add]
          _ = 119240733511 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 636705404233) ^ 2548289 = 460092194603 := by
        calc
          (5 : ZMod 636705404233) ^ 2548289 = (5 : ZMod 636705404233) ^ (1274144 + 1274144 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1274144 * (5 : ZMod 636705404233) ^ 1274144) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 460092194603 := by rw [factor_3_20]; decide
      have factor_3_22 : (5 : ZMod 636705404233) ^ 5096578 = 281668571658 := by
        calc
          (5 : ZMod 636705404233) ^ 5096578 = (5 : ZMod 636705404233) ^ (2548289 + 2548289) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 2548289 * (5 : ZMod 636705404233) ^ 2548289 := by rw [pow_add]
          _ = 281668571658 := by rw [factor_3_21]; decide
      have factor_3_23 : (5 : ZMod 636705404233) ^ 10193157 = 409082994454 := by
        calc
          (5 : ZMod 636705404233) ^ 10193157 = (5 : ZMod 636705404233) ^ (5096578 + 5096578 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 5096578 * (5 : ZMod 636705404233) ^ 5096578) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 409082994454 := by rw [factor_3_22]; decide
      have factor_3_24 : (5 : ZMod 636705404233) ^ 20386315 = 358533045842 := by
        calc
          (5 : ZMod 636705404233) ^ 20386315 = (5 : ZMod 636705404233) ^ (10193157 + 10193157 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 10193157 * (5 : ZMod 636705404233) ^ 10193157) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 358533045842 := by rw [factor_3_23]; decide
      have factor_3_25 : (5 : ZMod 636705404233) ^ 40772630 = 317332559659 := by
        calc
          (5 : ZMod 636705404233) ^ 40772630 = (5 : ZMod 636705404233) ^ (20386315 + 20386315) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 20386315 * (5 : ZMod 636705404233) ^ 20386315 := by rw [pow_add]
          _ = 317332559659 := by rw [factor_3_24]; decide
      have factor_3_26 : (5 : ZMod 636705404233) ^ 81545261 = 377389301128 := by
        calc
          (5 : ZMod 636705404233) ^ 81545261 = (5 : ZMod 636705404233) ^ (40772630 + 40772630 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 40772630 * (5 : ZMod 636705404233) ^ 40772630) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 377389301128 := by rw [factor_3_25]; decide
      have factor_3_27 : (5 : ZMod 636705404233) ^ 163090523 = 410702510039 := by
        calc
          (5 : ZMod 636705404233) ^ 163090523 = (5 : ZMod 636705404233) ^ (81545261 + 81545261 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 81545261 * (5 : ZMod 636705404233) ^ 81545261) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 410702510039 := by rw [factor_3_26]; decide
      have factor_3_28 : (5 : ZMod 636705404233) ^ 326181047 = 419906581845 := by
        calc
          (5 : ZMod 636705404233) ^ 326181047 = (5 : ZMod 636705404233) ^ (163090523 + 163090523 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 163090523 * (5 : ZMod 636705404233) ^ 163090523) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 419906581845 := by rw [factor_3_27]; decide
      have factor_3_29 : (5 : ZMod 636705404233) ^ 652362094 = 465266677945 := by
        calc
          (5 : ZMod 636705404233) ^ 652362094 = (5 : ZMod 636705404233) ^ (326181047 + 326181047) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 326181047 * (5 : ZMod 636705404233) ^ 326181047 := by rw [pow_add]
          _ = 465266677945 := by rw [factor_3_28]; decide
      have factor_3_30 : (5 : ZMod 636705404233) ^ 1304724189 = 611317696940 := by
        calc
          (5 : ZMod 636705404233) ^ 1304724189 = (5 : ZMod 636705404233) ^ (652362094 + 652362094 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 652362094 * (5 : ZMod 636705404233) ^ 652362094) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 611317696940 := by rw [factor_3_29]; decide
      have factor_3_31 : (5 : ZMod 636705404233) ^ 2609448378 = 442961062821 := by
        calc
          (5 : ZMod 636705404233) ^ 2609448378 = (5 : ZMod 636705404233) ^ (1304724189 + 1304724189) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1304724189 * (5 : ZMod 636705404233) ^ 1304724189 := by rw [pow_add]
          _ = 442961062821 := by rw [factor_3_30]; decide
      have factor_3_32 : (5 : ZMod 636705404233) ^ 5218896756 = 374878084183 := by
        calc
          (5 : ZMod 636705404233) ^ 5218896756 = (5 : ZMod 636705404233) ^ (2609448378 + 2609448378) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 2609448378 * (5 : ZMod 636705404233) ^ 2609448378 := by rw [pow_add]
          _ = 374878084183 := by rw [factor_3_31]; decide
      have factor_3_33 : (5 : ZMod 636705404233) ^ 10437793512 = 247287076198 := by
        calc
          (5 : ZMod 636705404233) ^ 10437793512 = (5 : ZMod 636705404233) ^ (5218896756 + 5218896756) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 5218896756 * (5 : ZMod 636705404233) ^ 5218896756 := by rw [pow_add]
          _ = 247287076198 := by rw [factor_3_32]; decide
      change (5 : ZMod 636705404233) ^ 10437793512 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (5 : ZMod 636705404233) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 636705404233) ^ 3 = 125 := by
        calc
          (5 : ZMod 636705404233) ^ 3 = (5 : ZMod 636705404233) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 1 * (5 : ZMod 636705404233) ^ 1) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 636705404233) ^ 7 = 78125 := by
        calc
          (5 : ZMod 636705404233) ^ 7 = (5 : ZMod 636705404233) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 3 * (5 : ZMod 636705404233) ^ 3) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 636705404233) ^ 15 = 30517578125 := by
        calc
          (5 : ZMod 636705404233) ^ 15 = (5 : ZMod 636705404233) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 7 * (5 : ZMod 636705404233) ^ 7) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 30517578125 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 636705404233) ^ 30 = 191007934201 := by
        calc
          (5 : ZMod 636705404233) ^ 30 = (5 : ZMod 636705404233) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 15 * (5 : ZMod 636705404233) ^ 15 := by rw [pow_add]
          _ = 191007934201 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 636705404233) ^ 61 = 577118328673 := by
        calc
          (5 : ZMod 636705404233) ^ 61 = (5 : ZMod 636705404233) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 30 * (5 : ZMod 636705404233) ^ 30) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 577118328673 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 636705404233) ^ 122 = 244475420727 := by
        calc
          (5 : ZMod 636705404233) ^ 122 = (5 : ZMod 636705404233) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 61 * (5 : ZMod 636705404233) ^ 61 := by rw [pow_add]
          _ = 244475420727 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 636705404233) ^ 245 = 591749778355 := by
        calc
          (5 : ZMod 636705404233) ^ 245 = (5 : ZMod 636705404233) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 122 * (5 : ZMod 636705404233) ^ 122) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 591749778355 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 636705404233) ^ 491 = 502868137442 := by
        calc
          (5 : ZMod 636705404233) ^ 491 = (5 : ZMod 636705404233) ^ (245 + 245 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 245 * (5 : ZMod 636705404233) ^ 245) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 502868137442 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 636705404233) ^ 983 = 402043937430 := by
        calc
          (5 : ZMod 636705404233) ^ 983 = (5 : ZMod 636705404233) ^ (491 + 491 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 491 * (5 : ZMod 636705404233) ^ 491) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 402043937430 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 636705404233) ^ 1967 = 29599664025 := by
        calc
          (5 : ZMod 636705404233) ^ 1967 = (5 : ZMod 636705404233) ^ (983 + 983 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 983 * (5 : ZMod 636705404233) ^ 983) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 29599664025 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 636705404233) ^ 3934 = 18349054883 := by
        calc
          (5 : ZMod 636705404233) ^ 3934 = (5 : ZMod 636705404233) ^ (1967 + 1967) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 1967 * (5 : ZMod 636705404233) ^ 1967 := by rw [pow_add]
          _ = 18349054883 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 636705404233) ^ 7869 = 170571090836 := by
        calc
          (5 : ZMod 636705404233) ^ 7869 = (5 : ZMod 636705404233) ^ (3934 + 3934 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = ((5 : ZMod 636705404233) ^ 3934 * (5 : ZMod 636705404233) ^ 3934) * (5 : ZMod 636705404233) := by rw [pow_succ, pow_add]
          _ = 170571090836 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 636705404233) ^ 15738 = 79646972785 := by
        calc
          (5 : ZMod 636705404233) ^ 15738 = (5 : ZMod 636705404233) ^ (7869 + 7869) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 7869 * (5 : ZMod 636705404233) ^ 7869 := by rw [pow_add]
          _ = 79646972785 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 636705404233) ^ 31476 = 513298502853 := by
        calc
          (5 : ZMod 636705404233) ^ 31476 = (5 : ZMod 636705404233) ^ (15738 + 15738) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 15738 * (5 : ZMod 636705404233) ^ 15738 := by rw [pow_add]
          _ = 513298502853 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 636705404233) ^ 62952 = 57655294978 := by
        calc
          (5 : ZMod 636705404233) ^ 62952 = (5 : ZMod 636705404233) ^ (31476 + 31476) :=
            congrArg (fun n : ℕ => (5 : ZMod 636705404233) ^ n) (by norm_num)
          _ = (5 : ZMod 636705404233) ^ 31476 * (5 : ZMod 636705404233) ^ 31476 := by rw [pow_add]
          _ = 57655294978 := by rw [factor_4_14]; decide
      change (5 : ZMod 636705404233) ^ 62952 ≠ 1
      rw [factor_4_15]
      decide

#print axioms prime_lucas_636705404233

end TotientTailPeriodKiller
end Erdos249257
