import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime215985101

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1732632480223 : Nat.Prime 1732632480223 := by
  apply lucas_primality 1732632480223 (3 : ZMod 1732632480223)
  ·
      have fermat_0 : (3 : ZMod 1732632480223) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 1732632480223) ^ 3 = 27 := by
        calc
          (3 : ZMod 1732632480223) ^ 3 = (3 : ZMod 1732632480223) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1 * (3 : ZMod 1732632480223) ^ 1) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 1732632480223) ^ 6 = 729 := by
        calc
          (3 : ZMod 1732632480223) ^ 6 = (3 : ZMod 1732632480223) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 3 * (3 : ZMod 1732632480223) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 1732632480223) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1732632480223) ^ 12 = (3 : ZMod 1732632480223) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 6 * (3 : ZMod 1732632480223) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 1732632480223) ^ 25 = 847288609443 := by
        calc
          (3 : ZMod 1732632480223) ^ 25 = (3 : ZMod 1732632480223) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 12 * (3 : ZMod 1732632480223) ^ 12) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 847288609443 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 1732632480223) ^ 50 = 426892536795 := by
        calc
          (3 : ZMod 1732632480223) ^ 50 = (3 : ZMod 1732632480223) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 25 * (3 : ZMod 1732632480223) ^ 25 := by rw [pow_add]
          _ = 426892536795 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 1732632480223) ^ 100 = 52180976819 := by
        calc
          (3 : ZMod 1732632480223) ^ 100 = (3 : ZMod 1732632480223) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 50 * (3 : ZMod 1732632480223) ^ 50 := by rw [pow_add]
          _ = 52180976819 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 1732632480223) ^ 201 = 658232087674 := by
        calc
          (3 : ZMod 1732632480223) ^ 201 = (3 : ZMod 1732632480223) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 100 * (3 : ZMod 1732632480223) ^ 100) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 658232087674 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 1732632480223) ^ 403 = 799406789565 := by
        calc
          (3 : ZMod 1732632480223) ^ 403 = (3 : ZMod 1732632480223) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 201 * (3 : ZMod 1732632480223) ^ 201) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 799406789565 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 1732632480223) ^ 806 = 20332276380 := by
        calc
          (3 : ZMod 1732632480223) ^ 806 = (3 : ZMod 1732632480223) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 403 * (3 : ZMod 1732632480223) ^ 403 := by rw [pow_add]
          _ = 20332276380 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 1732632480223) ^ 1613 = 1528062667681 := by
        calc
          (3 : ZMod 1732632480223) ^ 1613 = (3 : ZMod 1732632480223) ^ (806 + 806 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 806 * (3 : ZMod 1732632480223) ^ 806) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1528062667681 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 1732632480223) ^ 3227 = 656613261585 := by
        calc
          (3 : ZMod 1732632480223) ^ 3227 = (3 : ZMod 1732632480223) ^ (1613 + 1613 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1613 * (3 : ZMod 1732632480223) ^ 1613) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 656613261585 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 1732632480223) ^ 6454 = 1340343118525 := by
        calc
          (3 : ZMod 1732632480223) ^ 6454 = (3 : ZMod 1732632480223) ^ (3227 + 3227) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 3227 * (3 : ZMod 1732632480223) ^ 3227 := by rw [pow_add]
          _ = 1340343118525 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 1732632480223) ^ 12909 = 1172867709652 := by
        calc
          (3 : ZMod 1732632480223) ^ 12909 = (3 : ZMod 1732632480223) ^ (6454 + 6454 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 6454 * (3 : ZMod 1732632480223) ^ 6454) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1172867709652 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 1732632480223) ^ 25818 = 1382721921495 := by
        calc
          (3 : ZMod 1732632480223) ^ 25818 = (3 : ZMod 1732632480223) ^ (12909 + 12909) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 12909 * (3 : ZMod 1732632480223) ^ 12909 := by rw [pow_add]
          _ = 1382721921495 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 1732632480223) ^ 51636 = 1303839098800 := by
        calc
          (3 : ZMod 1732632480223) ^ 51636 = (3 : ZMod 1732632480223) ^ (25818 + 25818) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 25818 * (3 : ZMod 1732632480223) ^ 25818 := by rw [pow_add]
          _ = 1303839098800 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 1732632480223) ^ 103272 = 449594140873 := by
        calc
          (3 : ZMod 1732632480223) ^ 103272 = (3 : ZMod 1732632480223) ^ (51636 + 51636) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 51636 * (3 : ZMod 1732632480223) ^ 51636 := by rw [pow_add]
          _ = 449594140873 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 1732632480223) ^ 206545 = 967565285449 := by
        calc
          (3 : ZMod 1732632480223) ^ 206545 = (3 : ZMod 1732632480223) ^ (103272 + 103272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 103272 * (3 : ZMod 1732632480223) ^ 103272) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 967565285449 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 1732632480223) ^ 413091 = 746400260073 := by
        calc
          (3 : ZMod 1732632480223) ^ 413091 = (3 : ZMod 1732632480223) ^ (206545 + 206545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 206545 * (3 : ZMod 1732632480223) ^ 206545) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 746400260073 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 1732632480223) ^ 826183 = 1409989407611 := by
        calc
          (3 : ZMod 1732632480223) ^ 826183 = (3 : ZMod 1732632480223) ^ (413091 + 413091 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 413091 * (3 : ZMod 1732632480223) ^ 413091) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1409989407611 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 1732632480223) ^ 1652367 = 1062896656696 := by
        calc
          (3 : ZMod 1732632480223) ^ 1652367 = (3 : ZMod 1732632480223) ^ (826183 + 826183 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 826183 * (3 : ZMod 1732632480223) ^ 826183) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1062896656696 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 1732632480223) ^ 3304734 = 858939028327 := by
        calc
          (3 : ZMod 1732632480223) ^ 3304734 = (3 : ZMod 1732632480223) ^ (1652367 + 1652367) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1652367 * (3 : ZMod 1732632480223) ^ 1652367 := by rw [pow_add]
          _ = 858939028327 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 1732632480223) ^ 6609468 = 1388376321483 := by
        calc
          (3 : ZMod 1732632480223) ^ 6609468 = (3 : ZMod 1732632480223) ^ (3304734 + 3304734) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 3304734 * (3 : ZMod 1732632480223) ^ 3304734 := by rw [pow_add]
          _ = 1388376321483 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 1732632480223) ^ 13218936 = 725631346000 := by
        calc
          (3 : ZMod 1732632480223) ^ 13218936 = (3 : ZMod 1732632480223) ^ (6609468 + 6609468) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 6609468 * (3 : ZMod 1732632480223) ^ 6609468 := by rw [pow_add]
          _ = 725631346000 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 1732632480223) ^ 26437873 = 1074346815591 := by
        calc
          (3 : ZMod 1732632480223) ^ 26437873 = (3 : ZMod 1732632480223) ^ (13218936 + 13218936 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 13218936 * (3 : ZMod 1732632480223) ^ 13218936) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1074346815591 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 1732632480223) ^ 52875747 = 1605662709618 := by
        calc
          (3 : ZMod 1732632480223) ^ 52875747 = (3 : ZMod 1732632480223) ^ (26437873 + 26437873 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 26437873 * (3 : ZMod 1732632480223) ^ 26437873) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1605662709618 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 1732632480223) ^ 105751494 = 142352777059 := by
        calc
          (3 : ZMod 1732632480223) ^ 105751494 = (3 : ZMod 1732632480223) ^ (52875747 + 52875747) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 52875747 * (3 : ZMod 1732632480223) ^ 52875747 := by rw [pow_add]
          _ = 142352777059 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 1732632480223) ^ 211502988 = 1208445735450 := by
        calc
          (3 : ZMod 1732632480223) ^ 211502988 = (3 : ZMod 1732632480223) ^ (105751494 + 105751494) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 105751494 * (3 : ZMod 1732632480223) ^ 105751494 := by rw [pow_add]
          _ = 1208445735450 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 1732632480223) ^ 423005976 = 558415178957 := by
        calc
          (3 : ZMod 1732632480223) ^ 423005976 = (3 : ZMod 1732632480223) ^ (211502988 + 211502988) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 211502988 * (3 : ZMod 1732632480223) ^ 211502988 := by rw [pow_add]
          _ = 558415178957 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 1732632480223) ^ 846011953 = 118044694608 := by
        calc
          (3 : ZMod 1732632480223) ^ 846011953 = (3 : ZMod 1732632480223) ^ (423005976 + 423005976 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 423005976 * (3 : ZMod 1732632480223) ^ 423005976) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 118044694608 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 1732632480223) ^ 1692023906 = 189393667339 := by
        calc
          (3 : ZMod 1732632480223) ^ 1692023906 = (3 : ZMod 1732632480223) ^ (846011953 + 846011953) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 846011953 * (3 : ZMod 1732632480223) ^ 846011953 := by rw [pow_add]
          _ = 189393667339 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 1732632480223) ^ 3384047812 = 372977608840 := by
        calc
          (3 : ZMod 1732632480223) ^ 3384047812 = (3 : ZMod 1732632480223) ^ (1692023906 + 1692023906) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1692023906 * (3 : ZMod 1732632480223) ^ 1692023906 := by rw [pow_add]
          _ = 372977608840 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 1732632480223) ^ 6768095625 = 1127944991437 := by
        calc
          (3 : ZMod 1732632480223) ^ 6768095625 = (3 : ZMod 1732632480223) ^ (3384047812 + 3384047812 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 3384047812 * (3 : ZMod 1732632480223) ^ 3384047812) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1127944991437 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 1732632480223) ^ 13536191251 = 1127543278561 := by
        calc
          (3 : ZMod 1732632480223) ^ 13536191251 = (3 : ZMod 1732632480223) ^ (6768095625 + 6768095625 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 6768095625 * (3 : ZMod 1732632480223) ^ 6768095625) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1127543278561 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 1732632480223) ^ 27072382503 = 611136453562 := by
        calc
          (3 : ZMod 1732632480223) ^ 27072382503 = (3 : ZMod 1732632480223) ^ (13536191251 + 13536191251 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 13536191251 * (3 : ZMod 1732632480223) ^ 13536191251) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 611136453562 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 1732632480223) ^ 54144765006 = 162463992046 := by
        calc
          (3 : ZMod 1732632480223) ^ 54144765006 = (3 : ZMod 1732632480223) ^ (27072382503 + 27072382503) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 27072382503 * (3 : ZMod 1732632480223) ^ 27072382503 := by rw [pow_add]
          _ = 162463992046 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 1732632480223) ^ 108289530013 = 434798956454 := by
        calc
          (3 : ZMod 1732632480223) ^ 108289530013 = (3 : ZMod 1732632480223) ^ (54144765006 + 54144765006 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 54144765006 * (3 : ZMod 1732632480223) ^ 54144765006) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 434798956454 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 1732632480223) ^ 216579060027 = 690321846298 := by
        calc
          (3 : ZMod 1732632480223) ^ 216579060027 = (3 : ZMod 1732632480223) ^ (108289530013 + 108289530013 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 108289530013 * (3 : ZMod 1732632480223) ^ 108289530013) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 690321846298 := by rw [fermat_36]; decide
      have fermat_38 : (3 : ZMod 1732632480223) ^ 433158120055 = 538500546482 := by
        calc
          (3 : ZMod 1732632480223) ^ 433158120055 = (3 : ZMod 1732632480223) ^ (216579060027 + 216579060027 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 216579060027 * (3 : ZMod 1732632480223) ^ 216579060027) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 538500546482 := by rw [fermat_37]; decide
      have fermat_39 : (3 : ZMod 1732632480223) ^ 866316240111 = 1732632480222 := by
        calc
          (3 : ZMod 1732632480223) ^ 866316240111 = (3 : ZMod 1732632480223) ^ (433158120055 + 433158120055 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 433158120055 * (3 : ZMod 1732632480223) ^ 433158120055) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1732632480222 := by rw [fermat_38]; decide
      have fermat_40 : (3 : ZMod 1732632480223) ^ 1732632480222 = 1 := by
        calc
          (3 : ZMod 1732632480223) ^ 1732632480222 = (3 : ZMod 1732632480223) ^ (866316240111 + 866316240111) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 866316240111 * (3 : ZMod 1732632480223) ^ 866316240111 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (191, 1), (215985101, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (191, 1), (215985101, 1)] : List FactorBlock).map factorBlockValue).prod = 1732632480223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_215985101) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 1732632480223) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 1732632480223) ^ 3 = 27 := by
        calc
          (3 : ZMod 1732632480223) ^ 3 = (3 : ZMod 1732632480223) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1 * (3 : ZMod 1732632480223) ^ 1) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 1732632480223) ^ 6 = 729 := by
        calc
          (3 : ZMod 1732632480223) ^ 6 = (3 : ZMod 1732632480223) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 3 * (3 : ZMod 1732632480223) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 1732632480223) ^ 12 = 531441 := by
        calc
          (3 : ZMod 1732632480223) ^ 12 = (3 : ZMod 1732632480223) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 6 * (3 : ZMod 1732632480223) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 1732632480223) ^ 25 = 847288609443 := by
        calc
          (3 : ZMod 1732632480223) ^ 25 = (3 : ZMod 1732632480223) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 12 * (3 : ZMod 1732632480223) ^ 12) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 847288609443 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 1732632480223) ^ 50 = 426892536795 := by
        calc
          (3 : ZMod 1732632480223) ^ 50 = (3 : ZMod 1732632480223) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 25 * (3 : ZMod 1732632480223) ^ 25 := by rw [pow_add]
          _ = 426892536795 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 1732632480223) ^ 100 = 52180976819 := by
        calc
          (3 : ZMod 1732632480223) ^ 100 = (3 : ZMod 1732632480223) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 50 * (3 : ZMod 1732632480223) ^ 50 := by rw [pow_add]
          _ = 52180976819 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 1732632480223) ^ 201 = 658232087674 := by
        calc
          (3 : ZMod 1732632480223) ^ 201 = (3 : ZMod 1732632480223) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 100 * (3 : ZMod 1732632480223) ^ 100) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 658232087674 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 1732632480223) ^ 403 = 799406789565 := by
        calc
          (3 : ZMod 1732632480223) ^ 403 = (3 : ZMod 1732632480223) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 201 * (3 : ZMod 1732632480223) ^ 201) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 799406789565 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 1732632480223) ^ 806 = 20332276380 := by
        calc
          (3 : ZMod 1732632480223) ^ 806 = (3 : ZMod 1732632480223) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 403 * (3 : ZMod 1732632480223) ^ 403 := by rw [pow_add]
          _ = 20332276380 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 1732632480223) ^ 1613 = 1528062667681 := by
        calc
          (3 : ZMod 1732632480223) ^ 1613 = (3 : ZMod 1732632480223) ^ (806 + 806 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 806 * (3 : ZMod 1732632480223) ^ 806) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1528062667681 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 1732632480223) ^ 3227 = 656613261585 := by
        calc
          (3 : ZMod 1732632480223) ^ 3227 = (3 : ZMod 1732632480223) ^ (1613 + 1613 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1613 * (3 : ZMod 1732632480223) ^ 1613) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 656613261585 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 1732632480223) ^ 6454 = 1340343118525 := by
        calc
          (3 : ZMod 1732632480223) ^ 6454 = (3 : ZMod 1732632480223) ^ (3227 + 3227) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 3227 * (3 : ZMod 1732632480223) ^ 3227 := by rw [pow_add]
          _ = 1340343118525 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 1732632480223) ^ 12909 = 1172867709652 := by
        calc
          (3 : ZMod 1732632480223) ^ 12909 = (3 : ZMod 1732632480223) ^ (6454 + 6454 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 6454 * (3 : ZMod 1732632480223) ^ 6454) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1172867709652 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 1732632480223) ^ 25818 = 1382721921495 := by
        calc
          (3 : ZMod 1732632480223) ^ 25818 = (3 : ZMod 1732632480223) ^ (12909 + 12909) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 12909 * (3 : ZMod 1732632480223) ^ 12909 := by rw [pow_add]
          _ = 1382721921495 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 1732632480223) ^ 51636 = 1303839098800 := by
        calc
          (3 : ZMod 1732632480223) ^ 51636 = (3 : ZMod 1732632480223) ^ (25818 + 25818) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 25818 * (3 : ZMod 1732632480223) ^ 25818 := by rw [pow_add]
          _ = 1303839098800 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 1732632480223) ^ 103272 = 449594140873 := by
        calc
          (3 : ZMod 1732632480223) ^ 103272 = (3 : ZMod 1732632480223) ^ (51636 + 51636) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 51636 * (3 : ZMod 1732632480223) ^ 51636 := by rw [pow_add]
          _ = 449594140873 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 1732632480223) ^ 206545 = 967565285449 := by
        calc
          (3 : ZMod 1732632480223) ^ 206545 = (3 : ZMod 1732632480223) ^ (103272 + 103272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 103272 * (3 : ZMod 1732632480223) ^ 103272) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 967565285449 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 1732632480223) ^ 413091 = 746400260073 := by
        calc
          (3 : ZMod 1732632480223) ^ 413091 = (3 : ZMod 1732632480223) ^ (206545 + 206545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 206545 * (3 : ZMod 1732632480223) ^ 206545) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 746400260073 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 1732632480223) ^ 826183 = 1409989407611 := by
        calc
          (3 : ZMod 1732632480223) ^ 826183 = (3 : ZMod 1732632480223) ^ (413091 + 413091 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 413091 * (3 : ZMod 1732632480223) ^ 413091) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1409989407611 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 1732632480223) ^ 1652367 = 1062896656696 := by
        calc
          (3 : ZMod 1732632480223) ^ 1652367 = (3 : ZMod 1732632480223) ^ (826183 + 826183 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 826183 * (3 : ZMod 1732632480223) ^ 826183) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1062896656696 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 1732632480223) ^ 3304734 = 858939028327 := by
        calc
          (3 : ZMod 1732632480223) ^ 3304734 = (3 : ZMod 1732632480223) ^ (1652367 + 1652367) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1652367 * (3 : ZMod 1732632480223) ^ 1652367 := by rw [pow_add]
          _ = 858939028327 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 1732632480223) ^ 6609468 = 1388376321483 := by
        calc
          (3 : ZMod 1732632480223) ^ 6609468 = (3 : ZMod 1732632480223) ^ (3304734 + 3304734) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 3304734 * (3 : ZMod 1732632480223) ^ 3304734 := by rw [pow_add]
          _ = 1388376321483 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 1732632480223) ^ 13218936 = 725631346000 := by
        calc
          (3 : ZMod 1732632480223) ^ 13218936 = (3 : ZMod 1732632480223) ^ (6609468 + 6609468) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 6609468 * (3 : ZMod 1732632480223) ^ 6609468 := by rw [pow_add]
          _ = 725631346000 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 1732632480223) ^ 26437873 = 1074346815591 := by
        calc
          (3 : ZMod 1732632480223) ^ 26437873 = (3 : ZMod 1732632480223) ^ (13218936 + 13218936 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 13218936 * (3 : ZMod 1732632480223) ^ 13218936) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1074346815591 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 1732632480223) ^ 52875747 = 1605662709618 := by
        calc
          (3 : ZMod 1732632480223) ^ 52875747 = (3 : ZMod 1732632480223) ^ (26437873 + 26437873 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 26437873 * (3 : ZMod 1732632480223) ^ 26437873) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1605662709618 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 1732632480223) ^ 105751494 = 142352777059 := by
        calc
          (3 : ZMod 1732632480223) ^ 105751494 = (3 : ZMod 1732632480223) ^ (52875747 + 52875747) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 52875747 * (3 : ZMod 1732632480223) ^ 52875747 := by rw [pow_add]
          _ = 142352777059 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 1732632480223) ^ 211502988 = 1208445735450 := by
        calc
          (3 : ZMod 1732632480223) ^ 211502988 = (3 : ZMod 1732632480223) ^ (105751494 + 105751494) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 105751494 * (3 : ZMod 1732632480223) ^ 105751494 := by rw [pow_add]
          _ = 1208445735450 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 1732632480223) ^ 423005976 = 558415178957 := by
        calc
          (3 : ZMod 1732632480223) ^ 423005976 = (3 : ZMod 1732632480223) ^ (211502988 + 211502988) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 211502988 * (3 : ZMod 1732632480223) ^ 211502988 := by rw [pow_add]
          _ = 558415178957 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 1732632480223) ^ 846011953 = 118044694608 := by
        calc
          (3 : ZMod 1732632480223) ^ 846011953 = (3 : ZMod 1732632480223) ^ (423005976 + 423005976 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 423005976 * (3 : ZMod 1732632480223) ^ 423005976) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 118044694608 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 1732632480223) ^ 1692023906 = 189393667339 := by
        calc
          (3 : ZMod 1732632480223) ^ 1692023906 = (3 : ZMod 1732632480223) ^ (846011953 + 846011953) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 846011953 * (3 : ZMod 1732632480223) ^ 846011953 := by rw [pow_add]
          _ = 189393667339 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 1732632480223) ^ 3384047812 = 372977608840 := by
        calc
          (3 : ZMod 1732632480223) ^ 3384047812 = (3 : ZMod 1732632480223) ^ (1692023906 + 1692023906) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1692023906 * (3 : ZMod 1732632480223) ^ 1692023906 := by rw [pow_add]
          _ = 372977608840 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 1732632480223) ^ 6768095625 = 1127944991437 := by
        calc
          (3 : ZMod 1732632480223) ^ 6768095625 = (3 : ZMod 1732632480223) ^ (3384047812 + 3384047812 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 3384047812 * (3 : ZMod 1732632480223) ^ 3384047812) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1127944991437 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 1732632480223) ^ 13536191251 = 1127543278561 := by
        calc
          (3 : ZMod 1732632480223) ^ 13536191251 = (3 : ZMod 1732632480223) ^ (6768095625 + 6768095625 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 6768095625 * (3 : ZMod 1732632480223) ^ 6768095625) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1127543278561 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 1732632480223) ^ 27072382503 = 611136453562 := by
        calc
          (3 : ZMod 1732632480223) ^ 27072382503 = (3 : ZMod 1732632480223) ^ (13536191251 + 13536191251 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 13536191251 * (3 : ZMod 1732632480223) ^ 13536191251) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 611136453562 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 1732632480223) ^ 54144765006 = 162463992046 := by
        calc
          (3 : ZMod 1732632480223) ^ 54144765006 = (3 : ZMod 1732632480223) ^ (27072382503 + 27072382503) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 27072382503 * (3 : ZMod 1732632480223) ^ 27072382503 := by rw [pow_add]
          _ = 162463992046 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 1732632480223) ^ 108289530013 = 434798956454 := by
        calc
          (3 : ZMod 1732632480223) ^ 108289530013 = (3 : ZMod 1732632480223) ^ (54144765006 + 54144765006 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 54144765006 * (3 : ZMod 1732632480223) ^ 54144765006) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 434798956454 := by rw [factor_0_35]; decide
      have factor_0_37 : (3 : ZMod 1732632480223) ^ 216579060027 = 690321846298 := by
        calc
          (3 : ZMod 1732632480223) ^ 216579060027 = (3 : ZMod 1732632480223) ^ (108289530013 + 108289530013 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 108289530013 * (3 : ZMod 1732632480223) ^ 108289530013) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 690321846298 := by rw [factor_0_36]; decide
      have factor_0_38 : (3 : ZMod 1732632480223) ^ 433158120055 = 538500546482 := by
        calc
          (3 : ZMod 1732632480223) ^ 433158120055 = (3 : ZMod 1732632480223) ^ (216579060027 + 216579060027 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 216579060027 * (3 : ZMod 1732632480223) ^ 216579060027) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 538500546482 := by rw [factor_0_37]; decide
      have factor_0_39 : (3 : ZMod 1732632480223) ^ 866316240111 = 1732632480222 := by
        calc
          (3 : ZMod 1732632480223) ^ 866316240111 = (3 : ZMod 1732632480223) ^ (433158120055 + 433158120055 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 433158120055 * (3 : ZMod 1732632480223) ^ 433158120055) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1732632480222 := by rw [factor_0_38]; decide
      change (3 : ZMod 1732632480223) ^ 866316240111 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (3 : ZMod 1732632480223) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 1732632480223) ^ 2 = 9 := by
        calc
          (3 : ZMod 1732632480223) ^ 2 = (3 : ZMod 1732632480223) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1 * (3 : ZMod 1732632480223) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 1732632480223) ^ 4 = 81 := by
        calc
          (3 : ZMod 1732632480223) ^ 4 = (3 : ZMod 1732632480223) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 2 * (3 : ZMod 1732632480223) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 1732632480223) ^ 8 = 6561 := by
        calc
          (3 : ZMod 1732632480223) ^ 8 = (3 : ZMod 1732632480223) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 4 * (3 : ZMod 1732632480223) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 1732632480223) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 1732632480223) ^ 16 = (3 : ZMod 1732632480223) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 8 * (3 : ZMod 1732632480223) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 1732632480223) ^ 33 = 775570000139 := by
        calc
          (3 : ZMod 1732632480223) ^ 33 = (3 : ZMod 1732632480223) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 16 * (3 : ZMod 1732632480223) ^ 16) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 775570000139 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 1732632480223) ^ 67 = 491522694442 := by
        calc
          (3 : ZMod 1732632480223) ^ 67 = (3 : ZMod 1732632480223) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 33 * (3 : ZMod 1732632480223) ^ 33) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 491522694442 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 1732632480223) ^ 134 = 19405770972 := by
        calc
          (3 : ZMod 1732632480223) ^ 134 = (3 : ZMod 1732632480223) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 67 * (3 : ZMod 1732632480223) ^ 67 := by rw [pow_add]
          _ = 19405770972 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 1732632480223) ^ 268 = 868448774011 := by
        calc
          (3 : ZMod 1732632480223) ^ 268 = (3 : ZMod 1732632480223) ^ (134 + 134) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 134 * (3 : ZMod 1732632480223) ^ 134 := by rw [pow_add]
          _ = 868448774011 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 1732632480223) ^ 537 = 458090040753 := by
        calc
          (3 : ZMod 1732632480223) ^ 537 = (3 : ZMod 1732632480223) ^ (268 + 268 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 268 * (3 : ZMod 1732632480223) ^ 268) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 458090040753 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 1732632480223) ^ 1075 = 1420625012241 := by
        calc
          (3 : ZMod 1732632480223) ^ 1075 = (3 : ZMod 1732632480223) ^ (537 + 537 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 537 * (3 : ZMod 1732632480223) ^ 537) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1420625012241 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 1732632480223) ^ 2151 = 1348561202661 := by
        calc
          (3 : ZMod 1732632480223) ^ 2151 = (3 : ZMod 1732632480223) ^ (1075 + 1075 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1075 * (3 : ZMod 1732632480223) ^ 1075) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1348561202661 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 1732632480223) ^ 4303 = 482924772086 := by
        calc
          (3 : ZMod 1732632480223) ^ 4303 = (3 : ZMod 1732632480223) ^ (2151 + 2151 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 2151 * (3 : ZMod 1732632480223) ^ 2151) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 482924772086 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 1732632480223) ^ 8606 = 52424217268 := by
        calc
          (3 : ZMod 1732632480223) ^ 8606 = (3 : ZMod 1732632480223) ^ (4303 + 4303) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 4303 * (3 : ZMod 1732632480223) ^ 4303 := by rw [pow_add]
          _ = 52424217268 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 1732632480223) ^ 17212 = 118561580764 := by
        calc
          (3 : ZMod 1732632480223) ^ 17212 = (3 : ZMod 1732632480223) ^ (8606 + 8606) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 8606 * (3 : ZMod 1732632480223) ^ 8606 := by rw [pow_add]
          _ = 118561580764 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 1732632480223) ^ 34424 = 196081119415 := by
        calc
          (3 : ZMod 1732632480223) ^ 34424 = (3 : ZMod 1732632480223) ^ (17212 + 17212) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 17212 * (3 : ZMod 1732632480223) ^ 17212 := by rw [pow_add]
          _ = 196081119415 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 1732632480223) ^ 68848 = 1595015851080 := by
        calc
          (3 : ZMod 1732632480223) ^ 68848 = (3 : ZMod 1732632480223) ^ (34424 + 34424) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 34424 * (3 : ZMod 1732632480223) ^ 34424 := by rw [pow_add]
          _ = 1595015851080 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 1732632480223) ^ 137697 = 1091924832779 := by
        calc
          (3 : ZMod 1732632480223) ^ 137697 = (3 : ZMod 1732632480223) ^ (68848 + 68848 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 68848 * (3 : ZMod 1732632480223) ^ 68848) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1091924832779 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 1732632480223) ^ 275394 = 167654395108 := by
        calc
          (3 : ZMod 1732632480223) ^ 275394 = (3 : ZMod 1732632480223) ^ (137697 + 137697) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 137697 * (3 : ZMod 1732632480223) ^ 137697 := by rw [pow_add]
          _ = 167654395108 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 1732632480223) ^ 550789 = 1321288777719 := by
        calc
          (3 : ZMod 1732632480223) ^ 550789 = (3 : ZMod 1732632480223) ^ (275394 + 275394 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 275394 * (3 : ZMod 1732632480223) ^ 275394) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1321288777719 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 1732632480223) ^ 1101578 = 1330148396469 := by
        calc
          (3 : ZMod 1732632480223) ^ 1101578 = (3 : ZMod 1732632480223) ^ (550789 + 550789) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 550789 * (3 : ZMod 1732632480223) ^ 550789 := by rw [pow_add]
          _ = 1330148396469 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 1732632480223) ^ 2203156 = 628189508250 := by
        calc
          (3 : ZMod 1732632480223) ^ 2203156 = (3 : ZMod 1732632480223) ^ (1101578 + 1101578) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1101578 * (3 : ZMod 1732632480223) ^ 1101578 := by rw [pow_add]
          _ = 628189508250 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 1732632480223) ^ 4406312 = 527608870780 := by
        calc
          (3 : ZMod 1732632480223) ^ 4406312 = (3 : ZMod 1732632480223) ^ (2203156 + 2203156) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 2203156 * (3 : ZMod 1732632480223) ^ 2203156 := by rw [pow_add]
          _ = 527608870780 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 1732632480223) ^ 8812624 = 237575700059 := by
        calc
          (3 : ZMod 1732632480223) ^ 8812624 = (3 : ZMod 1732632480223) ^ (4406312 + 4406312) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 4406312 * (3 : ZMod 1732632480223) ^ 4406312 := by rw [pow_add]
          _ = 237575700059 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 1732632480223) ^ 17625249 = 468173666188 := by
        calc
          (3 : ZMod 1732632480223) ^ 17625249 = (3 : ZMod 1732632480223) ^ (8812624 + 8812624 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 8812624 * (3 : ZMod 1732632480223) ^ 8812624) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 468173666188 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 1732632480223) ^ 35250498 = 416527380501 := by
        calc
          (3 : ZMod 1732632480223) ^ 35250498 = (3 : ZMod 1732632480223) ^ (17625249 + 17625249) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 17625249 * (3 : ZMod 1732632480223) ^ 17625249 := by rw [pow_add]
          _ = 416527380501 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 1732632480223) ^ 70500996 = 584345211311 := by
        calc
          (3 : ZMod 1732632480223) ^ 70500996 = (3 : ZMod 1732632480223) ^ (35250498 + 35250498) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 35250498 * (3 : ZMod 1732632480223) ^ 35250498 := by rw [pow_add]
          _ = 584345211311 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 1732632480223) ^ 141001992 = 1103809915717 := by
        calc
          (3 : ZMod 1732632480223) ^ 141001992 = (3 : ZMod 1732632480223) ^ (70500996 + 70500996) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 70500996 * (3 : ZMod 1732632480223) ^ 70500996 := by rw [pow_add]
          _ = 1103809915717 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 1732632480223) ^ 282003984 = 549155718596 := by
        calc
          (3 : ZMod 1732632480223) ^ 282003984 = (3 : ZMod 1732632480223) ^ (141001992 + 141001992) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 141001992 * (3 : ZMod 1732632480223) ^ 141001992 := by rw [pow_add]
          _ = 549155718596 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 1732632480223) ^ 564007968 = 996672233457 := by
        calc
          (3 : ZMod 1732632480223) ^ 564007968 = (3 : ZMod 1732632480223) ^ (282003984 + 282003984) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 282003984 * (3 : ZMod 1732632480223) ^ 282003984 := by rw [pow_add]
          _ = 996672233457 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 1732632480223) ^ 1128015937 = 1296675266787 := by
        calc
          (3 : ZMod 1732632480223) ^ 1128015937 = (3 : ZMod 1732632480223) ^ (564007968 + 564007968 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 564007968 * (3 : ZMod 1732632480223) ^ 564007968) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1296675266787 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 1732632480223) ^ 2256031875 = 636515100922 := by
        calc
          (3 : ZMod 1732632480223) ^ 2256031875 = (3 : ZMod 1732632480223) ^ (1128015937 + 1128015937 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1128015937 * (3 : ZMod 1732632480223) ^ 1128015937) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 636515100922 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 1732632480223) ^ 4512063750 = 1452402467730 := by
        calc
          (3 : ZMod 1732632480223) ^ 4512063750 = (3 : ZMod 1732632480223) ^ (2256031875 + 2256031875) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 2256031875 * (3 : ZMod 1732632480223) ^ 2256031875 := by rw [pow_add]
          _ = 1452402467730 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 1732632480223) ^ 9024127501 = 1610522627905 := by
        calc
          (3 : ZMod 1732632480223) ^ 9024127501 = (3 : ZMod 1732632480223) ^ (4512063750 + 4512063750 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 4512063750 * (3 : ZMod 1732632480223) ^ 4512063750) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1610522627905 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 1732632480223) ^ 18048255002 = 1434388651697 := by
        calc
          (3 : ZMod 1732632480223) ^ 18048255002 = (3 : ZMod 1732632480223) ^ (9024127501 + 9024127501) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 9024127501 * (3 : ZMod 1732632480223) ^ 9024127501 := by rw [pow_add]
          _ = 1434388651697 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 1732632480223) ^ 36096510004 = 1477257851378 := by
        calc
          (3 : ZMod 1732632480223) ^ 36096510004 = (3 : ZMod 1732632480223) ^ (18048255002 + 18048255002) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 18048255002 * (3 : ZMod 1732632480223) ^ 18048255002 := by rw [pow_add]
          _ = 1477257851378 := by rw [factor_1_34]; decide
      have factor_1_36 : (3 : ZMod 1732632480223) ^ 72193020009 = 97832874326 := by
        calc
          (3 : ZMod 1732632480223) ^ 72193020009 = (3 : ZMod 1732632480223) ^ (36096510004 + 36096510004 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 36096510004 * (3 : ZMod 1732632480223) ^ 36096510004) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 97832874326 := by rw [factor_1_35]; decide
      have factor_1_37 : (3 : ZMod 1732632480223) ^ 144386040018 = 1135566513353 := by
        calc
          (3 : ZMod 1732632480223) ^ 144386040018 = (3 : ZMod 1732632480223) ^ (72193020009 + 72193020009) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 72193020009 * (3 : ZMod 1732632480223) ^ 72193020009 := by rw [pow_add]
          _ = 1135566513353 := by rw [factor_1_36]; decide
      have factor_1_38 : (3 : ZMod 1732632480223) ^ 288772080037 = 1674067059835 := by
        calc
          (3 : ZMod 1732632480223) ^ 288772080037 = (3 : ZMod 1732632480223) ^ (144386040018 + 144386040018 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 144386040018 * (3 : ZMod 1732632480223) ^ 144386040018) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1674067059835 := by rw [factor_1_37]; decide
      have factor_1_39 : (3 : ZMod 1732632480223) ^ 577544160074 = 1674067059834 := by
        calc
          (3 : ZMod 1732632480223) ^ 577544160074 = (3 : ZMod 1732632480223) ^ (288772080037 + 288772080037) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 288772080037 * (3 : ZMod 1732632480223) ^ 288772080037 := by rw [pow_add]
          _ = 1674067059834 := by rw [factor_1_38]; decide
      change (3 : ZMod 1732632480223) ^ 577544160074 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (3 : ZMod 1732632480223) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 1732632480223) ^ 3 = 27 := by
        calc
          (3 : ZMod 1732632480223) ^ 3 = (3 : ZMod 1732632480223) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1 * (3 : ZMod 1732632480223) ^ 1) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 1732632480223) ^ 7 = 2187 := by
        calc
          (3 : ZMod 1732632480223) ^ 7 = (3 : ZMod 1732632480223) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 3 * (3 : ZMod 1732632480223) ^ 3) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 1732632480223) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 1732632480223) ^ 14 = (3 : ZMod 1732632480223) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 7 * (3 : ZMod 1732632480223) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 1732632480223) ^ 28 = 352570212062 := by
        calc
          (3 : ZMod 1732632480223) ^ 28 = (3 : ZMod 1732632480223) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 14 * (3 : ZMod 1732632480223) ^ 14 := by rw [pow_add]
          _ = 352570212062 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 1732632480223) ^ 57 = 1457703610691 := by
        calc
          (3 : ZMod 1732632480223) ^ 57 = (3 : ZMod 1732632480223) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 28 * (3 : ZMod 1732632480223) ^ 28) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1457703610691 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 1732632480223) ^ 115 = 183541419613 := by
        calc
          (3 : ZMod 1732632480223) ^ 115 = (3 : ZMod 1732632480223) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 57 * (3 : ZMod 1732632480223) ^ 57) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 183541419613 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 1732632480223) ^ 230 = 463337991684 := by
        calc
          (3 : ZMod 1732632480223) ^ 230 = (3 : ZMod 1732632480223) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 115 * (3 : ZMod 1732632480223) ^ 115 := by rw [pow_add]
          _ = 463337991684 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 1732632480223) ^ 461 = 759187505009 := by
        calc
          (3 : ZMod 1732632480223) ^ 461 = (3 : ZMod 1732632480223) ^ (230 + 230 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 230 * (3 : ZMod 1732632480223) ^ 230) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 759187505009 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 1732632480223) ^ 922 = 1135041175158 := by
        calc
          (3 : ZMod 1732632480223) ^ 922 = (3 : ZMod 1732632480223) ^ (461 + 461) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 461 * (3 : ZMod 1732632480223) ^ 461 := by rw [pow_add]
          _ = 1135041175158 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 1732632480223) ^ 1844 = 814534272526 := by
        calc
          (3 : ZMod 1732632480223) ^ 1844 = (3 : ZMod 1732632480223) ^ (922 + 922) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 922 * (3 : ZMod 1732632480223) ^ 922 := by rw [pow_add]
          _ = 814534272526 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 1732632480223) ^ 3688 = 1030699397137 := by
        calc
          (3 : ZMod 1732632480223) ^ 3688 = (3 : ZMod 1732632480223) ^ (1844 + 1844) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1844 * (3 : ZMod 1732632480223) ^ 1844 := by rw [pow_add]
          _ = 1030699397137 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 1732632480223) ^ 7376 = 1592907721926 := by
        calc
          (3 : ZMod 1732632480223) ^ 7376 = (3 : ZMod 1732632480223) ^ (3688 + 3688) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 3688 * (3 : ZMod 1732632480223) ^ 3688 := by rw [pow_add]
          _ = 1592907721926 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 1732632480223) ^ 14753 = 1045764811952 := by
        calc
          (3 : ZMod 1732632480223) ^ 14753 = (3 : ZMod 1732632480223) ^ (7376 + 7376 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 7376 * (3 : ZMod 1732632480223) ^ 7376) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1045764811952 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 1732632480223) ^ 29506 = 870223744846 := by
        calc
          (3 : ZMod 1732632480223) ^ 29506 = (3 : ZMod 1732632480223) ^ (14753 + 14753) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 14753 * (3 : ZMod 1732632480223) ^ 14753 := by rw [pow_add]
          _ = 870223744846 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 1732632480223) ^ 59013 = 1174358153115 := by
        calc
          (3 : ZMod 1732632480223) ^ 59013 = (3 : ZMod 1732632480223) ^ (29506 + 29506 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 29506 * (3 : ZMod 1732632480223) ^ 29506) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1174358153115 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 1732632480223) ^ 118026 = 612899490862 := by
        calc
          (3 : ZMod 1732632480223) ^ 118026 = (3 : ZMod 1732632480223) ^ (59013 + 59013) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 59013 * (3 : ZMod 1732632480223) ^ 59013 := by rw [pow_add]
          _ = 612899490862 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 1732632480223) ^ 236052 = 969717797226 := by
        calc
          (3 : ZMod 1732632480223) ^ 236052 = (3 : ZMod 1732632480223) ^ (118026 + 118026) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 118026 * (3 : ZMod 1732632480223) ^ 118026 := by rw [pow_add]
          _ = 969717797226 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 1732632480223) ^ 472104 = 869057449258 := by
        calc
          (3 : ZMod 1732632480223) ^ 472104 = (3 : ZMod 1732632480223) ^ (236052 + 236052) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 236052 * (3 : ZMod 1732632480223) ^ 236052 := by rw [pow_add]
          _ = 869057449258 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 1732632480223) ^ 944209 = 612064359489 := by
        calc
          (3 : ZMod 1732632480223) ^ 944209 = (3 : ZMod 1732632480223) ^ (472104 + 472104 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 472104 * (3 : ZMod 1732632480223) ^ 472104) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 612064359489 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 1732632480223) ^ 1888419 = 722346169627 := by
        calc
          (3 : ZMod 1732632480223) ^ 1888419 = (3 : ZMod 1732632480223) ^ (944209 + 944209 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 944209 * (3 : ZMod 1732632480223) ^ 944209) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 722346169627 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 1732632480223) ^ 3776839 = 1080319816183 := by
        calc
          (3 : ZMod 1732632480223) ^ 3776839 = (3 : ZMod 1732632480223) ^ (1888419 + 1888419 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1888419 * (3 : ZMod 1732632480223) ^ 1888419) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1080319816183 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 1732632480223) ^ 7553678 = 361748424165 := by
        calc
          (3 : ZMod 1732632480223) ^ 7553678 = (3 : ZMod 1732632480223) ^ (3776839 + 3776839) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 3776839 * (3 : ZMod 1732632480223) ^ 3776839 := by rw [pow_add]
          _ = 361748424165 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 1732632480223) ^ 15107356 = 598840168125 := by
        calc
          (3 : ZMod 1732632480223) ^ 15107356 = (3 : ZMod 1732632480223) ^ (7553678 + 7553678) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 7553678 * (3 : ZMod 1732632480223) ^ 7553678 := by rw [pow_add]
          _ = 598840168125 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 1732632480223) ^ 30214712 = 1225262551532 := by
        calc
          (3 : ZMod 1732632480223) ^ 30214712 = (3 : ZMod 1732632480223) ^ (15107356 + 15107356) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 15107356 * (3 : ZMod 1732632480223) ^ 15107356 := by rw [pow_add]
          _ = 1225262551532 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 1732632480223) ^ 60429425 = 1053403188679 := by
        calc
          (3 : ZMod 1732632480223) ^ 60429425 = (3 : ZMod 1732632480223) ^ (30214712 + 30214712 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 30214712 * (3 : ZMod 1732632480223) ^ 30214712) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1053403188679 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 1732632480223) ^ 120858850 = 97047374431 := by
        calc
          (3 : ZMod 1732632480223) ^ 120858850 = (3 : ZMod 1732632480223) ^ (60429425 + 60429425) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 60429425 * (3 : ZMod 1732632480223) ^ 60429425 := by rw [pow_add]
          _ = 97047374431 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 1732632480223) ^ 241717700 = 225139865877 := by
        calc
          (3 : ZMod 1732632480223) ^ 241717700 = (3 : ZMod 1732632480223) ^ (120858850 + 120858850) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 120858850 * (3 : ZMod 1732632480223) ^ 120858850 := by rw [pow_add]
          _ = 225139865877 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 1732632480223) ^ 483435401 = 211613746116 := by
        calc
          (3 : ZMod 1732632480223) ^ 483435401 = (3 : ZMod 1732632480223) ^ (241717700 + 241717700 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 241717700 * (3 : ZMod 1732632480223) ^ 241717700) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 211613746116 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 1732632480223) ^ 966870803 = 1728254396569 := by
        calc
          (3 : ZMod 1732632480223) ^ 966870803 = (3 : ZMod 1732632480223) ^ (483435401 + 483435401 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 483435401 * (3 : ZMod 1732632480223) ^ 483435401) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1728254396569 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 1732632480223) ^ 1933741607 = 122077819928 := by
        calc
          (3 : ZMod 1732632480223) ^ 1933741607 = (3 : ZMod 1732632480223) ^ (966870803 + 966870803 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 966870803 * (3 : ZMod 1732632480223) ^ 966870803) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 122077819928 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 1732632480223) ^ 3867483214 = 571539970121 := by
        calc
          (3 : ZMod 1732632480223) ^ 3867483214 = (3 : ZMod 1732632480223) ^ (1933741607 + 1933741607) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1933741607 * (3 : ZMod 1732632480223) ^ 1933741607 := by rw [pow_add]
          _ = 571539970121 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 1732632480223) ^ 7734966429 = 448815150250 := by
        calc
          (3 : ZMod 1732632480223) ^ 7734966429 = (3 : ZMod 1732632480223) ^ (3867483214 + 3867483214 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 3867483214 * (3 : ZMod 1732632480223) ^ 3867483214) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 448815150250 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 1732632480223) ^ 15469932859 = 163190963109 := by
        calc
          (3 : ZMod 1732632480223) ^ 15469932859 = (3 : ZMod 1732632480223) ^ (7734966429 + 7734966429 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 7734966429 * (3 : ZMod 1732632480223) ^ 7734966429) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 163190963109 := by rw [factor_2_32]; decide
      have factor_2_34 : (3 : ZMod 1732632480223) ^ 30939865718 = 1185640051202 := by
        calc
          (3 : ZMod 1732632480223) ^ 30939865718 = (3 : ZMod 1732632480223) ^ (15469932859 + 15469932859) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 15469932859 * (3 : ZMod 1732632480223) ^ 15469932859 := by rw [pow_add]
          _ = 1185640051202 := by rw [factor_2_33]; decide
      have factor_2_35 : (3 : ZMod 1732632480223) ^ 61879731436 = 192867730281 := by
        calc
          (3 : ZMod 1732632480223) ^ 61879731436 = (3 : ZMod 1732632480223) ^ (30939865718 + 30939865718) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 30939865718 * (3 : ZMod 1732632480223) ^ 30939865718 := by rw [pow_add]
          _ = 192867730281 := by rw [factor_2_34]; decide
      have factor_2_36 : (3 : ZMod 1732632480223) ^ 123759462873 = 1051256307220 := by
        calc
          (3 : ZMod 1732632480223) ^ 123759462873 = (3 : ZMod 1732632480223) ^ (61879731436 + 61879731436 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 61879731436 * (3 : ZMod 1732632480223) ^ 61879731436) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1051256307220 := by rw [factor_2_35]; decide
      have factor_2_37 : (3 : ZMod 1732632480223) ^ 247518925746 = 818397425090 := by
        calc
          (3 : ZMod 1732632480223) ^ 247518925746 = (3 : ZMod 1732632480223) ^ (123759462873 + 123759462873) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 123759462873 * (3 : ZMod 1732632480223) ^ 123759462873 := by rw [pow_add]
          _ = 818397425090 := by rw [factor_2_36]; decide
      change (3 : ZMod 1732632480223) ^ 247518925746 ≠ 1
      rw [factor_2_37]
      decide
    ·
      have factor_3_0 : (3 : ZMod 1732632480223) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 1732632480223) ^ 2 = 9 := by
        calc
          (3 : ZMod 1732632480223) ^ 2 = (3 : ZMod 1732632480223) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1 * (3 : ZMod 1732632480223) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 1732632480223) ^ 4 = 81 := by
        calc
          (3 : ZMod 1732632480223) ^ 4 = (3 : ZMod 1732632480223) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 2 * (3 : ZMod 1732632480223) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 1732632480223) ^ 8 = 6561 := by
        calc
          (3 : ZMod 1732632480223) ^ 8 = (3 : ZMod 1732632480223) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 4 * (3 : ZMod 1732632480223) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 1732632480223) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 1732632480223) ^ 16 = (3 : ZMod 1732632480223) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 8 * (3 : ZMod 1732632480223) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 1732632480223) ^ 33 = 775570000139 := by
        calc
          (3 : ZMod 1732632480223) ^ 33 = (3 : ZMod 1732632480223) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 16 * (3 : ZMod 1732632480223) ^ 16) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 775570000139 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 1732632480223) ^ 67 = 491522694442 := by
        calc
          (3 : ZMod 1732632480223) ^ 67 = (3 : ZMod 1732632480223) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 33 * (3 : ZMod 1732632480223) ^ 33) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 491522694442 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 1732632480223) ^ 135 = 58217312916 := by
        calc
          (3 : ZMod 1732632480223) ^ 135 = (3 : ZMod 1732632480223) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 67 * (3 : ZMod 1732632480223) ^ 67) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 58217312916 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 1732632480223) ^ 270 = 885509045207 := by
        calc
          (3 : ZMod 1732632480223) ^ 270 = (3 : ZMod 1732632480223) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 135 * (3 : ZMod 1732632480223) ^ 135 := by rw [pow_add]
          _ = 885509045207 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 1732632480223) ^ 540 = 240003738770 := by
        calc
          (3 : ZMod 1732632480223) ^ 540 = (3 : ZMod 1732632480223) ^ (270 + 270) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 270 * (3 : ZMod 1732632480223) ^ 270 := by rw [pow_add]
          _ = 240003738770 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 1732632480223) ^ 1081 = 1254043230558 := by
        calc
          (3 : ZMod 1732632480223) ^ 1081 = (3 : ZMod 1732632480223) ^ (540 + 540 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 540 * (3 : ZMod 1732632480223) ^ 540) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1254043230558 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 1732632480223) ^ 2162 = 1670259601373 := by
        calc
          (3 : ZMod 1732632480223) ^ 2162 = (3 : ZMod 1732632480223) ^ (1081 + 1081) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1081 * (3 : ZMod 1732632480223) ^ 1081 := by rw [pow_add]
          _ = 1670259601373 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 1732632480223) ^ 4325 = 1179619161358 := by
        calc
          (3 : ZMod 1732632480223) ^ 4325 = (3 : ZMod 1732632480223) ^ (2162 + 2162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 2162 * (3 : ZMod 1732632480223) ^ 2162) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1179619161358 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 1732632480223) ^ 8651 = 1470656586144 := by
        calc
          (3 : ZMod 1732632480223) ^ 8651 = (3 : ZMod 1732632480223) ^ (4325 + 4325 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 4325 * (3 : ZMod 1732632480223) ^ 4325) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1470656586144 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 1732632480223) ^ 17302 = 1427038673555 := by
        calc
          (3 : ZMod 1732632480223) ^ 17302 = (3 : ZMod 1732632480223) ^ (8651 + 8651) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 8651 * (3 : ZMod 1732632480223) ^ 8651 := by rw [pow_add]
          _ = 1427038673555 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 1732632480223) ^ 34604 = 423819760536 := by
        calc
          (3 : ZMod 1732632480223) ^ 34604 = (3 : ZMod 1732632480223) ^ (17302 + 17302) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 17302 * (3 : ZMod 1732632480223) ^ 17302 := by rw [pow_add]
          _ = 423819760536 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 1732632480223) ^ 69209 = 529660287409 := by
        calc
          (3 : ZMod 1732632480223) ^ 69209 = (3 : ZMod 1732632480223) ^ (34604 + 34604 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 34604 * (3 : ZMod 1732632480223) ^ 34604) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 529660287409 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 1732632480223) ^ 138418 = 632008487120 := by
        calc
          (3 : ZMod 1732632480223) ^ 138418 = (3 : ZMod 1732632480223) ^ (69209 + 69209) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 69209 * (3 : ZMod 1732632480223) ^ 69209 := by rw [pow_add]
          _ = 632008487120 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 1732632480223) ^ 276836 = 1036559724397 := by
        calc
          (3 : ZMod 1732632480223) ^ 276836 = (3 : ZMod 1732632480223) ^ (138418 + 138418) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 138418 * (3 : ZMod 1732632480223) ^ 138418 := by rw [pow_add]
          _ = 1036559724397 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 1732632480223) ^ 553672 = 275791011799 := by
        calc
          (3 : ZMod 1732632480223) ^ 553672 = (3 : ZMod 1732632480223) ^ (276836 + 276836) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 276836 * (3 : ZMod 1732632480223) ^ 276836 := by rw [pow_add]
          _ = 275791011799 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 1732632480223) ^ 1107345 = 1573670336414 := by
        calc
          (3 : ZMod 1732632480223) ^ 1107345 = (3 : ZMod 1732632480223) ^ (553672 + 553672 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 553672 * (3 : ZMod 1732632480223) ^ 553672) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1573670336414 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 1732632480223) ^ 2214690 = 473520873997 := by
        calc
          (3 : ZMod 1732632480223) ^ 2214690 = (3 : ZMod 1732632480223) ^ (1107345 + 1107345) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1107345 * (3 : ZMod 1732632480223) ^ 1107345 := by rw [pow_add]
          _ = 473520873997 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 1732632480223) ^ 4429381 = 1157781412851 := by
        calc
          (3 : ZMod 1732632480223) ^ 4429381 = (3 : ZMod 1732632480223) ^ (2214690 + 2214690 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 2214690 * (3 : ZMod 1732632480223) ^ 2214690) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1157781412851 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 1732632480223) ^ 8858763 = 1582821793812 := by
        calc
          (3 : ZMod 1732632480223) ^ 8858763 = (3 : ZMod 1732632480223) ^ (4429381 + 4429381 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 4429381 * (3 : ZMod 1732632480223) ^ 4429381) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1582821793812 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 1732632480223) ^ 17717527 = 1036288816377 := by
        calc
          (3 : ZMod 1732632480223) ^ 17717527 = (3 : ZMod 1732632480223) ^ (8858763 + 8858763 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 8858763 * (3 : ZMod 1732632480223) ^ 8858763) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1036288816377 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 1732632480223) ^ 35435055 = 1194297724946 := by
        calc
          (3 : ZMod 1732632480223) ^ 35435055 = (3 : ZMod 1732632480223) ^ (17717527 + 17717527 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 17717527 * (3 : ZMod 1732632480223) ^ 17717527) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1194297724946 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 1732632480223) ^ 70870111 = 386905588590 := by
        calc
          (3 : ZMod 1732632480223) ^ 70870111 = (3 : ZMod 1732632480223) ^ (35435055 + 35435055 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 35435055 * (3 : ZMod 1732632480223) ^ 35435055) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 386905588590 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 1732632480223) ^ 141740222 = 1306532898772 := by
        calc
          (3 : ZMod 1732632480223) ^ 141740222 = (3 : ZMod 1732632480223) ^ (70870111 + 70870111) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 70870111 * (3 : ZMod 1732632480223) ^ 70870111 := by rw [pow_add]
          _ = 1306532898772 := by rw [factor_3_26]; decide
      have factor_3_28 : (3 : ZMod 1732632480223) ^ 283480445 = 681974332701 := by
        calc
          (3 : ZMod 1732632480223) ^ 283480445 = (3 : ZMod 1732632480223) ^ (141740222 + 141740222 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 141740222 * (3 : ZMod 1732632480223) ^ 141740222) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 681974332701 := by rw [factor_3_27]; decide
      have factor_3_29 : (3 : ZMod 1732632480223) ^ 566960890 = 1404963921047 := by
        calc
          (3 : ZMod 1732632480223) ^ 566960890 = (3 : ZMod 1732632480223) ^ (283480445 + 283480445) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 283480445 * (3 : ZMod 1732632480223) ^ 283480445 := by rw [pow_add]
          _ = 1404963921047 := by rw [factor_3_28]; decide
      have factor_3_30 : (3 : ZMod 1732632480223) ^ 1133921780 = 1587586707304 := by
        calc
          (3 : ZMod 1732632480223) ^ 1133921780 = (3 : ZMod 1732632480223) ^ (566960890 + 566960890) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 566960890 * (3 : ZMod 1732632480223) ^ 566960890 := by rw [pow_add]
          _ = 1587586707304 := by rw [factor_3_29]; decide
      have factor_3_31 : (3 : ZMod 1732632480223) ^ 2267843560 = 1473472578691 := by
        calc
          (3 : ZMod 1732632480223) ^ 2267843560 = (3 : ZMod 1732632480223) ^ (1133921780 + 1133921780) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 1133921780 * (3 : ZMod 1732632480223) ^ 1133921780 := by rw [pow_add]
          _ = 1473472578691 := by rw [factor_3_30]; decide
      have factor_3_32 : (3 : ZMod 1732632480223) ^ 4535687121 = 1189335358639 := by
        calc
          (3 : ZMod 1732632480223) ^ 4535687121 = (3 : ZMod 1732632480223) ^ (2267843560 + 2267843560 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 2267843560 * (3 : ZMod 1732632480223) ^ 2267843560) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1189335358639 := by rw [factor_3_31]; decide
      have factor_3_33 : (3 : ZMod 1732632480223) ^ 9071374242 = 1284535858420 := by
        calc
          (3 : ZMod 1732632480223) ^ 9071374242 = (3 : ZMod 1732632480223) ^ (4535687121 + 4535687121) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 4535687121 * (3 : ZMod 1732632480223) ^ 4535687121 := by rw [pow_add]
          _ = 1284535858420 := by rw [factor_3_32]; decide
      change (3 : ZMod 1732632480223) ^ 9071374242 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (3 : ZMod 1732632480223) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 1732632480223) ^ 3 = 27 := by
        calc
          (3 : ZMod 1732632480223) ^ 3 = (3 : ZMod 1732632480223) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1 * (3 : ZMod 1732632480223) ^ 1) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 1732632480223) ^ 7 = 2187 := by
        calc
          (3 : ZMod 1732632480223) ^ 7 = (3 : ZMod 1732632480223) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 3 * (3 : ZMod 1732632480223) ^ 3) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 1732632480223) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 1732632480223) ^ 15 = (3 : ZMod 1732632480223) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 7 * (3 : ZMod 1732632480223) ^ 7) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 1732632480223) ^ 31 = 856233324559 := by
        calc
          (3 : ZMod 1732632480223) ^ 31 = (3 : ZMod 1732632480223) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 15 * (3 : ZMod 1732632480223) ^ 15) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 856233324559 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 1732632480223) ^ 62 = 764951432421 := by
        calc
          (3 : ZMod 1732632480223) ^ 62 = (3 : ZMod 1732632480223) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 31 * (3 : ZMod 1732632480223) ^ 31 := by rw [pow_add]
          _ = 764951432421 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 1732632480223) ^ 125 = 321122933172 := by
        calc
          (3 : ZMod 1732632480223) ^ 125 = (3 : ZMod 1732632480223) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 62 * (3 : ZMod 1732632480223) ^ 62) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 321122933172 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 1732632480223) ^ 250 = 70020479644 := by
        calc
          (3 : ZMod 1732632480223) ^ 250 = (3 : ZMod 1732632480223) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 125 * (3 : ZMod 1732632480223) ^ 125 := by rw [pow_add]
          _ = 70020479644 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 1732632480223) ^ 501 = 1233222864010 := by
        calc
          (3 : ZMod 1732632480223) ^ 501 = (3 : ZMod 1732632480223) ^ (250 + 250 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 250 * (3 : ZMod 1732632480223) ^ 250) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1233222864010 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 1732632480223) ^ 1002 = 308695990093 := by
        calc
          (3 : ZMod 1732632480223) ^ 1002 = (3 : ZMod 1732632480223) ^ (501 + 501) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 501 * (3 : ZMod 1732632480223) ^ 501 := by rw [pow_add]
          _ = 308695990093 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 1732632480223) ^ 2005 = 1662573146665 := by
        calc
          (3 : ZMod 1732632480223) ^ 2005 = (3 : ZMod 1732632480223) ^ (1002 + 1002 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 1002 * (3 : ZMod 1732632480223) ^ 1002) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 1662573146665 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 1732632480223) ^ 4011 = 964606678954 := by
        calc
          (3 : ZMod 1732632480223) ^ 4011 = (3 : ZMod 1732632480223) ^ (2005 + 2005 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = ((3 : ZMod 1732632480223) ^ 2005 * (3 : ZMod 1732632480223) ^ 2005) * (3 : ZMod 1732632480223) := by rw [pow_succ, pow_add]
          _ = 964606678954 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 1732632480223) ^ 8022 = 1356002112453 := by
        calc
          (3 : ZMod 1732632480223) ^ 8022 = (3 : ZMod 1732632480223) ^ (4011 + 4011) :=
            congrArg (fun n : ℕ => (3 : ZMod 1732632480223) ^ n) (by norm_num)
          _ = (3 : ZMod 1732632480223) ^ 4011 * (3 : ZMod 1732632480223) ^ 4011 := by rw [pow_add]
          _ = 1356002112453 := by rw [factor_4_11]; decide
      change (3 : ZMod 1732632480223) ^ 8022 ≠ 1
      rw [factor_4_12]
      decide

#print axioms prime_lucas_1732632480223

end TotientTailPeriodKiller
end Erdos249257
