import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime9245152471

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_943005552043 : Nat.Prime 943005552043 := by
  apply lucas_primality 943005552043 (2 : ZMod 943005552043)
  ·
      have fermat_0 : (2 : ZMod 943005552043) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 943005552043) ^ 3 = 8 := by
        calc
          (2 : ZMod 943005552043) ^ 3 = (2 : ZMod 943005552043) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1 * (2 : ZMod 943005552043) ^ 1) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 943005552043) ^ 6 = 64 := by
        calc
          (2 : ZMod 943005552043) ^ 6 = (2 : ZMod 943005552043) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 3 * (2 : ZMod 943005552043) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 943005552043) ^ 13 = 8192 := by
        calc
          (2 : ZMod 943005552043) ^ 13 = (2 : ZMod 943005552043) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 6 * (2 : ZMod 943005552043) ^ 6) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 943005552043) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 943005552043) ^ 27 = (2 : ZMod 943005552043) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 13 * (2 : ZMod 943005552043) ^ 13) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 943005552043) ^ 54 = 163448804555 := by
        calc
          (2 : ZMod 943005552043) ^ 54 = (2 : ZMod 943005552043) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 27 * (2 : ZMod 943005552043) ^ 27 := by rw [pow_add]
          _ = 163448804555 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 943005552043) ^ 109 = 93705717219 := by
        calc
          (2 : ZMod 943005552043) ^ 109 = (2 : ZMod 943005552043) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 54 * (2 : ZMod 943005552043) ^ 54) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 93705717219 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 943005552043) ^ 219 = 783888245839 := by
        calc
          (2 : ZMod 943005552043) ^ 219 = (2 : ZMod 943005552043) ^ (109 + 109 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 109 * (2 : ZMod 943005552043) ^ 109) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 783888245839 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 943005552043) ^ 439 = 130509856964 := by
        calc
          (2 : ZMod 943005552043) ^ 439 = (2 : ZMod 943005552043) ^ (219 + 219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 219 * (2 : ZMod 943005552043) ^ 219) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 130509856964 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 943005552043) ^ 878 = 398000881941 := by
        calc
          (2 : ZMod 943005552043) ^ 878 = (2 : ZMod 943005552043) ^ (439 + 439) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 439 * (2 : ZMod 943005552043) ^ 439 := by rw [pow_add]
          _ = 398000881941 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 943005552043) ^ 1756 = 335269065616 := by
        calc
          (2 : ZMod 943005552043) ^ 1756 = (2 : ZMod 943005552043) ^ (878 + 878) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 878 * (2 : ZMod 943005552043) ^ 878 := by rw [pow_add]
          _ = 335269065616 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 943005552043) ^ 3512 = 771892450738 := by
        calc
          (2 : ZMod 943005552043) ^ 3512 = (2 : ZMod 943005552043) ^ (1756 + 1756) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 1756 * (2 : ZMod 943005552043) ^ 1756 := by rw [pow_add]
          _ = 771892450738 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 943005552043) ^ 7025 = 785138781169 := by
        calc
          (2 : ZMod 943005552043) ^ 7025 = (2 : ZMod 943005552043) ^ (3512 + 3512 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 3512 * (2 : ZMod 943005552043) ^ 3512) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 785138781169 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 943005552043) ^ 14051 = 882279356713 := by
        calc
          (2 : ZMod 943005552043) ^ 14051 = (2 : ZMod 943005552043) ^ (7025 + 7025 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 7025 * (2 : ZMod 943005552043) ^ 7025) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 882279356713 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 943005552043) ^ 28103 = 321968021896 := by
        calc
          (2 : ZMod 943005552043) ^ 28103 = (2 : ZMod 943005552043) ^ (14051 + 14051 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 14051 * (2 : ZMod 943005552043) ^ 14051) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 321968021896 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 943005552043) ^ 56207 = 559618455969 := by
        calc
          (2 : ZMod 943005552043) ^ 56207 = (2 : ZMod 943005552043) ^ (28103 + 28103 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 28103 * (2 : ZMod 943005552043) ^ 28103) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 559618455969 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 943005552043) ^ 112415 = 185609510031 := by
        calc
          (2 : ZMod 943005552043) ^ 112415 = (2 : ZMod 943005552043) ^ (56207 + 56207 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 56207 * (2 : ZMod 943005552043) ^ 56207) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 185609510031 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 943005552043) ^ 224830 = 56369774859 := by
        calc
          (2 : ZMod 943005552043) ^ 224830 = (2 : ZMod 943005552043) ^ (112415 + 112415) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 112415 * (2 : ZMod 943005552043) ^ 112415 := by rw [pow_add]
          _ = 56369774859 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 943005552043) ^ 449660 = 60200149451 := by
        calc
          (2 : ZMod 943005552043) ^ 449660 = (2 : ZMod 943005552043) ^ (224830 + 224830) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 224830 * (2 : ZMod 943005552043) ^ 224830 := by rw [pow_add]
          _ = 60200149451 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 943005552043) ^ 899320 = 340396444336 := by
        calc
          (2 : ZMod 943005552043) ^ 899320 = (2 : ZMod 943005552043) ^ (449660 + 449660) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 449660 * (2 : ZMod 943005552043) ^ 449660 := by rw [pow_add]
          _ = 340396444336 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 943005552043) ^ 1798640 = 721846670435 := by
        calc
          (2 : ZMod 943005552043) ^ 1798640 = (2 : ZMod 943005552043) ^ (899320 + 899320) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 899320 * (2 : ZMod 943005552043) ^ 899320 := by rw [pow_add]
          _ = 721846670435 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 943005552043) ^ 3597280 = 748335689374 := by
        calc
          (2 : ZMod 943005552043) ^ 3597280 = (2 : ZMod 943005552043) ^ (1798640 + 1798640) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 1798640 * (2 : ZMod 943005552043) ^ 1798640 := by rw [pow_add]
          _ = 748335689374 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 943005552043) ^ 7194561 = 316908495051 := by
        calc
          (2 : ZMod 943005552043) ^ 7194561 = (2 : ZMod 943005552043) ^ (3597280 + 3597280 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 3597280 * (2 : ZMod 943005552043) ^ 3597280) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 316908495051 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 943005552043) ^ 14389122 = 6021487413 := by
        calc
          (2 : ZMod 943005552043) ^ 14389122 = (2 : ZMod 943005552043) ^ (7194561 + 7194561) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 7194561 * (2 : ZMod 943005552043) ^ 7194561 := by rw [pow_add]
          _ = 6021487413 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 943005552043) ^ 28778245 = 771709612229 := by
        calc
          (2 : ZMod 943005552043) ^ 28778245 = (2 : ZMod 943005552043) ^ (14389122 + 14389122 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 14389122 * (2 : ZMod 943005552043) ^ 14389122) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 771709612229 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 943005552043) ^ 57556491 = 574333557201 := by
        calc
          (2 : ZMod 943005552043) ^ 57556491 = (2 : ZMod 943005552043) ^ (28778245 + 28778245 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 28778245 * (2 : ZMod 943005552043) ^ 28778245) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 574333557201 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 943005552043) ^ 115112982 = 371895356901 := by
        calc
          (2 : ZMod 943005552043) ^ 115112982 = (2 : ZMod 943005552043) ^ (57556491 + 57556491) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 57556491 * (2 : ZMod 943005552043) ^ 57556491 := by rw [pow_add]
          _ = 371895356901 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 943005552043) ^ 230225964 = 318194084039 := by
        calc
          (2 : ZMod 943005552043) ^ 230225964 = (2 : ZMod 943005552043) ^ (115112982 + 115112982) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 115112982 * (2 : ZMod 943005552043) ^ 115112982 := by rw [pow_add]
          _ = 318194084039 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 943005552043) ^ 460451929 = 355289015984 := by
        calc
          (2 : ZMod 943005552043) ^ 460451929 = (2 : ZMod 943005552043) ^ (230225964 + 230225964 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 230225964 * (2 : ZMod 943005552043) ^ 230225964) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 355289015984 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 943005552043) ^ 920903859 = 684339638129 := by
        calc
          (2 : ZMod 943005552043) ^ 920903859 = (2 : ZMod 943005552043) ^ (460451929 + 460451929 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 460451929 * (2 : ZMod 943005552043) ^ 460451929) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 684339638129 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 943005552043) ^ 1841807718 = 55949335101 := by
        calc
          (2 : ZMod 943005552043) ^ 1841807718 = (2 : ZMod 943005552043) ^ (920903859 + 920903859) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 920903859 * (2 : ZMod 943005552043) ^ 920903859 := by rw [pow_add]
          _ = 55949335101 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 943005552043) ^ 3683615437 = 240245389917 := by
        calc
          (2 : ZMod 943005552043) ^ 3683615437 = (2 : ZMod 943005552043) ^ (1841807718 + 1841807718 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1841807718 * (2 : ZMod 943005552043) ^ 1841807718) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 240245389917 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 943005552043) ^ 7367230875 = 190418110652 := by
        calc
          (2 : ZMod 943005552043) ^ 7367230875 = (2 : ZMod 943005552043) ^ (3683615437 + 3683615437 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 3683615437 * (2 : ZMod 943005552043) ^ 3683615437) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 190418110652 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 943005552043) ^ 14734461750 = 175092551160 := by
        calc
          (2 : ZMod 943005552043) ^ 14734461750 = (2 : ZMod 943005552043) ^ (7367230875 + 7367230875) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 7367230875 * (2 : ZMod 943005552043) ^ 7367230875 := by rw [pow_add]
          _ = 175092551160 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 943005552043) ^ 29468923501 = 126286810954 := by
        calc
          (2 : ZMod 943005552043) ^ 29468923501 = (2 : ZMod 943005552043) ^ (14734461750 + 14734461750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 14734461750 * (2 : ZMod 943005552043) ^ 14734461750) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 126286810954 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 943005552043) ^ 58937847002 = 464728184565 := by
        calc
          (2 : ZMod 943005552043) ^ 58937847002 = (2 : ZMod 943005552043) ^ (29468923501 + 29468923501) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 29468923501 * (2 : ZMod 943005552043) ^ 29468923501 := by rw [pow_add]
          _ = 464728184565 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 943005552043) ^ 117875694005 = 95267581149 := by
        calc
          (2 : ZMod 943005552043) ^ 117875694005 = (2 : ZMod 943005552043) ^ (58937847002 + 58937847002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 58937847002 * (2 : ZMod 943005552043) ^ 58937847002) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 95267581149 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 943005552043) ^ 235751388010 = 526907124420 := by
        calc
          (2 : ZMod 943005552043) ^ 235751388010 = (2 : ZMod 943005552043) ^ (117875694005 + 117875694005) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 117875694005 * (2 : ZMod 943005552043) ^ 117875694005 := by rw [pow_add]
          _ = 526907124420 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 943005552043) ^ 471502776021 = 943005552042 := by
        calc
          (2 : ZMod 943005552043) ^ 471502776021 = (2 : ZMod 943005552043) ^ (235751388010 + 235751388010 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 235751388010 * (2 : ZMod 943005552043) ^ 235751388010) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 943005552042 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 943005552043) ^ 943005552042 = 1 := by
        calc
          (2 : ZMod 943005552043) ^ 943005552042 = (2 : ZMod 943005552043) ^ (471502776021 + 471502776021) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 471502776021 * (2 : ZMod 943005552043) ^ 471502776021 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (9245152471, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (9245152471, 1)] : List FactorBlock).map factorBlockValue).prod = 943005552043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_9245152471) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 943005552043) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 943005552043) ^ 3 = 8 := by
        calc
          (2 : ZMod 943005552043) ^ 3 = (2 : ZMod 943005552043) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1 * (2 : ZMod 943005552043) ^ 1) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 943005552043) ^ 6 = 64 := by
        calc
          (2 : ZMod 943005552043) ^ 6 = (2 : ZMod 943005552043) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 3 * (2 : ZMod 943005552043) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 943005552043) ^ 13 = 8192 := by
        calc
          (2 : ZMod 943005552043) ^ 13 = (2 : ZMod 943005552043) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 6 * (2 : ZMod 943005552043) ^ 6) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 943005552043) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 943005552043) ^ 27 = (2 : ZMod 943005552043) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 13 * (2 : ZMod 943005552043) ^ 13) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 943005552043) ^ 54 = 163448804555 := by
        calc
          (2 : ZMod 943005552043) ^ 54 = (2 : ZMod 943005552043) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 27 * (2 : ZMod 943005552043) ^ 27 := by rw [pow_add]
          _ = 163448804555 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 943005552043) ^ 109 = 93705717219 := by
        calc
          (2 : ZMod 943005552043) ^ 109 = (2 : ZMod 943005552043) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 54 * (2 : ZMod 943005552043) ^ 54) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 93705717219 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 943005552043) ^ 219 = 783888245839 := by
        calc
          (2 : ZMod 943005552043) ^ 219 = (2 : ZMod 943005552043) ^ (109 + 109 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 109 * (2 : ZMod 943005552043) ^ 109) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 783888245839 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 943005552043) ^ 439 = 130509856964 := by
        calc
          (2 : ZMod 943005552043) ^ 439 = (2 : ZMod 943005552043) ^ (219 + 219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 219 * (2 : ZMod 943005552043) ^ 219) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 130509856964 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 943005552043) ^ 878 = 398000881941 := by
        calc
          (2 : ZMod 943005552043) ^ 878 = (2 : ZMod 943005552043) ^ (439 + 439) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 439 * (2 : ZMod 943005552043) ^ 439 := by rw [pow_add]
          _ = 398000881941 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 943005552043) ^ 1756 = 335269065616 := by
        calc
          (2 : ZMod 943005552043) ^ 1756 = (2 : ZMod 943005552043) ^ (878 + 878) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 878 * (2 : ZMod 943005552043) ^ 878 := by rw [pow_add]
          _ = 335269065616 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 943005552043) ^ 3512 = 771892450738 := by
        calc
          (2 : ZMod 943005552043) ^ 3512 = (2 : ZMod 943005552043) ^ (1756 + 1756) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 1756 * (2 : ZMod 943005552043) ^ 1756 := by rw [pow_add]
          _ = 771892450738 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 943005552043) ^ 7025 = 785138781169 := by
        calc
          (2 : ZMod 943005552043) ^ 7025 = (2 : ZMod 943005552043) ^ (3512 + 3512 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 3512 * (2 : ZMod 943005552043) ^ 3512) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 785138781169 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 943005552043) ^ 14051 = 882279356713 := by
        calc
          (2 : ZMod 943005552043) ^ 14051 = (2 : ZMod 943005552043) ^ (7025 + 7025 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 7025 * (2 : ZMod 943005552043) ^ 7025) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 882279356713 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 943005552043) ^ 28103 = 321968021896 := by
        calc
          (2 : ZMod 943005552043) ^ 28103 = (2 : ZMod 943005552043) ^ (14051 + 14051 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 14051 * (2 : ZMod 943005552043) ^ 14051) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 321968021896 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 943005552043) ^ 56207 = 559618455969 := by
        calc
          (2 : ZMod 943005552043) ^ 56207 = (2 : ZMod 943005552043) ^ (28103 + 28103 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 28103 * (2 : ZMod 943005552043) ^ 28103) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 559618455969 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 943005552043) ^ 112415 = 185609510031 := by
        calc
          (2 : ZMod 943005552043) ^ 112415 = (2 : ZMod 943005552043) ^ (56207 + 56207 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 56207 * (2 : ZMod 943005552043) ^ 56207) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 185609510031 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 943005552043) ^ 224830 = 56369774859 := by
        calc
          (2 : ZMod 943005552043) ^ 224830 = (2 : ZMod 943005552043) ^ (112415 + 112415) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 112415 * (2 : ZMod 943005552043) ^ 112415 := by rw [pow_add]
          _ = 56369774859 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 943005552043) ^ 449660 = 60200149451 := by
        calc
          (2 : ZMod 943005552043) ^ 449660 = (2 : ZMod 943005552043) ^ (224830 + 224830) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 224830 * (2 : ZMod 943005552043) ^ 224830 := by rw [pow_add]
          _ = 60200149451 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 943005552043) ^ 899320 = 340396444336 := by
        calc
          (2 : ZMod 943005552043) ^ 899320 = (2 : ZMod 943005552043) ^ (449660 + 449660) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 449660 * (2 : ZMod 943005552043) ^ 449660 := by rw [pow_add]
          _ = 340396444336 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 943005552043) ^ 1798640 = 721846670435 := by
        calc
          (2 : ZMod 943005552043) ^ 1798640 = (2 : ZMod 943005552043) ^ (899320 + 899320) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 899320 * (2 : ZMod 943005552043) ^ 899320 := by rw [pow_add]
          _ = 721846670435 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 943005552043) ^ 3597280 = 748335689374 := by
        calc
          (2 : ZMod 943005552043) ^ 3597280 = (2 : ZMod 943005552043) ^ (1798640 + 1798640) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 1798640 * (2 : ZMod 943005552043) ^ 1798640 := by rw [pow_add]
          _ = 748335689374 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 943005552043) ^ 7194561 = 316908495051 := by
        calc
          (2 : ZMod 943005552043) ^ 7194561 = (2 : ZMod 943005552043) ^ (3597280 + 3597280 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 3597280 * (2 : ZMod 943005552043) ^ 3597280) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 316908495051 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 943005552043) ^ 14389122 = 6021487413 := by
        calc
          (2 : ZMod 943005552043) ^ 14389122 = (2 : ZMod 943005552043) ^ (7194561 + 7194561) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 7194561 * (2 : ZMod 943005552043) ^ 7194561 := by rw [pow_add]
          _ = 6021487413 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 943005552043) ^ 28778245 = 771709612229 := by
        calc
          (2 : ZMod 943005552043) ^ 28778245 = (2 : ZMod 943005552043) ^ (14389122 + 14389122 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 14389122 * (2 : ZMod 943005552043) ^ 14389122) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 771709612229 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 943005552043) ^ 57556491 = 574333557201 := by
        calc
          (2 : ZMod 943005552043) ^ 57556491 = (2 : ZMod 943005552043) ^ (28778245 + 28778245 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 28778245 * (2 : ZMod 943005552043) ^ 28778245) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 574333557201 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 943005552043) ^ 115112982 = 371895356901 := by
        calc
          (2 : ZMod 943005552043) ^ 115112982 = (2 : ZMod 943005552043) ^ (57556491 + 57556491) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 57556491 * (2 : ZMod 943005552043) ^ 57556491 := by rw [pow_add]
          _ = 371895356901 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 943005552043) ^ 230225964 = 318194084039 := by
        calc
          (2 : ZMod 943005552043) ^ 230225964 = (2 : ZMod 943005552043) ^ (115112982 + 115112982) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 115112982 * (2 : ZMod 943005552043) ^ 115112982 := by rw [pow_add]
          _ = 318194084039 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 943005552043) ^ 460451929 = 355289015984 := by
        calc
          (2 : ZMod 943005552043) ^ 460451929 = (2 : ZMod 943005552043) ^ (230225964 + 230225964 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 230225964 * (2 : ZMod 943005552043) ^ 230225964) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 355289015984 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 943005552043) ^ 920903859 = 684339638129 := by
        calc
          (2 : ZMod 943005552043) ^ 920903859 = (2 : ZMod 943005552043) ^ (460451929 + 460451929 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 460451929 * (2 : ZMod 943005552043) ^ 460451929) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 684339638129 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 943005552043) ^ 1841807718 = 55949335101 := by
        calc
          (2 : ZMod 943005552043) ^ 1841807718 = (2 : ZMod 943005552043) ^ (920903859 + 920903859) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 920903859 * (2 : ZMod 943005552043) ^ 920903859 := by rw [pow_add]
          _ = 55949335101 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 943005552043) ^ 3683615437 = 240245389917 := by
        calc
          (2 : ZMod 943005552043) ^ 3683615437 = (2 : ZMod 943005552043) ^ (1841807718 + 1841807718 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1841807718 * (2 : ZMod 943005552043) ^ 1841807718) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 240245389917 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 943005552043) ^ 7367230875 = 190418110652 := by
        calc
          (2 : ZMod 943005552043) ^ 7367230875 = (2 : ZMod 943005552043) ^ (3683615437 + 3683615437 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 3683615437 * (2 : ZMod 943005552043) ^ 3683615437) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 190418110652 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 943005552043) ^ 14734461750 = 175092551160 := by
        calc
          (2 : ZMod 943005552043) ^ 14734461750 = (2 : ZMod 943005552043) ^ (7367230875 + 7367230875) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 7367230875 * (2 : ZMod 943005552043) ^ 7367230875 := by rw [pow_add]
          _ = 175092551160 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 943005552043) ^ 29468923501 = 126286810954 := by
        calc
          (2 : ZMod 943005552043) ^ 29468923501 = (2 : ZMod 943005552043) ^ (14734461750 + 14734461750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 14734461750 * (2 : ZMod 943005552043) ^ 14734461750) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 126286810954 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 943005552043) ^ 58937847002 = 464728184565 := by
        calc
          (2 : ZMod 943005552043) ^ 58937847002 = (2 : ZMod 943005552043) ^ (29468923501 + 29468923501) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 29468923501 * (2 : ZMod 943005552043) ^ 29468923501 := by rw [pow_add]
          _ = 464728184565 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 943005552043) ^ 117875694005 = 95267581149 := by
        calc
          (2 : ZMod 943005552043) ^ 117875694005 = (2 : ZMod 943005552043) ^ (58937847002 + 58937847002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 58937847002 * (2 : ZMod 943005552043) ^ 58937847002) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 95267581149 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 943005552043) ^ 235751388010 = 526907124420 := by
        calc
          (2 : ZMod 943005552043) ^ 235751388010 = (2 : ZMod 943005552043) ^ (117875694005 + 117875694005) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 117875694005 * (2 : ZMod 943005552043) ^ 117875694005 := by rw [pow_add]
          _ = 526907124420 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 943005552043) ^ 471502776021 = 943005552042 := by
        calc
          (2 : ZMod 943005552043) ^ 471502776021 = (2 : ZMod 943005552043) ^ (235751388010 + 235751388010 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 235751388010 * (2 : ZMod 943005552043) ^ 235751388010) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 943005552042 := by rw [factor_0_37]; decide
      change (2 : ZMod 943005552043) ^ 471502776021 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (2 : ZMod 943005552043) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 943005552043) ^ 2 = 4 := by
        calc
          (2 : ZMod 943005552043) ^ 2 = (2 : ZMod 943005552043) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 1 * (2 : ZMod 943005552043) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 943005552043) ^ 4 = 16 := by
        calc
          (2 : ZMod 943005552043) ^ 4 = (2 : ZMod 943005552043) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 2 * (2 : ZMod 943005552043) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 943005552043) ^ 9 = 512 := by
        calc
          (2 : ZMod 943005552043) ^ 9 = (2 : ZMod 943005552043) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 4 * (2 : ZMod 943005552043) ^ 4) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 943005552043) ^ 18 = 262144 := by
        calc
          (2 : ZMod 943005552043) ^ 18 = (2 : ZMod 943005552043) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 9 * (2 : ZMod 943005552043) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 943005552043) ^ 36 = 68719476736 := by
        calc
          (2 : ZMod 943005552043) ^ 36 = (2 : ZMod 943005552043) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 18 * (2 : ZMod 943005552043) ^ 18 := by rw [pow_add]
          _ = 68719476736 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 943005552043) ^ 73 = 503311728301 := by
        calc
          (2 : ZMod 943005552043) ^ 73 = (2 : ZMod 943005552043) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 36 * (2 : ZMod 943005552043) ^ 36) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 503311728301 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 943005552043) ^ 146 = 659205021468 := by
        calc
          (2 : ZMod 943005552043) ^ 146 = (2 : ZMod 943005552043) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 73 * (2 : ZMod 943005552043) ^ 73 := by rw [pow_add]
          _ = 659205021468 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 943005552043) ^ 292 = 615746834232 := by
        calc
          (2 : ZMod 943005552043) ^ 292 = (2 : ZMod 943005552043) ^ (146 + 146) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 146 * (2 : ZMod 943005552043) ^ 146 := by rw [pow_add]
          _ = 615746834232 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 943005552043) ^ 585 = 613917095184 := by
        calc
          (2 : ZMod 943005552043) ^ 585 = (2 : ZMod 943005552043) ^ (292 + 292 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 292 * (2 : ZMod 943005552043) ^ 292) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 613917095184 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 943005552043) ^ 1170 = 7444434097 := by
        calc
          (2 : ZMod 943005552043) ^ 1170 = (2 : ZMod 943005552043) ^ (585 + 585) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 585 * (2 : ZMod 943005552043) ^ 585 := by rw [pow_add]
          _ = 7444434097 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 943005552043) ^ 2341 = 239878619186 := by
        calc
          (2 : ZMod 943005552043) ^ 2341 = (2 : ZMod 943005552043) ^ (1170 + 1170 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1170 * (2 : ZMod 943005552043) ^ 1170) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 239878619186 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 943005552043) ^ 4683 = 197965756292 := by
        calc
          (2 : ZMod 943005552043) ^ 4683 = (2 : ZMod 943005552043) ^ (2341 + 2341 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 2341 * (2 : ZMod 943005552043) ^ 2341) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 197965756292 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 943005552043) ^ 9367 = 91272239761 := by
        calc
          (2 : ZMod 943005552043) ^ 9367 = (2 : ZMod 943005552043) ^ (4683 + 4683 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 4683 * (2 : ZMod 943005552043) ^ 4683) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 91272239761 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 943005552043) ^ 18735 = 209650498272 := by
        calc
          (2 : ZMod 943005552043) ^ 18735 = (2 : ZMod 943005552043) ^ (9367 + 9367 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 9367 * (2 : ZMod 943005552043) ^ 9367) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 209650498272 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 943005552043) ^ 37471 = 133178834401 := by
        calc
          (2 : ZMod 943005552043) ^ 37471 = (2 : ZMod 943005552043) ^ (18735 + 18735 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 18735 * (2 : ZMod 943005552043) ^ 18735) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 133178834401 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 943005552043) ^ 74943 = 432786426784 := by
        calc
          (2 : ZMod 943005552043) ^ 74943 = (2 : ZMod 943005552043) ^ (37471 + 37471 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 37471 * (2 : ZMod 943005552043) ^ 37471) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 432786426784 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 943005552043) ^ 149886 = 187666569646 := by
        calc
          (2 : ZMod 943005552043) ^ 149886 = (2 : ZMod 943005552043) ^ (74943 + 74943) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 74943 * (2 : ZMod 943005552043) ^ 74943 := by rw [pow_add]
          _ = 187666569646 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 943005552043) ^ 299773 = 257332520781 := by
        calc
          (2 : ZMod 943005552043) ^ 299773 = (2 : ZMod 943005552043) ^ (149886 + 149886 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 149886 * (2 : ZMod 943005552043) ^ 149886) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 257332520781 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 943005552043) ^ 599546 = 12632457143 := by
        calc
          (2 : ZMod 943005552043) ^ 599546 = (2 : ZMod 943005552043) ^ (299773 + 299773) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 299773 * (2 : ZMod 943005552043) ^ 299773 := by rw [pow_add]
          _ = 12632457143 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 943005552043) ^ 1199093 = 866951591001 := by
        calc
          (2 : ZMod 943005552043) ^ 1199093 = (2 : ZMod 943005552043) ^ (599546 + 599546 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 599546 * (2 : ZMod 943005552043) ^ 599546) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 866951591001 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 943005552043) ^ 2398187 = 146426732332 := by
        calc
          (2 : ZMod 943005552043) ^ 2398187 = (2 : ZMod 943005552043) ^ (1199093 + 1199093 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1199093 * (2 : ZMod 943005552043) ^ 1199093) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 146426732332 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 943005552043) ^ 4796374 = 278245469738 := by
        calc
          (2 : ZMod 943005552043) ^ 4796374 = (2 : ZMod 943005552043) ^ (2398187 + 2398187) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 2398187 * (2 : ZMod 943005552043) ^ 2398187 := by rw [pow_add]
          _ = 278245469738 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 943005552043) ^ 9592748 = 245236316737 := by
        calc
          (2 : ZMod 943005552043) ^ 9592748 = (2 : ZMod 943005552043) ^ (4796374 + 4796374) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 4796374 * (2 : ZMod 943005552043) ^ 4796374 := by rw [pow_add]
          _ = 245236316737 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 943005552043) ^ 19185497 = 355195260630 := by
        calc
          (2 : ZMod 943005552043) ^ 19185497 = (2 : ZMod 943005552043) ^ (9592748 + 9592748 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 9592748 * (2 : ZMod 943005552043) ^ 9592748) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 355195260630 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 943005552043) ^ 38370994 = 568613291067 := by
        calc
          (2 : ZMod 943005552043) ^ 38370994 = (2 : ZMod 943005552043) ^ (19185497 + 19185497) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 19185497 * (2 : ZMod 943005552043) ^ 19185497 := by rw [pow_add]
          _ = 568613291067 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 943005552043) ^ 76741988 = 103938354012 := by
        calc
          (2 : ZMod 943005552043) ^ 76741988 = (2 : ZMod 943005552043) ^ (38370994 + 38370994) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 38370994 * (2 : ZMod 943005552043) ^ 38370994 := by rw [pow_add]
          _ = 103938354012 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 943005552043) ^ 153483976 = 548593152020 := by
        calc
          (2 : ZMod 943005552043) ^ 153483976 = (2 : ZMod 943005552043) ^ (76741988 + 76741988) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 76741988 * (2 : ZMod 943005552043) ^ 76741988 := by rw [pow_add]
          _ = 548593152020 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 943005552043) ^ 306967953 = 883373352745 := by
        calc
          (2 : ZMod 943005552043) ^ 306967953 = (2 : ZMod 943005552043) ^ (153483976 + 153483976 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 153483976 * (2 : ZMod 943005552043) ^ 153483976) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 883373352745 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 943005552043) ^ 613935906 = 868304725070 := by
        calc
          (2 : ZMod 943005552043) ^ 613935906 = (2 : ZMod 943005552043) ^ (306967953 + 306967953) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 306967953 * (2 : ZMod 943005552043) ^ 306967953 := by rw [pow_add]
          _ = 868304725070 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 943005552043) ^ 1227871812 = 410006180975 := by
        calc
          (2 : ZMod 943005552043) ^ 1227871812 = (2 : ZMod 943005552043) ^ (613935906 + 613935906) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 613935906 * (2 : ZMod 943005552043) ^ 613935906 := by rw [pow_add]
          _ = 410006180975 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 943005552043) ^ 2455743625 = 181976875977 := by
        calc
          (2 : ZMod 943005552043) ^ 2455743625 = (2 : ZMod 943005552043) ^ (1227871812 + 1227871812 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1227871812 * (2 : ZMod 943005552043) ^ 1227871812) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 181976875977 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 943005552043) ^ 4911487250 = 589350358302 := by
        calc
          (2 : ZMod 943005552043) ^ 4911487250 = (2 : ZMod 943005552043) ^ (2455743625 + 2455743625) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 2455743625 * (2 : ZMod 943005552043) ^ 2455743625 := by rw [pow_add]
          _ = 589350358302 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 943005552043) ^ 9822974500 = 693473614440 := by
        calc
          (2 : ZMod 943005552043) ^ 9822974500 = (2 : ZMod 943005552043) ^ (4911487250 + 4911487250) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 4911487250 * (2 : ZMod 943005552043) ^ 4911487250 := by rw [pow_add]
          _ = 693473614440 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 943005552043) ^ 19645949000 = 588821702630 := by
        calc
          (2 : ZMod 943005552043) ^ 19645949000 = (2 : ZMod 943005552043) ^ (9822974500 + 9822974500) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 9822974500 * (2 : ZMod 943005552043) ^ 9822974500 := by rw [pow_add]
          _ = 588821702630 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 943005552043) ^ 39291898001 = 308345710644 := by
        calc
          (2 : ZMod 943005552043) ^ 39291898001 = (2 : ZMod 943005552043) ^ (19645949000 + 19645949000 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 19645949000 * (2 : ZMod 943005552043) ^ 19645949000) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 308345710644 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 943005552043) ^ 78583796003 = 56308423330 := by
        calc
          (2 : ZMod 943005552043) ^ 78583796003 = (2 : ZMod 943005552043) ^ (39291898001 + 39291898001 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 39291898001 * (2 : ZMod 943005552043) ^ 39291898001) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 56308423330 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 943005552043) ^ 157167592007 = 461452513267 := by
        calc
          (2 : ZMod 943005552043) ^ 157167592007 = (2 : ZMod 943005552043) ^ (78583796003 + 78583796003 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 78583796003 * (2 : ZMod 943005552043) ^ 78583796003) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 461452513267 := by rw [factor_1_36]; decide
      have factor_1_38 : (2 : ZMod 943005552043) ^ 314335184014 = 461452513266 := by
        calc
          (2 : ZMod 943005552043) ^ 314335184014 = (2 : ZMod 943005552043) ^ (157167592007 + 157167592007) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 157167592007 * (2 : ZMod 943005552043) ^ 157167592007 := by rw [pow_add]
          _ = 461452513266 := by rw [factor_1_37]; decide
      change (2 : ZMod 943005552043) ^ 314335184014 ≠ 1
      rw [factor_1_38]
      decide
    ·
      have factor_2_0 : (2 : ZMod 943005552043) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 943005552043) ^ 3 = 8 := by
        calc
          (2 : ZMod 943005552043) ^ 3 = (2 : ZMod 943005552043) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1 * (2 : ZMod 943005552043) ^ 1) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 943005552043) ^ 6 = 64 := by
        calc
          (2 : ZMod 943005552043) ^ 6 = (2 : ZMod 943005552043) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 3 * (2 : ZMod 943005552043) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 943005552043) ^ 12 = 4096 := by
        calc
          (2 : ZMod 943005552043) ^ 12 = (2 : ZMod 943005552043) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 6 * (2 : ZMod 943005552043) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 943005552043) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 943005552043) ^ 25 = (2 : ZMod 943005552043) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 12 * (2 : ZMod 943005552043) ^ 12) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 943005552043) ^ 51 = 845560958607 := by
        calc
          (2 : ZMod 943005552043) ^ 51 = (2 : ZMod 943005552043) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 25 * (2 : ZMod 943005552043) ^ 25) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 845560958607 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 943005552043) ^ 103 = 340356772097 := by
        calc
          (2 : ZMod 943005552043) ^ 103 = (2 : ZMod 943005552043) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 51 * (2 : ZMod 943005552043) ^ 51) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 340356772097 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 943005552043) ^ 206 = 238034224160 := by
        calc
          (2 : ZMod 943005552043) ^ 206 = (2 : ZMod 943005552043) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 103 * (2 : ZMod 943005552043) ^ 103 := by rw [pow_add]
          _ = 238034224160 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 943005552043) ^ 413 = 333402103918 := by
        calc
          (2 : ZMod 943005552043) ^ 413 = (2 : ZMod 943005552043) ^ (206 + 206 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 206 * (2 : ZMod 943005552043) ^ 206) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 333402103918 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 943005552043) ^ 826 = 409168161633 := by
        calc
          (2 : ZMod 943005552043) ^ 826 = (2 : ZMod 943005552043) ^ (413 + 413) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 413 * (2 : ZMod 943005552043) ^ 413 := by rw [pow_add]
          _ = 409168161633 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 943005552043) ^ 1653 = 734548062418 := by
        calc
          (2 : ZMod 943005552043) ^ 1653 = (2 : ZMod 943005552043) ^ (826 + 826 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 826 * (2 : ZMod 943005552043) ^ 826) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 734548062418 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 943005552043) ^ 3306 = 268881072660 := by
        calc
          (2 : ZMod 943005552043) ^ 3306 = (2 : ZMod 943005552043) ^ (1653 + 1653) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 1653 * (2 : ZMod 943005552043) ^ 1653 := by rw [pow_add]
          _ = 268881072660 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 943005552043) ^ 6612 = 23864522502 := by
        calc
          (2 : ZMod 943005552043) ^ 6612 = (2 : ZMod 943005552043) ^ (3306 + 3306) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 3306 * (2 : ZMod 943005552043) ^ 3306 := by rw [pow_add]
          _ = 23864522502 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 943005552043) ^ 13225 = 660549408534 := by
        calc
          (2 : ZMod 943005552043) ^ 13225 = (2 : ZMod 943005552043) ^ (6612 + 6612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 6612 * (2 : ZMod 943005552043) ^ 6612) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 660549408534 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 943005552043) ^ 26450 = 35223550037 := by
        calc
          (2 : ZMod 943005552043) ^ 26450 = (2 : ZMod 943005552043) ^ (13225 + 13225) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 13225 * (2 : ZMod 943005552043) ^ 13225 := by rw [pow_add]
          _ = 35223550037 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 943005552043) ^ 52901 = 213137000915 := by
        calc
          (2 : ZMod 943005552043) ^ 52901 = (2 : ZMod 943005552043) ^ (26450 + 26450 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 26450 * (2 : ZMod 943005552043) ^ 26450) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 213137000915 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 943005552043) ^ 105802 = 369227598872 := by
        calc
          (2 : ZMod 943005552043) ^ 105802 = (2 : ZMod 943005552043) ^ (52901 + 52901) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 52901 * (2 : ZMod 943005552043) ^ 52901 := by rw [pow_add]
          _ = 369227598872 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 943005552043) ^ 211604 = 714054290760 := by
        calc
          (2 : ZMod 943005552043) ^ 211604 = (2 : ZMod 943005552043) ^ (105802 + 105802) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 105802 * (2 : ZMod 943005552043) ^ 105802 := by rw [pow_add]
          _ = 714054290760 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 943005552043) ^ 423209 = 929413189386 := by
        calc
          (2 : ZMod 943005552043) ^ 423209 = (2 : ZMod 943005552043) ^ (211604 + 211604 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 211604 * (2 : ZMod 943005552043) ^ 211604) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 929413189386 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 943005552043) ^ 846418 = 708949712107 := by
        calc
          (2 : ZMod 943005552043) ^ 846418 = (2 : ZMod 943005552043) ^ (423209 + 423209) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 423209 * (2 : ZMod 943005552043) ^ 423209 := by rw [pow_add]
          _ = 708949712107 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 943005552043) ^ 1692837 = 130605694248 := by
        calc
          (2 : ZMod 943005552043) ^ 1692837 = (2 : ZMod 943005552043) ^ (846418 + 846418 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 846418 * (2 : ZMod 943005552043) ^ 846418) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 130605694248 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 943005552043) ^ 3385675 = 696725168192 := by
        calc
          (2 : ZMod 943005552043) ^ 3385675 = (2 : ZMod 943005552043) ^ (1692837 + 1692837 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1692837 * (2 : ZMod 943005552043) ^ 1692837) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 696725168192 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 943005552043) ^ 6771351 = 508787627175 := by
        calc
          (2 : ZMod 943005552043) ^ 6771351 = (2 : ZMod 943005552043) ^ (3385675 + 3385675 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 3385675 * (2 : ZMod 943005552043) ^ 3385675) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 508787627175 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 943005552043) ^ 13542703 = 406938686828 := by
        calc
          (2 : ZMod 943005552043) ^ 13542703 = (2 : ZMod 943005552043) ^ (6771351 + 6771351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 6771351 * (2 : ZMod 943005552043) ^ 6771351) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 406938686828 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 943005552043) ^ 27085407 = 840202468809 := by
        calc
          (2 : ZMod 943005552043) ^ 27085407 = (2 : ZMod 943005552043) ^ (13542703 + 13542703 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 13542703 * (2 : ZMod 943005552043) ^ 13542703) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 840202468809 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 943005552043) ^ 54170815 = 450620342102 := by
        calc
          (2 : ZMod 943005552043) ^ 54170815 = (2 : ZMod 943005552043) ^ (27085407 + 27085407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 27085407 * (2 : ZMod 943005552043) ^ 27085407) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 450620342102 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 943005552043) ^ 108341630 = 408081771804 := by
        calc
          (2 : ZMod 943005552043) ^ 108341630 = (2 : ZMod 943005552043) ^ (54170815 + 54170815) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 54170815 * (2 : ZMod 943005552043) ^ 54170815 := by rw [pow_add]
          _ = 408081771804 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 943005552043) ^ 216683261 = 25441230495 := by
        calc
          (2 : ZMod 943005552043) ^ 216683261 = (2 : ZMod 943005552043) ^ (108341630 + 108341630 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 108341630 * (2 : ZMod 943005552043) ^ 108341630) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 25441230495 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 943005552043) ^ 433366522 = 51651144765 := by
        calc
          (2 : ZMod 943005552043) ^ 433366522 = (2 : ZMod 943005552043) ^ (216683261 + 216683261) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 216683261 * (2 : ZMod 943005552043) ^ 216683261 := by rw [pow_add]
          _ = 51651144765 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 943005552043) ^ 866733044 = 7819514287 := by
        calc
          (2 : ZMod 943005552043) ^ 866733044 = (2 : ZMod 943005552043) ^ (433366522 + 433366522) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 433366522 * (2 : ZMod 943005552043) ^ 433366522 := by rw [pow_add]
          _ = 7819514287 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 943005552043) ^ 1733466088 = 239224647620 := by
        calc
          (2 : ZMod 943005552043) ^ 1733466088 = (2 : ZMod 943005552043) ^ (866733044 + 866733044) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 866733044 * (2 : ZMod 943005552043) ^ 866733044 := by rw [pow_add]
          _ = 239224647620 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 943005552043) ^ 3466932176 = 176638230093 := by
        calc
          (2 : ZMod 943005552043) ^ 3466932176 = (2 : ZMod 943005552043) ^ (1733466088 + 1733466088) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 1733466088 * (2 : ZMod 943005552043) ^ 1733466088 := by rw [pow_add]
          _ = 176638230093 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 943005552043) ^ 6933864353 = 588133754716 := by
        calc
          (2 : ZMod 943005552043) ^ 6933864353 = (2 : ZMod 943005552043) ^ (3466932176 + 3466932176 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 3466932176 * (2 : ZMod 943005552043) ^ 3466932176) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 588133754716 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 943005552043) ^ 13867728706 = 709917843587 := by
        calc
          (2 : ZMod 943005552043) ^ 13867728706 = (2 : ZMod 943005552043) ^ (6933864353 + 6933864353) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 6933864353 * (2 : ZMod 943005552043) ^ 6933864353 := by rw [pow_add]
          _ = 709917843587 := by rw [factor_2_32]; decide
      have factor_2_34 : (2 : ZMod 943005552043) ^ 27735457413 = 406844057146 := by
        calc
          (2 : ZMod 943005552043) ^ 27735457413 = (2 : ZMod 943005552043) ^ (13867728706 + 13867728706 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 13867728706 * (2 : ZMod 943005552043) ^ 13867728706) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 406844057146 := by rw [factor_2_33]; decide
      have factor_2_35 : (2 : ZMod 943005552043) ^ 55470914826 = 904858053058 := by
        calc
          (2 : ZMod 943005552043) ^ 55470914826 = (2 : ZMod 943005552043) ^ (27735457413 + 27735457413) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 27735457413 * (2 : ZMod 943005552043) ^ 27735457413 := by rw [pow_add]
          _ = 904858053058 := by rw [factor_2_34]; decide
      change (2 : ZMod 943005552043) ^ 55470914826 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (2 : ZMod 943005552043) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 943005552043) ^ 3 = 8 := by
        calc
          (2 : ZMod 943005552043) ^ 3 = (2 : ZMod 943005552043) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 1 * (2 : ZMod 943005552043) ^ 1) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 943005552043) ^ 6 = 64 := by
        calc
          (2 : ZMod 943005552043) ^ 6 = (2 : ZMod 943005552043) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 3 * (2 : ZMod 943005552043) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 943005552043) ^ 12 = 4096 := by
        calc
          (2 : ZMod 943005552043) ^ 12 = (2 : ZMod 943005552043) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 6 * (2 : ZMod 943005552043) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 943005552043) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 943005552043) ^ 25 = (2 : ZMod 943005552043) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 12 * (2 : ZMod 943005552043) ^ 12) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 943005552043) ^ 51 = 845560958607 := by
        calc
          (2 : ZMod 943005552043) ^ 51 = (2 : ZMod 943005552043) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = ((2 : ZMod 943005552043) ^ 25 * (2 : ZMod 943005552043) ^ 25) * (2 : ZMod 943005552043) := by rw [pow_succ, pow_add]
          _ = 845560958607 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 943005552043) ^ 102 = 641681162070 := by
        calc
          (2 : ZMod 943005552043) ^ 102 = (2 : ZMod 943005552043) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 943005552043) ^ n) (by norm_num)
          _ = (2 : ZMod 943005552043) ^ 51 * (2 : ZMod 943005552043) ^ 51 := by rw [pow_add]
          _ = 641681162070 := by rw [factor_3_5]; decide
      change (2 : ZMod 943005552043) ^ 102 ≠ 1
      rw [factor_3_6]
      decide

#print axioms prime_lucas_943005552043

end TotientTailPeriodKiller
end Erdos249257
