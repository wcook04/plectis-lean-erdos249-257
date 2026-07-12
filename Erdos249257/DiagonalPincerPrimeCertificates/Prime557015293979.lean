import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime45293161

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_557015293979 : Nat.Prime 557015293979 := by
  apply lucas_primality 557015293979 (2 : ZMod 557015293979)
  ·
      have fermat_0 : (2 : ZMod 557015293979) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 557015293979) ^ 2 = 4 := by
        calc
          (2 : ZMod 557015293979) ^ 2 = (2 : ZMod 557015293979) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1 * (2 : ZMod 557015293979) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 557015293979) ^ 4 = 16 := by
        calc
          (2 : ZMod 557015293979) ^ 4 = (2 : ZMod 557015293979) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 2 * (2 : ZMod 557015293979) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 557015293979) ^ 8 = 256 := by
        calc
          (2 : ZMod 557015293979) ^ 8 = (2 : ZMod 557015293979) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 4 * (2 : ZMod 557015293979) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 557015293979) ^ 16 = 65536 := by
        calc
          (2 : ZMod 557015293979) ^ 16 = (2 : ZMod 557015293979) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 8 * (2 : ZMod 557015293979) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 557015293979) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 557015293979) ^ 32 = (2 : ZMod 557015293979) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 16 * (2 : ZMod 557015293979) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 557015293979) ^ 64 = 70125849199 := by
        calc
          (2 : ZMod 557015293979) ^ 64 = (2 : ZMod 557015293979) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 32 * (2 : ZMod 557015293979) ^ 32 := by rw [pow_add]
          _ = 70125849199 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 557015293979) ^ 129 = 546592135534 := by
        calc
          (2 : ZMod 557015293979) ^ 129 = (2 : ZMod 557015293979) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 64 * (2 : ZMod 557015293979) ^ 64) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 546592135534 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 557015293979) ^ 259 = 522708178499 := by
        calc
          (2 : ZMod 557015293979) ^ 259 = (2 : ZMod 557015293979) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 129 * (2 : ZMod 557015293979) ^ 129) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 522708178499 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 557015293979) ^ 518 = 321095721478 := by
        calc
          (2 : ZMod 557015293979) ^ 518 = (2 : ZMod 557015293979) ^ (259 + 259) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 259 * (2 : ZMod 557015293979) ^ 259 := by rw [pow_add]
          _ = 321095721478 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 557015293979) ^ 1037 = 358074937218 := by
        calc
          (2 : ZMod 557015293979) ^ 1037 = (2 : ZMod 557015293979) ^ (518 + 518 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 518 * (2 : ZMod 557015293979) ^ 518) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 358074937218 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 557015293979) ^ 2075 = 102153676624 := by
        calc
          (2 : ZMod 557015293979) ^ 2075 = (2 : ZMod 557015293979) ^ (1037 + 1037 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 1037 * (2 : ZMod 557015293979) ^ 1037) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 102153676624 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 557015293979) ^ 4150 = 294808283815 := by
        calc
          (2 : ZMod 557015293979) ^ 4150 = (2 : ZMod 557015293979) ^ (2075 + 2075) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 2075 * (2 : ZMod 557015293979) ^ 2075 := by rw [pow_add]
          _ = 294808283815 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 557015293979) ^ 8300 = 140932906315 := by
        calc
          (2 : ZMod 557015293979) ^ 8300 = (2 : ZMod 557015293979) ^ (4150 + 4150) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 4150 * (2 : ZMod 557015293979) ^ 4150 := by rw [pow_add]
          _ = 140932906315 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 557015293979) ^ 16600 = 27725967164 := by
        calc
          (2 : ZMod 557015293979) ^ 16600 = (2 : ZMod 557015293979) ^ (8300 + 8300) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 8300 * (2 : ZMod 557015293979) ^ 8300 := by rw [pow_add]
          _ = 27725967164 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 557015293979) ^ 33200 = 529159364157 := by
        calc
          (2 : ZMod 557015293979) ^ 33200 = (2 : ZMod 557015293979) ^ (16600 + 16600) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 16600 * (2 : ZMod 557015293979) ^ 16600 := by rw [pow_add]
          _ = 529159364157 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 557015293979) ^ 66401 = 164816744758 := by
        calc
          (2 : ZMod 557015293979) ^ 66401 = (2 : ZMod 557015293979) ^ (33200 + 33200 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 33200 * (2 : ZMod 557015293979) ^ 33200) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 164816744758 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 557015293979) ^ 132802 = 371334282179 := by
        calc
          (2 : ZMod 557015293979) ^ 132802 = (2 : ZMod 557015293979) ^ (66401 + 66401) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 66401 * (2 : ZMod 557015293979) ^ 66401 := by rw [pow_add]
          _ = 371334282179 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 557015293979) ^ 265605 = 139294613607 := by
        calc
          (2 : ZMod 557015293979) ^ 265605 = (2 : ZMod 557015293979) ^ (132802 + 132802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 132802 * (2 : ZMod 557015293979) ^ 132802) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 139294613607 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 557015293979) ^ 531211 = 405283063391 := by
        calc
          (2 : ZMod 557015293979) ^ 531211 = (2 : ZMod 557015293979) ^ (265605 + 265605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 265605 * (2 : ZMod 557015293979) ^ 265605) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 405283063391 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 557015293979) ^ 1062422 = 29978413151 := by
        calc
          (2 : ZMod 557015293979) ^ 1062422 = (2 : ZMod 557015293979) ^ (531211 + 531211) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 531211 * (2 : ZMod 557015293979) ^ 531211 := by rw [pow_add]
          _ = 29978413151 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 557015293979) ^ 2124844 = 217615325405 := by
        calc
          (2 : ZMod 557015293979) ^ 2124844 = (2 : ZMod 557015293979) ^ (1062422 + 1062422) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1062422 * (2 : ZMod 557015293979) ^ 1062422 := by rw [pow_add]
          _ = 217615325405 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 557015293979) ^ 4249689 = 80420866748 := by
        calc
          (2 : ZMod 557015293979) ^ 4249689 = (2 : ZMod 557015293979) ^ (2124844 + 2124844 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 2124844 * (2 : ZMod 557015293979) ^ 2124844) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 80420866748 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 557015293979) ^ 8499378 = 124061184885 := by
        calc
          (2 : ZMod 557015293979) ^ 8499378 = (2 : ZMod 557015293979) ^ (4249689 + 4249689) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 4249689 * (2 : ZMod 557015293979) ^ 4249689 := by rw [pow_add]
          _ = 124061184885 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 557015293979) ^ 16998757 = 301180890718 := by
        calc
          (2 : ZMod 557015293979) ^ 16998757 = (2 : ZMod 557015293979) ^ (8499378 + 8499378 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 8499378 * (2 : ZMod 557015293979) ^ 8499378) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 301180890718 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 557015293979) ^ 33997515 = 246412467531 := by
        calc
          (2 : ZMod 557015293979) ^ 33997515 = (2 : ZMod 557015293979) ^ (16998757 + 16998757 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 16998757 * (2 : ZMod 557015293979) ^ 16998757) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 246412467531 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 557015293979) ^ 67995031 = 284592066420 := by
        calc
          (2 : ZMod 557015293979) ^ 67995031 = (2 : ZMod 557015293979) ^ (33997515 + 33997515 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 33997515 * (2 : ZMod 557015293979) ^ 33997515) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 284592066420 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 557015293979) ^ 135990062 = 533313304622 := by
        calc
          (2 : ZMod 557015293979) ^ 135990062 = (2 : ZMod 557015293979) ^ (67995031 + 67995031) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 67995031 * (2 : ZMod 557015293979) ^ 67995031 := by rw [pow_add]
          _ = 533313304622 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 557015293979) ^ 271980124 = 416682447422 := by
        calc
          (2 : ZMod 557015293979) ^ 271980124 = (2 : ZMod 557015293979) ^ (135990062 + 135990062) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 135990062 * (2 : ZMod 557015293979) ^ 135990062 := by rw [pow_add]
          _ = 416682447422 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 557015293979) ^ 543960248 = 29477980605 := by
        calc
          (2 : ZMod 557015293979) ^ 543960248 = (2 : ZMod 557015293979) ^ (271980124 + 271980124) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 271980124 * (2 : ZMod 557015293979) ^ 271980124 := by rw [pow_add]
          _ = 29477980605 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 557015293979) ^ 1087920496 = 112087440097 := by
        calc
          (2 : ZMod 557015293979) ^ 1087920496 = (2 : ZMod 557015293979) ^ (543960248 + 543960248) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 543960248 * (2 : ZMod 557015293979) ^ 543960248 := by rw [pow_add]
          _ = 112087440097 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 557015293979) ^ 2175840992 = 114658577559 := by
        calc
          (2 : ZMod 557015293979) ^ 2175840992 = (2 : ZMod 557015293979) ^ (1087920496 + 1087920496) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1087920496 * (2 : ZMod 557015293979) ^ 1087920496 := by rw [pow_add]
          _ = 114658577559 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 557015293979) ^ 4351681984 = 252107336755 := by
        calc
          (2 : ZMod 557015293979) ^ 4351681984 = (2 : ZMod 557015293979) ^ (2175840992 + 2175840992) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 2175840992 * (2 : ZMod 557015293979) ^ 2175840992 := by rw [pow_add]
          _ = 252107336755 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 557015293979) ^ 8703363968 = 215018254962 := by
        calc
          (2 : ZMod 557015293979) ^ 8703363968 = (2 : ZMod 557015293979) ^ (4351681984 + 4351681984) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 4351681984 * (2 : ZMod 557015293979) ^ 4351681984 := by rw [pow_add]
          _ = 215018254962 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 557015293979) ^ 17406727936 = 189013895345 := by
        calc
          (2 : ZMod 557015293979) ^ 17406727936 = (2 : ZMod 557015293979) ^ (8703363968 + 8703363968) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 8703363968 * (2 : ZMod 557015293979) ^ 8703363968 := by rw [pow_add]
          _ = 189013895345 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 557015293979) ^ 34813455873 = 97945661212 := by
        calc
          (2 : ZMod 557015293979) ^ 34813455873 = (2 : ZMod 557015293979) ^ (17406727936 + 17406727936 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 17406727936 * (2 : ZMod 557015293979) ^ 17406727936) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 97945661212 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 557015293979) ^ 69626911747 = 25840895569 := by
        calc
          (2 : ZMod 557015293979) ^ 69626911747 = (2 : ZMod 557015293979) ^ (34813455873 + 34813455873 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 34813455873 * (2 : ZMod 557015293979) ^ 34813455873) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 25840895569 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 557015293979) ^ 139253823494 = 389425001240 := by
        calc
          (2 : ZMod 557015293979) ^ 139253823494 = (2 : ZMod 557015293979) ^ (69626911747 + 69626911747) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 69626911747 * (2 : ZMod 557015293979) ^ 69626911747 := by rw [pow_add]
          _ = 389425001240 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 557015293979) ^ 278507646989 = 557015293978 := by
        calc
          (2 : ZMod 557015293979) ^ 278507646989 = (2 : ZMod 557015293979) ^ (139253823494 + 139253823494 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 139253823494 * (2 : ZMod 557015293979) ^ 139253823494) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 557015293978 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 557015293979) ^ 557015293978 = 1 := by
        calc
          (2 : ZMod 557015293979) ^ 557015293978 = (2 : ZMod 557015293979) ^ (278507646989 + 278507646989) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 278507646989 * (2 : ZMod 557015293979) ^ 278507646989 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (13, 1), (43, 1), (45293161, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (13, 1), (43, 1), (45293161, 1)] : List FactorBlock).map factorBlockValue).prod = 557015293979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_45293161) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 557015293979) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 557015293979) ^ 2 = 4 := by
        calc
          (2 : ZMod 557015293979) ^ 2 = (2 : ZMod 557015293979) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1 * (2 : ZMod 557015293979) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 557015293979) ^ 4 = 16 := by
        calc
          (2 : ZMod 557015293979) ^ 4 = (2 : ZMod 557015293979) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 2 * (2 : ZMod 557015293979) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 557015293979) ^ 8 = 256 := by
        calc
          (2 : ZMod 557015293979) ^ 8 = (2 : ZMod 557015293979) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 4 * (2 : ZMod 557015293979) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 557015293979) ^ 16 = 65536 := by
        calc
          (2 : ZMod 557015293979) ^ 16 = (2 : ZMod 557015293979) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 8 * (2 : ZMod 557015293979) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 557015293979) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 557015293979) ^ 32 = (2 : ZMod 557015293979) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 16 * (2 : ZMod 557015293979) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 557015293979) ^ 64 = 70125849199 := by
        calc
          (2 : ZMod 557015293979) ^ 64 = (2 : ZMod 557015293979) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 32 * (2 : ZMod 557015293979) ^ 32 := by rw [pow_add]
          _ = 70125849199 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 557015293979) ^ 129 = 546592135534 := by
        calc
          (2 : ZMod 557015293979) ^ 129 = (2 : ZMod 557015293979) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 64 * (2 : ZMod 557015293979) ^ 64) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 546592135534 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 557015293979) ^ 259 = 522708178499 := by
        calc
          (2 : ZMod 557015293979) ^ 259 = (2 : ZMod 557015293979) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 129 * (2 : ZMod 557015293979) ^ 129) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 522708178499 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 557015293979) ^ 518 = 321095721478 := by
        calc
          (2 : ZMod 557015293979) ^ 518 = (2 : ZMod 557015293979) ^ (259 + 259) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 259 * (2 : ZMod 557015293979) ^ 259 := by rw [pow_add]
          _ = 321095721478 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 557015293979) ^ 1037 = 358074937218 := by
        calc
          (2 : ZMod 557015293979) ^ 1037 = (2 : ZMod 557015293979) ^ (518 + 518 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 518 * (2 : ZMod 557015293979) ^ 518) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 358074937218 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 557015293979) ^ 2075 = 102153676624 := by
        calc
          (2 : ZMod 557015293979) ^ 2075 = (2 : ZMod 557015293979) ^ (1037 + 1037 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 1037 * (2 : ZMod 557015293979) ^ 1037) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 102153676624 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 557015293979) ^ 4150 = 294808283815 := by
        calc
          (2 : ZMod 557015293979) ^ 4150 = (2 : ZMod 557015293979) ^ (2075 + 2075) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 2075 * (2 : ZMod 557015293979) ^ 2075 := by rw [pow_add]
          _ = 294808283815 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 557015293979) ^ 8300 = 140932906315 := by
        calc
          (2 : ZMod 557015293979) ^ 8300 = (2 : ZMod 557015293979) ^ (4150 + 4150) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 4150 * (2 : ZMod 557015293979) ^ 4150 := by rw [pow_add]
          _ = 140932906315 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 557015293979) ^ 16600 = 27725967164 := by
        calc
          (2 : ZMod 557015293979) ^ 16600 = (2 : ZMod 557015293979) ^ (8300 + 8300) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 8300 * (2 : ZMod 557015293979) ^ 8300 := by rw [pow_add]
          _ = 27725967164 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 557015293979) ^ 33200 = 529159364157 := by
        calc
          (2 : ZMod 557015293979) ^ 33200 = (2 : ZMod 557015293979) ^ (16600 + 16600) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 16600 * (2 : ZMod 557015293979) ^ 16600 := by rw [pow_add]
          _ = 529159364157 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 557015293979) ^ 66401 = 164816744758 := by
        calc
          (2 : ZMod 557015293979) ^ 66401 = (2 : ZMod 557015293979) ^ (33200 + 33200 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 33200 * (2 : ZMod 557015293979) ^ 33200) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 164816744758 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 557015293979) ^ 132802 = 371334282179 := by
        calc
          (2 : ZMod 557015293979) ^ 132802 = (2 : ZMod 557015293979) ^ (66401 + 66401) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 66401 * (2 : ZMod 557015293979) ^ 66401 := by rw [pow_add]
          _ = 371334282179 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 557015293979) ^ 265605 = 139294613607 := by
        calc
          (2 : ZMod 557015293979) ^ 265605 = (2 : ZMod 557015293979) ^ (132802 + 132802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 132802 * (2 : ZMod 557015293979) ^ 132802) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 139294613607 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 557015293979) ^ 531211 = 405283063391 := by
        calc
          (2 : ZMod 557015293979) ^ 531211 = (2 : ZMod 557015293979) ^ (265605 + 265605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 265605 * (2 : ZMod 557015293979) ^ 265605) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 405283063391 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 557015293979) ^ 1062422 = 29978413151 := by
        calc
          (2 : ZMod 557015293979) ^ 1062422 = (2 : ZMod 557015293979) ^ (531211 + 531211) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 531211 * (2 : ZMod 557015293979) ^ 531211 := by rw [pow_add]
          _ = 29978413151 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 557015293979) ^ 2124844 = 217615325405 := by
        calc
          (2 : ZMod 557015293979) ^ 2124844 = (2 : ZMod 557015293979) ^ (1062422 + 1062422) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1062422 * (2 : ZMod 557015293979) ^ 1062422 := by rw [pow_add]
          _ = 217615325405 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 557015293979) ^ 4249689 = 80420866748 := by
        calc
          (2 : ZMod 557015293979) ^ 4249689 = (2 : ZMod 557015293979) ^ (2124844 + 2124844 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 2124844 * (2 : ZMod 557015293979) ^ 2124844) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 80420866748 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 557015293979) ^ 8499378 = 124061184885 := by
        calc
          (2 : ZMod 557015293979) ^ 8499378 = (2 : ZMod 557015293979) ^ (4249689 + 4249689) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 4249689 * (2 : ZMod 557015293979) ^ 4249689 := by rw [pow_add]
          _ = 124061184885 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 557015293979) ^ 16998757 = 301180890718 := by
        calc
          (2 : ZMod 557015293979) ^ 16998757 = (2 : ZMod 557015293979) ^ (8499378 + 8499378 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 8499378 * (2 : ZMod 557015293979) ^ 8499378) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 301180890718 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 557015293979) ^ 33997515 = 246412467531 := by
        calc
          (2 : ZMod 557015293979) ^ 33997515 = (2 : ZMod 557015293979) ^ (16998757 + 16998757 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 16998757 * (2 : ZMod 557015293979) ^ 16998757) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 246412467531 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 557015293979) ^ 67995031 = 284592066420 := by
        calc
          (2 : ZMod 557015293979) ^ 67995031 = (2 : ZMod 557015293979) ^ (33997515 + 33997515 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 33997515 * (2 : ZMod 557015293979) ^ 33997515) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 284592066420 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 557015293979) ^ 135990062 = 533313304622 := by
        calc
          (2 : ZMod 557015293979) ^ 135990062 = (2 : ZMod 557015293979) ^ (67995031 + 67995031) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 67995031 * (2 : ZMod 557015293979) ^ 67995031 := by rw [pow_add]
          _ = 533313304622 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 557015293979) ^ 271980124 = 416682447422 := by
        calc
          (2 : ZMod 557015293979) ^ 271980124 = (2 : ZMod 557015293979) ^ (135990062 + 135990062) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 135990062 * (2 : ZMod 557015293979) ^ 135990062 := by rw [pow_add]
          _ = 416682447422 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 557015293979) ^ 543960248 = 29477980605 := by
        calc
          (2 : ZMod 557015293979) ^ 543960248 = (2 : ZMod 557015293979) ^ (271980124 + 271980124) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 271980124 * (2 : ZMod 557015293979) ^ 271980124 := by rw [pow_add]
          _ = 29477980605 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 557015293979) ^ 1087920496 = 112087440097 := by
        calc
          (2 : ZMod 557015293979) ^ 1087920496 = (2 : ZMod 557015293979) ^ (543960248 + 543960248) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 543960248 * (2 : ZMod 557015293979) ^ 543960248 := by rw [pow_add]
          _ = 112087440097 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 557015293979) ^ 2175840992 = 114658577559 := by
        calc
          (2 : ZMod 557015293979) ^ 2175840992 = (2 : ZMod 557015293979) ^ (1087920496 + 1087920496) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1087920496 * (2 : ZMod 557015293979) ^ 1087920496 := by rw [pow_add]
          _ = 114658577559 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 557015293979) ^ 4351681984 = 252107336755 := by
        calc
          (2 : ZMod 557015293979) ^ 4351681984 = (2 : ZMod 557015293979) ^ (2175840992 + 2175840992) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 2175840992 * (2 : ZMod 557015293979) ^ 2175840992 := by rw [pow_add]
          _ = 252107336755 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 557015293979) ^ 8703363968 = 215018254962 := by
        calc
          (2 : ZMod 557015293979) ^ 8703363968 = (2 : ZMod 557015293979) ^ (4351681984 + 4351681984) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 4351681984 * (2 : ZMod 557015293979) ^ 4351681984 := by rw [pow_add]
          _ = 215018254962 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 557015293979) ^ 17406727936 = 189013895345 := by
        calc
          (2 : ZMod 557015293979) ^ 17406727936 = (2 : ZMod 557015293979) ^ (8703363968 + 8703363968) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 8703363968 * (2 : ZMod 557015293979) ^ 8703363968 := by rw [pow_add]
          _ = 189013895345 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 557015293979) ^ 34813455873 = 97945661212 := by
        calc
          (2 : ZMod 557015293979) ^ 34813455873 = (2 : ZMod 557015293979) ^ (17406727936 + 17406727936 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 17406727936 * (2 : ZMod 557015293979) ^ 17406727936) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 97945661212 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 557015293979) ^ 69626911747 = 25840895569 := by
        calc
          (2 : ZMod 557015293979) ^ 69626911747 = (2 : ZMod 557015293979) ^ (34813455873 + 34813455873 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 34813455873 * (2 : ZMod 557015293979) ^ 34813455873) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 25840895569 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 557015293979) ^ 139253823494 = 389425001240 := by
        calc
          (2 : ZMod 557015293979) ^ 139253823494 = (2 : ZMod 557015293979) ^ (69626911747 + 69626911747) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 69626911747 * (2 : ZMod 557015293979) ^ 69626911747 := by rw [pow_add]
          _ = 389425001240 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 557015293979) ^ 278507646989 = 557015293978 := by
        calc
          (2 : ZMod 557015293979) ^ 278507646989 = (2 : ZMod 557015293979) ^ (139253823494 + 139253823494 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 139253823494 * (2 : ZMod 557015293979) ^ 139253823494) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 557015293978 := by rw [factor_0_37]; decide
      change (2 : ZMod 557015293979) ^ 278507646989 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (2 : ZMod 557015293979) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 557015293979) ^ 2 = 4 := by
        calc
          (2 : ZMod 557015293979) ^ 2 = (2 : ZMod 557015293979) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1 * (2 : ZMod 557015293979) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 557015293979) ^ 5 = 32 := by
        calc
          (2 : ZMod 557015293979) ^ 5 = (2 : ZMod 557015293979) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 2 * (2 : ZMod 557015293979) ^ 2) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 557015293979) ^ 11 = 2048 := by
        calc
          (2 : ZMod 557015293979) ^ 11 = (2 : ZMod 557015293979) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 5 * (2 : ZMod 557015293979) ^ 5) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 557015293979) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 557015293979) ^ 23 = (2 : ZMod 557015293979) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 11 * (2 : ZMod 557015293979) ^ 11) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 557015293979) ^ 47 = 369634272620 := by
        calc
          (2 : ZMod 557015293979) ^ 47 = (2 : ZMod 557015293979) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 23 * (2 : ZMod 557015293979) ^ 23) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 369634272620 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 557015293979) ^ 94 = 497834852770 := by
        calc
          (2 : ZMod 557015293979) ^ 94 = (2 : ZMod 557015293979) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 47 * (2 : ZMod 557015293979) ^ 47 := by rw [pow_add]
          _ = 497834852770 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 557015293979) ^ 188 = 201436110981 := by
        calc
          (2 : ZMod 557015293979) ^ 188 = (2 : ZMod 557015293979) ^ (94 + 94) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 94 * (2 : ZMod 557015293979) ^ 94 := by rw [pow_add]
          _ = 201436110981 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 557015293979) ^ 377 = 325105131958 := by
        calc
          (2 : ZMod 557015293979) ^ 377 = (2 : ZMod 557015293979) ^ (188 + 188 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 188 * (2 : ZMod 557015293979) ^ 188) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 325105131958 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 557015293979) ^ 754 = 531434003150 := by
        calc
          (2 : ZMod 557015293979) ^ 754 = (2 : ZMod 557015293979) ^ (377 + 377) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 377 * (2 : ZMod 557015293979) ^ 377 := by rw [pow_add]
          _ = 531434003150 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 557015293979) ^ 1509 = 154478064348 := by
        calc
          (2 : ZMod 557015293979) ^ 1509 = (2 : ZMod 557015293979) ^ (754 + 754 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 754 * (2 : ZMod 557015293979) ^ 754) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 154478064348 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 557015293979) ^ 3018 = 210563113310 := by
        calc
          (2 : ZMod 557015293979) ^ 3018 = (2 : ZMod 557015293979) ^ (1509 + 1509) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1509 * (2 : ZMod 557015293979) ^ 1509 := by rw [pow_add]
          _ = 210563113310 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 557015293979) ^ 6036 = 6674477288 := by
        calc
          (2 : ZMod 557015293979) ^ 6036 = (2 : ZMod 557015293979) ^ (3018 + 3018) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 3018 * (2 : ZMod 557015293979) ^ 3018 := by rw [pow_add]
          _ = 6674477288 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 557015293979) ^ 12072 = 398030586785 := by
        calc
          (2 : ZMod 557015293979) ^ 12072 = (2 : ZMod 557015293979) ^ (6036 + 6036) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 6036 * (2 : ZMod 557015293979) ^ 6036 := by rw [pow_add]
          _ = 398030586785 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 557015293979) ^ 24145 = 368746075263 := by
        calc
          (2 : ZMod 557015293979) ^ 24145 = (2 : ZMod 557015293979) ^ (12072 + 12072 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 12072 * (2 : ZMod 557015293979) ^ 12072) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 368746075263 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 557015293979) ^ 48291 = 11397777079 := by
        calc
          (2 : ZMod 557015293979) ^ 48291 = (2 : ZMod 557015293979) ^ (24145 + 24145 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 24145 * (2 : ZMod 557015293979) ^ 24145) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 11397777079 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 557015293979) ^ 96583 = 461942475516 := by
        calc
          (2 : ZMod 557015293979) ^ 96583 = (2 : ZMod 557015293979) ^ (48291 + 48291 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 48291 * (2 : ZMod 557015293979) ^ 48291) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 461942475516 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 557015293979) ^ 193167 = 513931965094 := by
        calc
          (2 : ZMod 557015293979) ^ 193167 = (2 : ZMod 557015293979) ^ (96583 + 96583 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 96583 * (2 : ZMod 557015293979) ^ 96583) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 513931965094 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 557015293979) ^ 386335 = 147387506245 := by
        calc
          (2 : ZMod 557015293979) ^ 386335 = (2 : ZMod 557015293979) ^ (193167 + 193167 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 193167 * (2 : ZMod 557015293979) ^ 193167) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 147387506245 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 557015293979) ^ 772670 = 502971757572 := by
        calc
          (2 : ZMod 557015293979) ^ 772670 = (2 : ZMod 557015293979) ^ (386335 + 386335) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 386335 * (2 : ZMod 557015293979) ^ 386335 := by rw [pow_add]
          _ = 502971757572 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 557015293979) ^ 1545341 = 318863606933 := by
        calc
          (2 : ZMod 557015293979) ^ 1545341 = (2 : ZMod 557015293979) ^ (772670 + 772670 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 772670 * (2 : ZMod 557015293979) ^ 772670) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 318863606933 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 557015293979) ^ 3090683 = 2587264245 := by
        calc
          (2 : ZMod 557015293979) ^ 3090683 = (2 : ZMod 557015293979) ^ (1545341 + 1545341 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 1545341 * (2 : ZMod 557015293979) ^ 1545341) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 2587264245 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 557015293979) ^ 6181366 = 521940435693 := by
        calc
          (2 : ZMod 557015293979) ^ 6181366 = (2 : ZMod 557015293979) ^ (3090683 + 3090683) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 3090683 * (2 : ZMod 557015293979) ^ 3090683 := by rw [pow_add]
          _ = 521940435693 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 557015293979) ^ 12362732 = 286002978103 := by
        calc
          (2 : ZMod 557015293979) ^ 12362732 = (2 : ZMod 557015293979) ^ (6181366 + 6181366) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 6181366 * (2 : ZMod 557015293979) ^ 6181366 := by rw [pow_add]
          _ = 286002978103 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 557015293979) ^ 24725465 = 187586957473 := by
        calc
          (2 : ZMod 557015293979) ^ 24725465 = (2 : ZMod 557015293979) ^ (12362732 + 12362732 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 12362732 * (2 : ZMod 557015293979) ^ 12362732) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 187586957473 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 557015293979) ^ 49450931 = 263257992799 := by
        calc
          (2 : ZMod 557015293979) ^ 49450931 = (2 : ZMod 557015293979) ^ (24725465 + 24725465 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 24725465 * (2 : ZMod 557015293979) ^ 24725465) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 263257992799 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 557015293979) ^ 98901863 = 237820693872 := by
        calc
          (2 : ZMod 557015293979) ^ 98901863 = (2 : ZMod 557015293979) ^ (49450931 + 49450931 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 49450931 * (2 : ZMod 557015293979) ^ 49450931) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 237820693872 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 557015293979) ^ 197803726 = 127135255282 := by
        calc
          (2 : ZMod 557015293979) ^ 197803726 = (2 : ZMod 557015293979) ^ (98901863 + 98901863) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 98901863 * (2 : ZMod 557015293979) ^ 98901863 := by rw [pow_add]
          _ = 127135255282 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 557015293979) ^ 395607453 = 412653912305 := by
        calc
          (2 : ZMod 557015293979) ^ 395607453 = (2 : ZMod 557015293979) ^ (197803726 + 197803726 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 197803726 * (2 : ZMod 557015293979) ^ 197803726) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 412653912305 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 557015293979) ^ 791214906 = 55123048593 := by
        calc
          (2 : ZMod 557015293979) ^ 791214906 = (2 : ZMod 557015293979) ^ (395607453 + 395607453) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 395607453 * (2 : ZMod 557015293979) ^ 395607453 := by rw [pow_add]
          _ = 55123048593 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 557015293979) ^ 1582429812 = 186595200241 := by
        calc
          (2 : ZMod 557015293979) ^ 1582429812 = (2 : ZMod 557015293979) ^ (791214906 + 791214906) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 791214906 * (2 : ZMod 557015293979) ^ 791214906 := by rw [pow_add]
          _ = 186595200241 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 557015293979) ^ 3164859624 = 106584685679 := by
        calc
          (2 : ZMod 557015293979) ^ 3164859624 = (2 : ZMod 557015293979) ^ (1582429812 + 1582429812) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1582429812 * (2 : ZMod 557015293979) ^ 1582429812 := by rw [pow_add]
          _ = 106584685679 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 557015293979) ^ 6329719249 = 102790777883 := by
        calc
          (2 : ZMod 557015293979) ^ 6329719249 = (2 : ZMod 557015293979) ^ (3164859624 + 3164859624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 3164859624 * (2 : ZMod 557015293979) ^ 3164859624) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 102790777883 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 557015293979) ^ 12659438499 = 496549607546 := by
        calc
          (2 : ZMod 557015293979) ^ 12659438499 = (2 : ZMod 557015293979) ^ (6329719249 + 6329719249 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 6329719249 * (2 : ZMod 557015293979) ^ 6329719249) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 496549607546 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 557015293979) ^ 25318876999 = 141093098491 := by
        calc
          (2 : ZMod 557015293979) ^ 25318876999 = (2 : ZMod 557015293979) ^ (12659438499 + 12659438499 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 12659438499 * (2 : ZMod 557015293979) ^ 12659438499) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 141093098491 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 557015293979) ^ 50637753998 = 282161529613 := by
        calc
          (2 : ZMod 557015293979) ^ 50637753998 = (2 : ZMod 557015293979) ^ (25318876999 + 25318876999) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 25318876999 * (2 : ZMod 557015293979) ^ 25318876999 := by rw [pow_add]
          _ = 282161529613 := by rw [factor_1_34]; decide
      change (2 : ZMod 557015293979) ^ 50637753998 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (2 : ZMod 557015293979) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 557015293979) ^ 2 = 4 := by
        calc
          (2 : ZMod 557015293979) ^ 2 = (2 : ZMod 557015293979) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1 * (2 : ZMod 557015293979) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 557015293979) ^ 4 = 16 := by
        calc
          (2 : ZMod 557015293979) ^ 4 = (2 : ZMod 557015293979) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 2 * (2 : ZMod 557015293979) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 557015293979) ^ 9 = 512 := by
        calc
          (2 : ZMod 557015293979) ^ 9 = (2 : ZMod 557015293979) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 4 * (2 : ZMod 557015293979) ^ 4) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 557015293979) ^ 19 = 524288 := by
        calc
          (2 : ZMod 557015293979) ^ 19 = (2 : ZMod 557015293979) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 9 * (2 : ZMod 557015293979) ^ 9) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 557015293979) ^ 39 = 549755813888 := by
        calc
          (2 : ZMod 557015293979) ^ 39 = (2 : ZMod 557015293979) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 19 * (2 : ZMod 557015293979) ^ 19) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 549755813888 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 557015293979) ^ 79 = 195738889457 := by
        calc
          (2 : ZMod 557015293979) ^ 79 = (2 : ZMod 557015293979) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 39 * (2 : ZMod 557015293979) ^ 39) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 195738889457 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 557015293979) ^ 159 = 173367177647 := by
        calc
          (2 : ZMod 557015293979) ^ 159 = (2 : ZMod 557015293979) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 79 * (2 : ZMod 557015293979) ^ 79) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 173367177647 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 557015293979) ^ 319 = 17466694400 := by
        calc
          (2 : ZMod 557015293979) ^ 319 = (2 : ZMod 557015293979) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 159 * (2 : ZMod 557015293979) ^ 159) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 17466694400 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 557015293979) ^ 638 = 428293908747 := by
        calc
          (2 : ZMod 557015293979) ^ 638 = (2 : ZMod 557015293979) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 319 * (2 : ZMod 557015293979) ^ 319 := by rw [pow_add]
          _ = 428293908747 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 557015293979) ^ 1276 = 388760917681 := by
        calc
          (2 : ZMod 557015293979) ^ 1276 = (2 : ZMod 557015293979) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 638 * (2 : ZMod 557015293979) ^ 638 := by rw [pow_add]
          _ = 388760917681 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 557015293979) ^ 2553 = 423198807302 := by
        calc
          (2 : ZMod 557015293979) ^ 2553 = (2 : ZMod 557015293979) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 1276 * (2 : ZMod 557015293979) ^ 1276) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 423198807302 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 557015293979) ^ 5107 = 310200092959 := by
        calc
          (2 : ZMod 557015293979) ^ 5107 = (2 : ZMod 557015293979) ^ (2553 + 2553 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 2553 * (2 : ZMod 557015293979) ^ 2553) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 310200092959 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 557015293979) ^ 10215 = 531663269811 := by
        calc
          (2 : ZMod 557015293979) ^ 10215 = (2 : ZMod 557015293979) ^ (5107 + 5107 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 5107 * (2 : ZMod 557015293979) ^ 5107) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 531663269811 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 557015293979) ^ 20431 = 497722725101 := by
        calc
          (2 : ZMod 557015293979) ^ 20431 = (2 : ZMod 557015293979) ^ (10215 + 10215 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 10215 * (2 : ZMod 557015293979) ^ 10215) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 497722725101 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 557015293979) ^ 40862 = 323066757325 := by
        calc
          (2 : ZMod 557015293979) ^ 40862 = (2 : ZMod 557015293979) ^ (20431 + 20431) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 20431 * (2 : ZMod 557015293979) ^ 20431 := by rw [pow_add]
          _ = 323066757325 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 557015293979) ^ 81724 = 268097181435 := by
        calc
          (2 : ZMod 557015293979) ^ 81724 = (2 : ZMod 557015293979) ^ (40862 + 40862) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 40862 * (2 : ZMod 557015293979) ^ 40862 := by rw [pow_add]
          _ = 268097181435 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 557015293979) ^ 163449 = 94316531215 := by
        calc
          (2 : ZMod 557015293979) ^ 163449 = (2 : ZMod 557015293979) ^ (81724 + 81724 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 81724 * (2 : ZMod 557015293979) ^ 81724) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 94316531215 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 557015293979) ^ 326899 = 394377852269 := by
        calc
          (2 : ZMod 557015293979) ^ 326899 = (2 : ZMod 557015293979) ^ (163449 + 163449 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 163449 * (2 : ZMod 557015293979) ^ 163449) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 394377852269 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 557015293979) ^ 653798 = 555862821250 := by
        calc
          (2 : ZMod 557015293979) ^ 653798 = (2 : ZMod 557015293979) ^ (326899 + 326899) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 326899 * (2 : ZMod 557015293979) ^ 326899 := by rw [pow_add]
          _ = 555862821250 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 557015293979) ^ 1307596 = 448871073563 := by
        calc
          (2 : ZMod 557015293979) ^ 1307596 = (2 : ZMod 557015293979) ^ (653798 + 653798) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 653798 * (2 : ZMod 557015293979) ^ 653798 := by rw [pow_add]
          _ = 448871073563 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 557015293979) ^ 2615193 = 51097431253 := by
        calc
          (2 : ZMod 557015293979) ^ 2615193 = (2 : ZMod 557015293979) ^ (1307596 + 1307596 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 1307596 * (2 : ZMod 557015293979) ^ 1307596) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 51097431253 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 557015293979) ^ 5230387 = 363745402964 := by
        calc
          (2 : ZMod 557015293979) ^ 5230387 = (2 : ZMod 557015293979) ^ (2615193 + 2615193 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 2615193 * (2 : ZMod 557015293979) ^ 2615193) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 363745402964 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 557015293979) ^ 10460774 = 440010408509 := by
        calc
          (2 : ZMod 557015293979) ^ 10460774 = (2 : ZMod 557015293979) ^ (5230387 + 5230387) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 5230387 * (2 : ZMod 557015293979) ^ 5230387 := by rw [pow_add]
          _ = 440010408509 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 557015293979) ^ 20921548 = 556758882793 := by
        calc
          (2 : ZMod 557015293979) ^ 20921548 = (2 : ZMod 557015293979) ^ (10460774 + 10460774) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 10460774 * (2 : ZMod 557015293979) ^ 10460774 := by rw [pow_add]
          _ = 556758882793 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 557015293979) ^ 41843096 = 510111703289 := by
        calc
          (2 : ZMod 557015293979) ^ 41843096 = (2 : ZMod 557015293979) ^ (20921548 + 20921548) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 20921548 * (2 : ZMod 557015293979) ^ 20921548 := by rw [pow_add]
          _ = 510111703289 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 557015293979) ^ 83686192 = 289452006438 := by
        calc
          (2 : ZMod 557015293979) ^ 83686192 = (2 : ZMod 557015293979) ^ (41843096 + 41843096) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 41843096 * (2 : ZMod 557015293979) ^ 41843096 := by rw [pow_add]
          _ = 289452006438 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 557015293979) ^ 167372384 = 272956968637 := by
        calc
          (2 : ZMod 557015293979) ^ 167372384 = (2 : ZMod 557015293979) ^ (83686192 + 83686192) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 83686192 * (2 : ZMod 557015293979) ^ 83686192 := by rw [pow_add]
          _ = 272956968637 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 557015293979) ^ 334744768 = 434618412829 := by
        calc
          (2 : ZMod 557015293979) ^ 334744768 = (2 : ZMod 557015293979) ^ (167372384 + 167372384) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 167372384 * (2 : ZMod 557015293979) ^ 167372384 := by rw [pow_add]
          _ = 434618412829 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 557015293979) ^ 669489536 = 311994262479 := by
        calc
          (2 : ZMod 557015293979) ^ 669489536 = (2 : ZMod 557015293979) ^ (334744768 + 334744768) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 334744768 * (2 : ZMod 557015293979) ^ 334744768 := by rw [pow_add]
          _ = 311994262479 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 557015293979) ^ 1338979072 = 266830819634 := by
        calc
          (2 : ZMod 557015293979) ^ 1338979072 = (2 : ZMod 557015293979) ^ (669489536 + 669489536) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 669489536 * (2 : ZMod 557015293979) ^ 669489536 := by rw [pow_add]
          _ = 266830819634 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 557015293979) ^ 2677958144 = 305752553793 := by
        calc
          (2 : ZMod 557015293979) ^ 2677958144 = (2 : ZMod 557015293979) ^ (1338979072 + 1338979072) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1338979072 * (2 : ZMod 557015293979) ^ 1338979072 := by rw [pow_add]
          _ = 305752553793 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 557015293979) ^ 5355916288 = 543459419095 := by
        calc
          (2 : ZMod 557015293979) ^ 5355916288 = (2 : ZMod 557015293979) ^ (2677958144 + 2677958144) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 2677958144 * (2 : ZMod 557015293979) ^ 2677958144 := by rw [pow_add]
          _ = 543459419095 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 557015293979) ^ 10711832576 = 436149333861 := by
        calc
          (2 : ZMod 557015293979) ^ 10711832576 = (2 : ZMod 557015293979) ^ (5355916288 + 5355916288) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 5355916288 * (2 : ZMod 557015293979) ^ 5355916288 := by rw [pow_add]
          _ = 436149333861 := by rw [factor_2_32]; decide
      have factor_2_34 : (2 : ZMod 557015293979) ^ 21423665153 = 137134284439 := by
        calc
          (2 : ZMod 557015293979) ^ 21423665153 = (2 : ZMod 557015293979) ^ (10711832576 + 10711832576 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 10711832576 * (2 : ZMod 557015293979) ^ 10711832576) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 137134284439 := by rw [factor_2_33]; decide
      have factor_2_35 : (2 : ZMod 557015293979) ^ 42847330306 = 385256863397 := by
        calc
          (2 : ZMod 557015293979) ^ 42847330306 = (2 : ZMod 557015293979) ^ (21423665153 + 21423665153) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 21423665153 * (2 : ZMod 557015293979) ^ 21423665153 := by rw [pow_add]
          _ = 385256863397 := by rw [factor_2_34]; decide
      change (2 : ZMod 557015293979) ^ 42847330306 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (2 : ZMod 557015293979) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 557015293979) ^ 3 = 8 := by
        calc
          (2 : ZMod 557015293979) ^ 3 = (2 : ZMod 557015293979) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 1 * (2 : ZMod 557015293979) ^ 1) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 557015293979) ^ 6 = 64 := by
        calc
          (2 : ZMod 557015293979) ^ 6 = (2 : ZMod 557015293979) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 3 * (2 : ZMod 557015293979) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 557015293979) ^ 12 = 4096 := by
        calc
          (2 : ZMod 557015293979) ^ 12 = (2 : ZMod 557015293979) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 6 * (2 : ZMod 557015293979) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 557015293979) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 557015293979) ^ 24 = (2 : ZMod 557015293979) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 12 * (2 : ZMod 557015293979) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 557015293979) ^ 48 = 182253251261 := by
        calc
          (2 : ZMod 557015293979) ^ 48 = (2 : ZMod 557015293979) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 24 * (2 : ZMod 557015293979) ^ 24 := by rw [pow_add]
          _ = 182253251261 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 557015293979) ^ 96 = 320293529143 := by
        calc
          (2 : ZMod 557015293979) ^ 96 = (2 : ZMod 557015293979) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 48 * (2 : ZMod 557015293979) ^ 48 := by rw [pow_add]
          _ = 320293529143 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 557015293979) ^ 193 = 318787317623 := by
        calc
          (2 : ZMod 557015293979) ^ 193 = (2 : ZMod 557015293979) ^ (96 + 96 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 96 * (2 : ZMod 557015293979) ^ 96) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 318787317623 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 557015293979) ^ 386 = 463269956754 := by
        calc
          (2 : ZMod 557015293979) ^ 386 = (2 : ZMod 557015293979) ^ (193 + 193) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 193 * (2 : ZMod 557015293979) ^ 193 := by rw [pow_add]
          _ = 463269956754 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 557015293979) ^ 772 = 482236429784 := by
        calc
          (2 : ZMod 557015293979) ^ 772 = (2 : ZMod 557015293979) ^ (386 + 386) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 386 * (2 : ZMod 557015293979) ^ 386 := by rw [pow_add]
          _ = 482236429784 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 557015293979) ^ 1544 = 481334847184 := by
        calc
          (2 : ZMod 557015293979) ^ 1544 = (2 : ZMod 557015293979) ^ (772 + 772) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 772 * (2 : ZMod 557015293979) ^ 772 := by rw [pow_add]
          _ = 481334847184 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 557015293979) ^ 3088 = 307302140089 := by
        calc
          (2 : ZMod 557015293979) ^ 3088 = (2 : ZMod 557015293979) ^ (1544 + 1544) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1544 * (2 : ZMod 557015293979) ^ 1544 := by rw [pow_add]
          _ = 307302140089 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 557015293979) ^ 6176 = 540802120290 := by
        calc
          (2 : ZMod 557015293979) ^ 6176 = (2 : ZMod 557015293979) ^ (3088 + 3088) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 3088 * (2 : ZMod 557015293979) ^ 3088 := by rw [pow_add]
          _ = 540802120290 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 557015293979) ^ 12353 = 270366901335 := by
        calc
          (2 : ZMod 557015293979) ^ 12353 = (2 : ZMod 557015293979) ^ (6176 + 6176 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 6176 * (2 : ZMod 557015293979) ^ 6176) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 270366901335 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 557015293979) ^ 24707 = 157308637465 := by
        calc
          (2 : ZMod 557015293979) ^ 24707 = (2 : ZMod 557015293979) ^ (12353 + 12353 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 12353 * (2 : ZMod 557015293979) ^ 12353) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 157308637465 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 557015293979) ^ 49414 = 311535539355 := by
        calc
          (2 : ZMod 557015293979) ^ 49414 = (2 : ZMod 557015293979) ^ (24707 + 24707) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 24707 * (2 : ZMod 557015293979) ^ 24707 := by rw [pow_add]
          _ = 311535539355 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 557015293979) ^ 98829 = 99463022492 := by
        calc
          (2 : ZMod 557015293979) ^ 98829 = (2 : ZMod 557015293979) ^ (49414 + 49414 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 49414 * (2 : ZMod 557015293979) ^ 49414) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 99463022492 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 557015293979) ^ 197659 = 6790440846 := by
        calc
          (2 : ZMod 557015293979) ^ 197659 = (2 : ZMod 557015293979) ^ (98829 + 98829 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 98829 * (2 : ZMod 557015293979) ^ 98829) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 6790440846 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 557015293979) ^ 395319 = 360081448627 := by
        calc
          (2 : ZMod 557015293979) ^ 395319 = (2 : ZMod 557015293979) ^ (197659 + 197659 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 197659 * (2 : ZMod 557015293979) ^ 197659) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 360081448627 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 557015293979) ^ 790639 = 353501293182 := by
        calc
          (2 : ZMod 557015293979) ^ 790639 = (2 : ZMod 557015293979) ^ (395319 + 395319 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 395319 * (2 : ZMod 557015293979) ^ 395319) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 353501293182 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 557015293979) ^ 1581279 = 130560270215 := by
        calc
          (2 : ZMod 557015293979) ^ 1581279 = (2 : ZMod 557015293979) ^ (790639 + 790639 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 790639 * (2 : ZMod 557015293979) ^ 790639) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 130560270215 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 557015293979) ^ 3162559 = 104020447599 := by
        calc
          (2 : ZMod 557015293979) ^ 3162559 = (2 : ZMod 557015293979) ^ (1581279 + 1581279 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 1581279 * (2 : ZMod 557015293979) ^ 1581279) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 104020447599 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 557015293979) ^ 6325119 = 524545530077 := by
        calc
          (2 : ZMod 557015293979) ^ 6325119 = (2 : ZMod 557015293979) ^ (3162559 + 3162559 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 3162559 * (2 : ZMod 557015293979) ^ 3162559) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 524545530077 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 557015293979) ^ 12650238 = 283727562194 := by
        calc
          (2 : ZMod 557015293979) ^ 12650238 = (2 : ZMod 557015293979) ^ (6325119 + 6325119) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 6325119 * (2 : ZMod 557015293979) ^ 6325119 := by rw [pow_add]
          _ = 283727562194 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 557015293979) ^ 25300476 = 530929827210 := by
        calc
          (2 : ZMod 557015293979) ^ 25300476 = (2 : ZMod 557015293979) ^ (12650238 + 12650238) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 12650238 * (2 : ZMod 557015293979) ^ 12650238 := by rw [pow_add]
          _ = 530929827210 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 557015293979) ^ 50600953 = 210726406402 := by
        calc
          (2 : ZMod 557015293979) ^ 50600953 = (2 : ZMod 557015293979) ^ (25300476 + 25300476 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 25300476 * (2 : ZMod 557015293979) ^ 25300476) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 210726406402 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 557015293979) ^ 101201906 = 194652444724 := by
        calc
          (2 : ZMod 557015293979) ^ 101201906 = (2 : ZMod 557015293979) ^ (50600953 + 50600953) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 50600953 * (2 : ZMod 557015293979) ^ 50600953 := by rw [pow_add]
          _ = 194652444724 := by rw [factor_3_25]; decide
      have factor_3_27 : (2 : ZMod 557015293979) ^ 202403813 = 114690688087 := by
        calc
          (2 : ZMod 557015293979) ^ 202403813 = (2 : ZMod 557015293979) ^ (101201906 + 101201906 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 101201906 * (2 : ZMod 557015293979) ^ 101201906) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 114690688087 := by rw [factor_3_26]; decide
      have factor_3_28 : (2 : ZMod 557015293979) ^ 404807626 = 361491649390 := by
        calc
          (2 : ZMod 557015293979) ^ 404807626 = (2 : ZMod 557015293979) ^ (202403813 + 202403813) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 202403813 * (2 : ZMod 557015293979) ^ 202403813 := by rw [pow_add]
          _ = 361491649390 := by rw [factor_3_27]; decide
      have factor_3_29 : (2 : ZMod 557015293979) ^ 809615252 = 141733062337 := by
        calc
          (2 : ZMod 557015293979) ^ 809615252 = (2 : ZMod 557015293979) ^ (404807626 + 404807626) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 404807626 * (2 : ZMod 557015293979) ^ 404807626 := by rw [pow_add]
          _ = 141733062337 := by rw [factor_3_28]; decide
      have factor_3_30 : (2 : ZMod 557015293979) ^ 1619230505 = 151970838609 := by
        calc
          (2 : ZMod 557015293979) ^ 1619230505 = (2 : ZMod 557015293979) ^ (809615252 + 809615252 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 809615252 * (2 : ZMod 557015293979) ^ 809615252) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 151970838609 := by rw [factor_3_29]; decide
      have factor_3_31 : (2 : ZMod 557015293979) ^ 3238461011 = 555511696266 := by
        calc
          (2 : ZMod 557015293979) ^ 3238461011 = (2 : ZMod 557015293979) ^ (1619230505 + 1619230505 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 1619230505 * (2 : ZMod 557015293979) ^ 1619230505) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 555511696266 := by rw [factor_3_30]; decide
      have factor_3_32 : (2 : ZMod 557015293979) ^ 6476922023 = 411101961750 := by
        calc
          (2 : ZMod 557015293979) ^ 6476922023 = (2 : ZMod 557015293979) ^ (3238461011 + 3238461011 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 3238461011 * (2 : ZMod 557015293979) ^ 3238461011) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 411101961750 := by rw [factor_3_31]; decide
      have factor_3_33 : (2 : ZMod 557015293979) ^ 12953844046 = 84268270602 := by
        calc
          (2 : ZMod 557015293979) ^ 12953844046 = (2 : ZMod 557015293979) ^ (6476922023 + 6476922023) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 6476922023 * (2 : ZMod 557015293979) ^ 6476922023 := by rw [pow_add]
          _ = 84268270602 := by rw [factor_3_32]; decide
      change (2 : ZMod 557015293979) ^ 12953844046 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (2 : ZMod 557015293979) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 557015293979) ^ 3 = 8 := by
        calc
          (2 : ZMod 557015293979) ^ 3 = (2 : ZMod 557015293979) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 1 * (2 : ZMod 557015293979) ^ 1) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 557015293979) ^ 6 = 64 := by
        calc
          (2 : ZMod 557015293979) ^ 6 = (2 : ZMod 557015293979) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 3 * (2 : ZMod 557015293979) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 557015293979) ^ 12 = 4096 := by
        calc
          (2 : ZMod 557015293979) ^ 12 = (2 : ZMod 557015293979) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 6 * (2 : ZMod 557015293979) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 557015293979) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 557015293979) ^ 24 = (2 : ZMod 557015293979) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 12 * (2 : ZMod 557015293979) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 557015293979) ^ 48 = 182253251261 := by
        calc
          (2 : ZMod 557015293979) ^ 48 = (2 : ZMod 557015293979) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 24 * (2 : ZMod 557015293979) ^ 24 := by rw [pow_add]
          _ = 182253251261 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 557015293979) ^ 96 = 320293529143 := by
        calc
          (2 : ZMod 557015293979) ^ 96 = (2 : ZMod 557015293979) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 48 * (2 : ZMod 557015293979) ^ 48 := by rw [pow_add]
          _ = 320293529143 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 557015293979) ^ 192 = 437901305801 := by
        calc
          (2 : ZMod 557015293979) ^ 192 = (2 : ZMod 557015293979) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 96 * (2 : ZMod 557015293979) ^ 96 := by rw [pow_add]
          _ = 437901305801 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 557015293979) ^ 384 = 394325136178 := by
        calc
          (2 : ZMod 557015293979) ^ 384 = (2 : ZMod 557015293979) ^ (192 + 192) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 192 * (2 : ZMod 557015293979) ^ 192 := by rw [pow_add]
          _ = 394325136178 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 557015293979) ^ 768 = 308647423851 := by
        calc
          (2 : ZMod 557015293979) ^ 768 = (2 : ZMod 557015293979) ^ (384 + 384) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 384 * (2 : ZMod 557015293979) ^ 384 := by rw [pow_add]
          _ = 308647423851 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 557015293979) ^ 1537 = 73387340241 := by
        calc
          (2 : ZMod 557015293979) ^ 1537 = (2 : ZMod 557015293979) ^ (768 + 768 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 768 * (2 : ZMod 557015293979) ^ 768) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 73387340241 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 557015293979) ^ 3074 = 420126055288 := by
        calc
          (2 : ZMod 557015293979) ^ 3074 = (2 : ZMod 557015293979) ^ (1537 + 1537) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 1537 * (2 : ZMod 557015293979) ^ 1537 := by rw [pow_add]
          _ = 420126055288 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 557015293979) ^ 6149 = 310659448376 := by
        calc
          (2 : ZMod 557015293979) ^ 6149 = (2 : ZMod 557015293979) ^ (3074 + 3074 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = ((2 : ZMod 557015293979) ^ 3074 * (2 : ZMod 557015293979) ^ 3074) * (2 : ZMod 557015293979) := by rw [pow_succ, pow_add]
          _ = 310659448376 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 557015293979) ^ 12298 = 277113898388 := by
        calc
          (2 : ZMod 557015293979) ^ 12298 = (2 : ZMod 557015293979) ^ (6149 + 6149) :=
            congrArg (fun n : ℕ => (2 : ZMod 557015293979) ^ n) (by norm_num)
          _ = (2 : ZMod 557015293979) ^ 6149 * (2 : ZMod 557015293979) ^ 6149 := by rw [pow_add]
          _ = 277113898388 := by rw [factor_4_12]; decide
      change (2 : ZMod 557015293979) ^ 12298 ≠ 1
      rw [factor_4_13]
      decide

#print axioms prime_lucas_557015293979

end TotientTailPeriodKiller
end Erdos249257
