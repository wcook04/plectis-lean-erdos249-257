import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_5238105468361 : Nat.Prime 5238105468361 := by
  apply lucas_primality 5238105468361 (7 : ZMod 5238105468361)
  ·
      have fermat_0 : (7 : ZMod 5238105468361) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 5238105468361) ^ 2 = 49 := by
        calc
          (7 : ZMod 5238105468361) ^ 2 = (7 : ZMod 5238105468361) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1 * (7 : ZMod 5238105468361) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 5238105468361) ^ 4 = 2401 := by
        calc
          (7 : ZMod 5238105468361) ^ 4 = (7 : ZMod 5238105468361) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 2 * (7 : ZMod 5238105468361) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 5238105468361) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 5238105468361) ^ 9 = (7 : ZMod 5238105468361) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 4 * (7 : ZMod 5238105468361) ^ 4) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 5238105468361) ^ 19 = 777686219607 := by
        calc
          (7 : ZMod 5238105468361) ^ 19 = (7 : ZMod 5238105468361) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 9 * (7 : ZMod 5238105468361) ^ 9) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 777686219607 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 5238105468361) ^ 38 = 2894115082264 := by
        calc
          (7 : ZMod 5238105468361) ^ 38 = (7 : ZMod 5238105468361) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 19 * (7 : ZMod 5238105468361) ^ 19 := by rw [pow_add]
          _ = 2894115082264 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 5238105468361) ^ 76 = 3840369428002 := by
        calc
          (7 : ZMod 5238105468361) ^ 76 = (7 : ZMod 5238105468361) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 38 * (7 : ZMod 5238105468361) ^ 38 := by rw [pow_add]
          _ = 3840369428002 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 5238105468361) ^ 152 = 2727293998761 := by
        calc
          (7 : ZMod 5238105468361) ^ 152 = (7 : ZMod 5238105468361) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 76 * (7 : ZMod 5238105468361) ^ 76 := by rw [pow_add]
          _ = 2727293998761 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 5238105468361) ^ 304 = 1110540951196 := by
        calc
          (7 : ZMod 5238105468361) ^ 304 = (7 : ZMod 5238105468361) ^ (152 + 152) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 152 * (7 : ZMod 5238105468361) ^ 152 := by rw [pow_add]
          _ = 1110540951196 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 5238105468361) ^ 609 = 702352139517 := by
        calc
          (7 : ZMod 5238105468361) ^ 609 = (7 : ZMod 5238105468361) ^ (304 + 304 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 304 * (7 : ZMod 5238105468361) ^ 304) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 702352139517 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 5238105468361) ^ 1219 = 1599199445027 := by
        calc
          (7 : ZMod 5238105468361) ^ 1219 = (7 : ZMod 5238105468361) ^ (609 + 609 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 609 * (7 : ZMod 5238105468361) ^ 609) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1599199445027 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 5238105468361) ^ 2439 = 3549172301715 := by
        calc
          (7 : ZMod 5238105468361) ^ 2439 = (7 : ZMod 5238105468361) ^ (1219 + 1219 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1219 * (7 : ZMod 5238105468361) ^ 1219) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3549172301715 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 5238105468361) ^ 4878 = 786462498404 := by
        calc
          (7 : ZMod 5238105468361) ^ 4878 = (7 : ZMod 5238105468361) ^ (2439 + 2439) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 2439 * (7 : ZMod 5238105468361) ^ 2439 := by rw [pow_add]
          _ = 786462498404 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 5238105468361) ^ 9756 = 433680653096 := by
        calc
          (7 : ZMod 5238105468361) ^ 9756 = (7 : ZMod 5238105468361) ^ (4878 + 4878) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 4878 * (7 : ZMod 5238105468361) ^ 4878 := by rw [pow_add]
          _ = 433680653096 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 5238105468361) ^ 19513 = 825662177534 := by
        calc
          (7 : ZMod 5238105468361) ^ 19513 = (7 : ZMod 5238105468361) ^ (9756 + 9756 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 9756 * (7 : ZMod 5238105468361) ^ 9756) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 825662177534 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 5238105468361) ^ 39026 = 1455072775345 := by
        calc
          (7 : ZMod 5238105468361) ^ 39026 = (7 : ZMod 5238105468361) ^ (19513 + 19513) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 19513 * (7 : ZMod 5238105468361) ^ 19513 := by rw [pow_add]
          _ = 1455072775345 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 5238105468361) ^ 78053 = 3855720793368 := by
        calc
          (7 : ZMod 5238105468361) ^ 78053 = (7 : ZMod 5238105468361) ^ (39026 + 39026 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 39026 * (7 : ZMod 5238105468361) ^ 39026) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3855720793368 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 5238105468361) ^ 156107 = 2716922989059 := by
        calc
          (7 : ZMod 5238105468361) ^ 156107 = (7 : ZMod 5238105468361) ^ (78053 + 78053 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 78053 * (7 : ZMod 5238105468361) ^ 78053) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2716922989059 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 5238105468361) ^ 312215 = 1086030606712 := by
        calc
          (7 : ZMod 5238105468361) ^ 312215 = (7 : ZMod 5238105468361) ^ (156107 + 156107 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 156107 * (7 : ZMod 5238105468361) ^ 156107) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1086030606712 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 5238105468361) ^ 624430 = 623574911339 := by
        calc
          (7 : ZMod 5238105468361) ^ 624430 = (7 : ZMod 5238105468361) ^ (312215 + 312215) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 312215 * (7 : ZMod 5238105468361) ^ 312215 := by rw [pow_add]
          _ = 623574911339 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 5238105468361) ^ 1248861 = 2266508155473 := by
        calc
          (7 : ZMod 5238105468361) ^ 1248861 = (7 : ZMod 5238105468361) ^ (624430 + 624430 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 624430 * (7 : ZMod 5238105468361) ^ 624430) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2266508155473 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 5238105468361) ^ 2497723 = 4049699608965 := by
        calc
          (7 : ZMod 5238105468361) ^ 2497723 = (7 : ZMod 5238105468361) ^ (1248861 + 1248861 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1248861 * (7 : ZMod 5238105468361) ^ 1248861) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4049699608965 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 5238105468361) ^ 4995446 = 2478807872253 := by
        calc
          (7 : ZMod 5238105468361) ^ 4995446 = (7 : ZMod 5238105468361) ^ (2497723 + 2497723) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 2497723 * (7 : ZMod 5238105468361) ^ 2497723 := by rw [pow_add]
          _ = 2478807872253 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 5238105468361) ^ 9990893 = 1715172883100 := by
        calc
          (7 : ZMod 5238105468361) ^ 9990893 = (7 : ZMod 5238105468361) ^ (4995446 + 4995446 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 4995446 * (7 : ZMod 5238105468361) ^ 4995446) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1715172883100 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 5238105468361) ^ 19981786 = 2463247220138 := by
        calc
          (7 : ZMod 5238105468361) ^ 19981786 = (7 : ZMod 5238105468361) ^ (9990893 + 9990893) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 9990893 * (7 : ZMod 5238105468361) ^ 9990893 := by rw [pow_add]
          _ = 2463247220138 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 5238105468361) ^ 39963573 = 1533526684246 := by
        calc
          (7 : ZMod 5238105468361) ^ 39963573 = (7 : ZMod 5238105468361) ^ (19981786 + 19981786 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 19981786 * (7 : ZMod 5238105468361) ^ 19981786) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1533526684246 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 5238105468361) ^ 79927146 = 5141740966884 := by
        calc
          (7 : ZMod 5238105468361) ^ 79927146 = (7 : ZMod 5238105468361) ^ (39963573 + 39963573) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 39963573 * (7 : ZMod 5238105468361) ^ 39963573 := by rw [pow_add]
          _ = 5141740966884 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 5238105468361) ^ 159854292 = 4402522629970 := by
        calc
          (7 : ZMod 5238105468361) ^ 159854292 = (7 : ZMod 5238105468361) ^ (79927146 + 79927146) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 79927146 * (7 : ZMod 5238105468361) ^ 79927146 := by rw [pow_add]
          _ = 4402522629970 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 5238105468361) ^ 319708585 = 3823420171153 := by
        calc
          (7 : ZMod 5238105468361) ^ 319708585 = (7 : ZMod 5238105468361) ^ (159854292 + 159854292 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 159854292 * (7 : ZMod 5238105468361) ^ 159854292) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3823420171153 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 5238105468361) ^ 639417171 = 5202970375195 := by
        calc
          (7 : ZMod 5238105468361) ^ 639417171 = (7 : ZMod 5238105468361) ^ (319708585 + 319708585 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 319708585 * (7 : ZMod 5238105468361) ^ 319708585) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5202970375195 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 5238105468361) ^ 1278834342 = 796348185000 := by
        calc
          (7 : ZMod 5238105468361) ^ 1278834342 = (7 : ZMod 5238105468361) ^ (639417171 + 639417171) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 639417171 * (7 : ZMod 5238105468361) ^ 639417171 := by rw [pow_add]
          _ = 796348185000 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 5238105468361) ^ 2557668685 = 3958102178842 := by
        calc
          (7 : ZMod 5238105468361) ^ 2557668685 = (7 : ZMod 5238105468361) ^ (1278834342 + 1278834342 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1278834342 * (7 : ZMod 5238105468361) ^ 1278834342) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3958102178842 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 5238105468361) ^ 5115337371 = 2749698282206 := by
        calc
          (7 : ZMod 5238105468361) ^ 5115337371 = (7 : ZMod 5238105468361) ^ (2557668685 + 2557668685 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 2557668685 * (7 : ZMod 5238105468361) ^ 2557668685) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2749698282206 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 5238105468361) ^ 10230674742 = 3414960039114 := by
        calc
          (7 : ZMod 5238105468361) ^ 10230674742 = (7 : ZMod 5238105468361) ^ (5115337371 + 5115337371) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 5115337371 * (7 : ZMod 5238105468361) ^ 5115337371 := by rw [pow_add]
          _ = 3414960039114 := by rw [fermat_32]; decide
      have fermat_34 : (7 : ZMod 5238105468361) ^ 20461349485 = 827002441357 := by
        calc
          (7 : ZMod 5238105468361) ^ 20461349485 = (7 : ZMod 5238105468361) ^ (10230674742 + 10230674742 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 10230674742 * (7 : ZMod 5238105468361) ^ 10230674742) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 827002441357 := by rw [fermat_33]; decide
      have fermat_35 : (7 : ZMod 5238105468361) ^ 40922698971 = 3674089022771 := by
        calc
          (7 : ZMod 5238105468361) ^ 40922698971 = (7 : ZMod 5238105468361) ^ (20461349485 + 20461349485 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 20461349485 * (7 : ZMod 5238105468361) ^ 20461349485) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3674089022771 := by rw [fermat_34]; decide
      have fermat_36 : (7 : ZMod 5238105468361) ^ 81845397943 = 1000814766964 := by
        calc
          (7 : ZMod 5238105468361) ^ 81845397943 = (7 : ZMod 5238105468361) ^ (40922698971 + 40922698971 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 40922698971 * (7 : ZMod 5238105468361) ^ 40922698971) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1000814766964 := by rw [fermat_35]; decide
      have fermat_37 : (7 : ZMod 5238105468361) ^ 163690795886 = 3859497684715 := by
        calc
          (7 : ZMod 5238105468361) ^ 163690795886 = (7 : ZMod 5238105468361) ^ (81845397943 + 81845397943) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 81845397943 * (7 : ZMod 5238105468361) ^ 81845397943 := by rw [pow_add]
          _ = 3859497684715 := by rw [fermat_36]; decide
      have fermat_38 : (7 : ZMod 5238105468361) ^ 327381591772 = 2846999696002 := by
        calc
          (7 : ZMod 5238105468361) ^ 327381591772 = (7 : ZMod 5238105468361) ^ (163690795886 + 163690795886) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 163690795886 * (7 : ZMod 5238105468361) ^ 163690795886 := by rw [pow_add]
          _ = 2846999696002 := by rw [fermat_37]; decide
      have fermat_39 : (7 : ZMod 5238105468361) ^ 654763183545 = 2384151819450 := by
        calc
          (7 : ZMod 5238105468361) ^ 654763183545 = (7 : ZMod 5238105468361) ^ (327381591772 + 327381591772 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 327381591772 * (7 : ZMod 5238105468361) ^ 327381591772) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2384151819450 := by rw [fermat_38]; decide
      have fermat_40 : (7 : ZMod 5238105468361) ^ 1309526367090 = 24688945145 := by
        calc
          (7 : ZMod 5238105468361) ^ 1309526367090 = (7 : ZMod 5238105468361) ^ (654763183545 + 654763183545) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 654763183545 * (7 : ZMod 5238105468361) ^ 654763183545 := by rw [pow_add]
          _ = 24688945145 := by rw [fermat_39]; decide
      have fermat_41 : (7 : ZMod 5238105468361) ^ 2619052734180 = 5238105468360 := by
        calc
          (7 : ZMod 5238105468361) ^ 2619052734180 = (7 : ZMod 5238105468361) ^ (1309526367090 + 1309526367090) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1309526367090 * (7 : ZMod 5238105468361) ^ 1309526367090 := by rw [pow_add]
          _ = 5238105468360 := by rw [fermat_40]; decide
      have fermat_42 : (7 : ZMod 5238105468361) ^ 5238105468360 = 1 := by
        calc
          (7 : ZMod 5238105468361) ^ 5238105468360 = (7 : ZMod 5238105468361) ^ (2619052734180 + 2619052734180) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 2619052734180 * (7 : ZMod 5238105468361) ^ 2619052734180 := by rw [pow_add]
          _ = 1 := by rw [fermat_41]; decide
      simpa using fermat_42
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (17, 1), (41, 1), (191, 1), (327889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (17, 1), (41, 1), (191, 1), (327889, 1)] : List FactorBlock).map factorBlockValue).prod = 5238105468361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 5238105468361) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 5238105468361) ^ 2 = 49 := by
        calc
          (7 : ZMod 5238105468361) ^ 2 = (7 : ZMod 5238105468361) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1 * (7 : ZMod 5238105468361) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 5238105468361) ^ 4 = 2401 := by
        calc
          (7 : ZMod 5238105468361) ^ 4 = (7 : ZMod 5238105468361) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 2 * (7 : ZMod 5238105468361) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 5238105468361) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 5238105468361) ^ 9 = (7 : ZMod 5238105468361) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 4 * (7 : ZMod 5238105468361) ^ 4) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 5238105468361) ^ 19 = 777686219607 := by
        calc
          (7 : ZMod 5238105468361) ^ 19 = (7 : ZMod 5238105468361) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 9 * (7 : ZMod 5238105468361) ^ 9) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 777686219607 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 5238105468361) ^ 38 = 2894115082264 := by
        calc
          (7 : ZMod 5238105468361) ^ 38 = (7 : ZMod 5238105468361) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 19 * (7 : ZMod 5238105468361) ^ 19 := by rw [pow_add]
          _ = 2894115082264 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 5238105468361) ^ 76 = 3840369428002 := by
        calc
          (7 : ZMod 5238105468361) ^ 76 = (7 : ZMod 5238105468361) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 38 * (7 : ZMod 5238105468361) ^ 38 := by rw [pow_add]
          _ = 3840369428002 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 5238105468361) ^ 152 = 2727293998761 := by
        calc
          (7 : ZMod 5238105468361) ^ 152 = (7 : ZMod 5238105468361) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 76 * (7 : ZMod 5238105468361) ^ 76 := by rw [pow_add]
          _ = 2727293998761 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 5238105468361) ^ 304 = 1110540951196 := by
        calc
          (7 : ZMod 5238105468361) ^ 304 = (7 : ZMod 5238105468361) ^ (152 + 152) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 152 * (7 : ZMod 5238105468361) ^ 152 := by rw [pow_add]
          _ = 1110540951196 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 5238105468361) ^ 609 = 702352139517 := by
        calc
          (7 : ZMod 5238105468361) ^ 609 = (7 : ZMod 5238105468361) ^ (304 + 304 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 304 * (7 : ZMod 5238105468361) ^ 304) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 702352139517 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 5238105468361) ^ 1219 = 1599199445027 := by
        calc
          (7 : ZMod 5238105468361) ^ 1219 = (7 : ZMod 5238105468361) ^ (609 + 609 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 609 * (7 : ZMod 5238105468361) ^ 609) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1599199445027 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 5238105468361) ^ 2439 = 3549172301715 := by
        calc
          (7 : ZMod 5238105468361) ^ 2439 = (7 : ZMod 5238105468361) ^ (1219 + 1219 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1219 * (7 : ZMod 5238105468361) ^ 1219) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3549172301715 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 5238105468361) ^ 4878 = 786462498404 := by
        calc
          (7 : ZMod 5238105468361) ^ 4878 = (7 : ZMod 5238105468361) ^ (2439 + 2439) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 2439 * (7 : ZMod 5238105468361) ^ 2439 := by rw [pow_add]
          _ = 786462498404 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 5238105468361) ^ 9756 = 433680653096 := by
        calc
          (7 : ZMod 5238105468361) ^ 9756 = (7 : ZMod 5238105468361) ^ (4878 + 4878) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 4878 * (7 : ZMod 5238105468361) ^ 4878 := by rw [pow_add]
          _ = 433680653096 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 5238105468361) ^ 19513 = 825662177534 := by
        calc
          (7 : ZMod 5238105468361) ^ 19513 = (7 : ZMod 5238105468361) ^ (9756 + 9756 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 9756 * (7 : ZMod 5238105468361) ^ 9756) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 825662177534 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 5238105468361) ^ 39026 = 1455072775345 := by
        calc
          (7 : ZMod 5238105468361) ^ 39026 = (7 : ZMod 5238105468361) ^ (19513 + 19513) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 19513 * (7 : ZMod 5238105468361) ^ 19513 := by rw [pow_add]
          _ = 1455072775345 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 5238105468361) ^ 78053 = 3855720793368 := by
        calc
          (7 : ZMod 5238105468361) ^ 78053 = (7 : ZMod 5238105468361) ^ (39026 + 39026 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 39026 * (7 : ZMod 5238105468361) ^ 39026) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3855720793368 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 5238105468361) ^ 156107 = 2716922989059 := by
        calc
          (7 : ZMod 5238105468361) ^ 156107 = (7 : ZMod 5238105468361) ^ (78053 + 78053 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 78053 * (7 : ZMod 5238105468361) ^ 78053) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2716922989059 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 5238105468361) ^ 312215 = 1086030606712 := by
        calc
          (7 : ZMod 5238105468361) ^ 312215 = (7 : ZMod 5238105468361) ^ (156107 + 156107 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 156107 * (7 : ZMod 5238105468361) ^ 156107) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1086030606712 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 5238105468361) ^ 624430 = 623574911339 := by
        calc
          (7 : ZMod 5238105468361) ^ 624430 = (7 : ZMod 5238105468361) ^ (312215 + 312215) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 312215 * (7 : ZMod 5238105468361) ^ 312215 := by rw [pow_add]
          _ = 623574911339 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 5238105468361) ^ 1248861 = 2266508155473 := by
        calc
          (7 : ZMod 5238105468361) ^ 1248861 = (7 : ZMod 5238105468361) ^ (624430 + 624430 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 624430 * (7 : ZMod 5238105468361) ^ 624430) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2266508155473 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 5238105468361) ^ 2497723 = 4049699608965 := by
        calc
          (7 : ZMod 5238105468361) ^ 2497723 = (7 : ZMod 5238105468361) ^ (1248861 + 1248861 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1248861 * (7 : ZMod 5238105468361) ^ 1248861) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4049699608965 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 5238105468361) ^ 4995446 = 2478807872253 := by
        calc
          (7 : ZMod 5238105468361) ^ 4995446 = (7 : ZMod 5238105468361) ^ (2497723 + 2497723) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 2497723 * (7 : ZMod 5238105468361) ^ 2497723 := by rw [pow_add]
          _ = 2478807872253 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 5238105468361) ^ 9990893 = 1715172883100 := by
        calc
          (7 : ZMod 5238105468361) ^ 9990893 = (7 : ZMod 5238105468361) ^ (4995446 + 4995446 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 4995446 * (7 : ZMod 5238105468361) ^ 4995446) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1715172883100 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 5238105468361) ^ 19981786 = 2463247220138 := by
        calc
          (7 : ZMod 5238105468361) ^ 19981786 = (7 : ZMod 5238105468361) ^ (9990893 + 9990893) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 9990893 * (7 : ZMod 5238105468361) ^ 9990893 := by rw [pow_add]
          _ = 2463247220138 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 5238105468361) ^ 39963573 = 1533526684246 := by
        calc
          (7 : ZMod 5238105468361) ^ 39963573 = (7 : ZMod 5238105468361) ^ (19981786 + 19981786 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 19981786 * (7 : ZMod 5238105468361) ^ 19981786) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1533526684246 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 5238105468361) ^ 79927146 = 5141740966884 := by
        calc
          (7 : ZMod 5238105468361) ^ 79927146 = (7 : ZMod 5238105468361) ^ (39963573 + 39963573) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 39963573 * (7 : ZMod 5238105468361) ^ 39963573 := by rw [pow_add]
          _ = 5141740966884 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 5238105468361) ^ 159854292 = 4402522629970 := by
        calc
          (7 : ZMod 5238105468361) ^ 159854292 = (7 : ZMod 5238105468361) ^ (79927146 + 79927146) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 79927146 * (7 : ZMod 5238105468361) ^ 79927146 := by rw [pow_add]
          _ = 4402522629970 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 5238105468361) ^ 319708585 = 3823420171153 := by
        calc
          (7 : ZMod 5238105468361) ^ 319708585 = (7 : ZMod 5238105468361) ^ (159854292 + 159854292 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 159854292 * (7 : ZMod 5238105468361) ^ 159854292) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3823420171153 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 5238105468361) ^ 639417171 = 5202970375195 := by
        calc
          (7 : ZMod 5238105468361) ^ 639417171 = (7 : ZMod 5238105468361) ^ (319708585 + 319708585 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 319708585 * (7 : ZMod 5238105468361) ^ 319708585) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5202970375195 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 5238105468361) ^ 1278834342 = 796348185000 := by
        calc
          (7 : ZMod 5238105468361) ^ 1278834342 = (7 : ZMod 5238105468361) ^ (639417171 + 639417171) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 639417171 * (7 : ZMod 5238105468361) ^ 639417171 := by rw [pow_add]
          _ = 796348185000 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 5238105468361) ^ 2557668685 = 3958102178842 := by
        calc
          (7 : ZMod 5238105468361) ^ 2557668685 = (7 : ZMod 5238105468361) ^ (1278834342 + 1278834342 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1278834342 * (7 : ZMod 5238105468361) ^ 1278834342) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3958102178842 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 5238105468361) ^ 5115337371 = 2749698282206 := by
        calc
          (7 : ZMod 5238105468361) ^ 5115337371 = (7 : ZMod 5238105468361) ^ (2557668685 + 2557668685 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 2557668685 * (7 : ZMod 5238105468361) ^ 2557668685) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2749698282206 := by rw [factor_0_31]; decide
      have factor_0_33 : (7 : ZMod 5238105468361) ^ 10230674742 = 3414960039114 := by
        calc
          (7 : ZMod 5238105468361) ^ 10230674742 = (7 : ZMod 5238105468361) ^ (5115337371 + 5115337371) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 5115337371 * (7 : ZMod 5238105468361) ^ 5115337371 := by rw [pow_add]
          _ = 3414960039114 := by rw [factor_0_32]; decide
      have factor_0_34 : (7 : ZMod 5238105468361) ^ 20461349485 = 827002441357 := by
        calc
          (7 : ZMod 5238105468361) ^ 20461349485 = (7 : ZMod 5238105468361) ^ (10230674742 + 10230674742 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 10230674742 * (7 : ZMod 5238105468361) ^ 10230674742) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 827002441357 := by rw [factor_0_33]; decide
      have factor_0_35 : (7 : ZMod 5238105468361) ^ 40922698971 = 3674089022771 := by
        calc
          (7 : ZMod 5238105468361) ^ 40922698971 = (7 : ZMod 5238105468361) ^ (20461349485 + 20461349485 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 20461349485 * (7 : ZMod 5238105468361) ^ 20461349485) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3674089022771 := by rw [factor_0_34]; decide
      have factor_0_36 : (7 : ZMod 5238105468361) ^ 81845397943 = 1000814766964 := by
        calc
          (7 : ZMod 5238105468361) ^ 81845397943 = (7 : ZMod 5238105468361) ^ (40922698971 + 40922698971 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 40922698971 * (7 : ZMod 5238105468361) ^ 40922698971) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1000814766964 := by rw [factor_0_35]; decide
      have factor_0_37 : (7 : ZMod 5238105468361) ^ 163690795886 = 3859497684715 := by
        calc
          (7 : ZMod 5238105468361) ^ 163690795886 = (7 : ZMod 5238105468361) ^ (81845397943 + 81845397943) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 81845397943 * (7 : ZMod 5238105468361) ^ 81845397943 := by rw [pow_add]
          _ = 3859497684715 := by rw [factor_0_36]; decide
      have factor_0_38 : (7 : ZMod 5238105468361) ^ 327381591772 = 2846999696002 := by
        calc
          (7 : ZMod 5238105468361) ^ 327381591772 = (7 : ZMod 5238105468361) ^ (163690795886 + 163690795886) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 163690795886 * (7 : ZMod 5238105468361) ^ 163690795886 := by rw [pow_add]
          _ = 2846999696002 := by rw [factor_0_37]; decide
      have factor_0_39 : (7 : ZMod 5238105468361) ^ 654763183545 = 2384151819450 := by
        calc
          (7 : ZMod 5238105468361) ^ 654763183545 = (7 : ZMod 5238105468361) ^ (327381591772 + 327381591772 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 327381591772 * (7 : ZMod 5238105468361) ^ 327381591772) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2384151819450 := by rw [factor_0_38]; decide
      have factor_0_40 : (7 : ZMod 5238105468361) ^ 1309526367090 = 24688945145 := by
        calc
          (7 : ZMod 5238105468361) ^ 1309526367090 = (7 : ZMod 5238105468361) ^ (654763183545 + 654763183545) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 654763183545 * (7 : ZMod 5238105468361) ^ 654763183545 := by rw [pow_add]
          _ = 24688945145 := by rw [factor_0_39]; decide
      have factor_0_41 : (7 : ZMod 5238105468361) ^ 2619052734180 = 5238105468360 := by
        calc
          (7 : ZMod 5238105468361) ^ 2619052734180 = (7 : ZMod 5238105468361) ^ (1309526367090 + 1309526367090) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1309526367090 * (7 : ZMod 5238105468361) ^ 1309526367090 := by rw [pow_add]
          _ = 5238105468360 := by rw [factor_0_40]; decide
      change (7 : ZMod 5238105468361) ^ 2619052734180 ≠ 1
      rw [factor_0_41]
      decide
    ·
      have factor_1_0 : (7 : ZMod 5238105468361) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 5238105468361) ^ 3 = 343 := by
        calc
          (7 : ZMod 5238105468361) ^ 3 = (7 : ZMod 5238105468361) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1 * (7 : ZMod 5238105468361) ^ 1) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 5238105468361) ^ 6 = 117649 := by
        calc
          (7 : ZMod 5238105468361) ^ 6 = (7 : ZMod 5238105468361) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3 * (7 : ZMod 5238105468361) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 5238105468361) ^ 12 = 13841287201 := by
        calc
          (7 : ZMod 5238105468361) ^ 12 = (7 : ZMod 5238105468361) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 6 * (7 : ZMod 5238105468361) ^ 6 := by rw [pow_add]
          _ = 13841287201 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 5238105468361) ^ 25 = 17834682356 := by
        calc
          (7 : ZMod 5238105468361) ^ 25 = (7 : ZMod 5238105468361) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 12 * (7 : ZMod 5238105468361) ^ 12) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 17834682356 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 5238105468361) ^ 50 = 1617511793315 := by
        calc
          (7 : ZMod 5238105468361) ^ 50 = (7 : ZMod 5238105468361) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 25 * (7 : ZMod 5238105468361) ^ 25 := by rw [pow_add]
          _ = 1617511793315 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 5238105468361) ^ 101 = 4280226647439 := by
        calc
          (7 : ZMod 5238105468361) ^ 101 = (7 : ZMod 5238105468361) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 50 * (7 : ZMod 5238105468361) ^ 50) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4280226647439 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 5238105468361) ^ 203 = 2117663641146 := by
        calc
          (7 : ZMod 5238105468361) ^ 203 = (7 : ZMod 5238105468361) ^ (101 + 101 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 101 * (7 : ZMod 5238105468361) ^ 101) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2117663641146 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 5238105468361) ^ 406 = 2281289608723 := by
        calc
          (7 : ZMod 5238105468361) ^ 406 = (7 : ZMod 5238105468361) ^ (203 + 203) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 203 * (7 : ZMod 5238105468361) ^ 203 := by rw [pow_add]
          _ = 2281289608723 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 5238105468361) ^ 813 = 5130563733411 := by
        calc
          (7 : ZMod 5238105468361) ^ 813 = (7 : ZMod 5238105468361) ^ (406 + 406 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 406 * (7 : ZMod 5238105468361) ^ 406) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5130563733411 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 5238105468361) ^ 1626 = 1010394220748 := by
        calc
          (7 : ZMod 5238105468361) ^ 1626 = (7 : ZMod 5238105468361) ^ (813 + 813) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 813 * (7 : ZMod 5238105468361) ^ 813 := by rw [pow_add]
          _ = 1010394220748 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 5238105468361) ^ 3252 = 2703861755589 := by
        calc
          (7 : ZMod 5238105468361) ^ 3252 = (7 : ZMod 5238105468361) ^ (1626 + 1626) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1626 * (7 : ZMod 5238105468361) ^ 1626 := by rw [pow_add]
          _ = 2703861755589 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 5238105468361) ^ 6504 = 2102401418403 := by
        calc
          (7 : ZMod 5238105468361) ^ 6504 = (7 : ZMod 5238105468361) ^ (3252 + 3252) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3252 * (7 : ZMod 5238105468361) ^ 3252 := by rw [pow_add]
          _ = 2102401418403 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 5238105468361) ^ 13008 = 3076382346157 := by
        calc
          (7 : ZMod 5238105468361) ^ 13008 = (7 : ZMod 5238105468361) ^ (6504 + 6504) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 6504 * (7 : ZMod 5238105468361) ^ 6504 := by rw [pow_add]
          _ = 3076382346157 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 5238105468361) ^ 26017 = 3311418099062 := by
        calc
          (7 : ZMod 5238105468361) ^ 26017 = (7 : ZMod 5238105468361) ^ (13008 + 13008 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 13008 * (7 : ZMod 5238105468361) ^ 13008) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3311418099062 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 5238105468361) ^ 52035 = 4649181118183 := by
        calc
          (7 : ZMod 5238105468361) ^ 52035 = (7 : ZMod 5238105468361) ^ (26017 + 26017 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 26017 * (7 : ZMod 5238105468361) ^ 26017) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4649181118183 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 5238105468361) ^ 104071 = 2510238824295 := by
        calc
          (7 : ZMod 5238105468361) ^ 104071 = (7 : ZMod 5238105468361) ^ (52035 + 52035 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 52035 * (7 : ZMod 5238105468361) ^ 52035) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2510238824295 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 5238105468361) ^ 208143 = 3146245273930 := by
        calc
          (7 : ZMod 5238105468361) ^ 208143 = (7 : ZMod 5238105468361) ^ (104071 + 104071 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 104071 * (7 : ZMod 5238105468361) ^ 104071) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3146245273930 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 5238105468361) ^ 416287 = 416864561786 := by
        calc
          (7 : ZMod 5238105468361) ^ 416287 = (7 : ZMod 5238105468361) ^ (208143 + 208143 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 208143 * (7 : ZMod 5238105468361) ^ 208143) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 416864561786 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 5238105468361) ^ 832574 = 3562446615645 := by
        calc
          (7 : ZMod 5238105468361) ^ 832574 = (7 : ZMod 5238105468361) ^ (416287 + 416287) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 416287 * (7 : ZMod 5238105468361) ^ 416287 := by rw [pow_add]
          _ = 3562446615645 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 5238105468361) ^ 1665148 = 4797999780617 := by
        calc
          (7 : ZMod 5238105468361) ^ 1665148 = (7 : ZMod 5238105468361) ^ (832574 + 832574) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 832574 * (7 : ZMod 5238105468361) ^ 832574 := by rw [pow_add]
          _ = 4797999780617 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 5238105468361) ^ 3330297 = 4821774220494 := by
        calc
          (7 : ZMod 5238105468361) ^ 3330297 = (7 : ZMod 5238105468361) ^ (1665148 + 1665148 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1665148 * (7 : ZMod 5238105468361) ^ 1665148) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4821774220494 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 5238105468361) ^ 6660595 = 2076241529922 := by
        calc
          (7 : ZMod 5238105468361) ^ 6660595 = (7 : ZMod 5238105468361) ^ (3330297 + 3330297 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 3330297 * (7 : ZMod 5238105468361) ^ 3330297) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2076241529922 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 5238105468361) ^ 13321191 = 111761782473 := by
        calc
          (7 : ZMod 5238105468361) ^ 13321191 = (7 : ZMod 5238105468361) ^ (6660595 + 6660595 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 6660595 * (7 : ZMod 5238105468361) ^ 6660595) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 111761782473 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 5238105468361) ^ 26642382 = 436276597564 := by
        calc
          (7 : ZMod 5238105468361) ^ 26642382 = (7 : ZMod 5238105468361) ^ (13321191 + 13321191) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 13321191 * (7 : ZMod 5238105468361) ^ 13321191 := by rw [pow_add]
          _ = 436276597564 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 5238105468361) ^ 53284764 = 4878118558083 := by
        calc
          (7 : ZMod 5238105468361) ^ 53284764 = (7 : ZMod 5238105468361) ^ (26642382 + 26642382) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 26642382 * (7 : ZMod 5238105468361) ^ 26642382 := by rw [pow_add]
          _ = 4878118558083 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 5238105468361) ^ 106569528 = 1692756559190 := by
        calc
          (7 : ZMod 5238105468361) ^ 106569528 = (7 : ZMod 5238105468361) ^ (53284764 + 53284764) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 53284764 * (7 : ZMod 5238105468361) ^ 53284764 := by rw [pow_add]
          _ = 1692756559190 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 5238105468361) ^ 213139057 = 4108446317244 := by
        calc
          (7 : ZMod 5238105468361) ^ 213139057 = (7 : ZMod 5238105468361) ^ (106569528 + 106569528 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 106569528 * (7 : ZMod 5238105468361) ^ 106569528) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4108446317244 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 5238105468361) ^ 426278114 = 3864763693939 := by
        calc
          (7 : ZMod 5238105468361) ^ 426278114 = (7 : ZMod 5238105468361) ^ (213139057 + 213139057) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 213139057 * (7 : ZMod 5238105468361) ^ 213139057 := by rw [pow_add]
          _ = 3864763693939 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 5238105468361) ^ 852556228 = 4941762181477 := by
        calc
          (7 : ZMod 5238105468361) ^ 852556228 = (7 : ZMod 5238105468361) ^ (426278114 + 426278114) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 426278114 * (7 : ZMod 5238105468361) ^ 426278114 := by rw [pow_add]
          _ = 4941762181477 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 5238105468361) ^ 1705112457 = 444646541054 := by
        calc
          (7 : ZMod 5238105468361) ^ 1705112457 = (7 : ZMod 5238105468361) ^ (852556228 + 852556228 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 852556228 * (7 : ZMod 5238105468361) ^ 852556228) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 444646541054 := by rw [factor_1_29]; decide
      have factor_1_31 : (7 : ZMod 5238105468361) ^ 3410224914 = 3788479758024 := by
        calc
          (7 : ZMod 5238105468361) ^ 3410224914 = (7 : ZMod 5238105468361) ^ (1705112457 + 1705112457) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1705112457 * (7 : ZMod 5238105468361) ^ 1705112457 := by rw [pow_add]
          _ = 3788479758024 := by rw [factor_1_30]; decide
      have factor_1_32 : (7 : ZMod 5238105468361) ^ 6820449828 = 3301998342318 := by
        calc
          (7 : ZMod 5238105468361) ^ 6820449828 = (7 : ZMod 5238105468361) ^ (3410224914 + 3410224914) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3410224914 * (7 : ZMod 5238105468361) ^ 3410224914 := by rw [pow_add]
          _ = 3301998342318 := by rw [factor_1_31]; decide
      have factor_1_33 : (7 : ZMod 5238105468361) ^ 13640899657 = 2321692807392 := by
        calc
          (7 : ZMod 5238105468361) ^ 13640899657 = (7 : ZMod 5238105468361) ^ (6820449828 + 6820449828 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 6820449828 * (7 : ZMod 5238105468361) ^ 6820449828) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2321692807392 := by rw [factor_1_32]; decide
      have factor_1_34 : (7 : ZMod 5238105468361) ^ 27281799314 = 2324226883582 := by
        calc
          (7 : ZMod 5238105468361) ^ 27281799314 = (7 : ZMod 5238105468361) ^ (13640899657 + 13640899657) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 13640899657 * (7 : ZMod 5238105468361) ^ 13640899657 := by rw [pow_add]
          _ = 2324226883582 := by rw [factor_1_33]; decide
      have factor_1_35 : (7 : ZMod 5238105468361) ^ 54563598628 = 1761953745691 := by
        calc
          (7 : ZMod 5238105468361) ^ 54563598628 = (7 : ZMod 5238105468361) ^ (27281799314 + 27281799314) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 27281799314 * (7 : ZMod 5238105468361) ^ 27281799314 := by rw [pow_add]
          _ = 1761953745691 := by rw [factor_1_34]; decide
      have factor_1_36 : (7 : ZMod 5238105468361) ^ 109127197257 = 3788147041690 := by
        calc
          (7 : ZMod 5238105468361) ^ 109127197257 = (7 : ZMod 5238105468361) ^ (54563598628 + 54563598628 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 54563598628 * (7 : ZMod 5238105468361) ^ 54563598628) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3788147041690 := by rw [factor_1_35]; decide
      have factor_1_37 : (7 : ZMod 5238105468361) ^ 218254394515 = 1274373837720 := by
        calc
          (7 : ZMod 5238105468361) ^ 218254394515 = (7 : ZMod 5238105468361) ^ (109127197257 + 109127197257 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 109127197257 * (7 : ZMod 5238105468361) ^ 109127197257) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1274373837720 := by rw [factor_1_36]; decide
      have factor_1_38 : (7 : ZMod 5238105468361) ^ 436508789030 = 3370586798989 := by
        calc
          (7 : ZMod 5238105468361) ^ 436508789030 = (7 : ZMod 5238105468361) ^ (218254394515 + 218254394515) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 218254394515 * (7 : ZMod 5238105468361) ^ 218254394515 := by rw [pow_add]
          _ = 3370586798989 := by rw [factor_1_37]; decide
      have factor_1_39 : (7 : ZMod 5238105468361) ^ 873017578060 = 2446037299882 := by
        calc
          (7 : ZMod 5238105468361) ^ 873017578060 = (7 : ZMod 5238105468361) ^ (436508789030 + 436508789030) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 436508789030 * (7 : ZMod 5238105468361) ^ 436508789030 := by rw [pow_add]
          _ = 2446037299882 := by rw [factor_1_38]; decide
      have factor_1_40 : (7 : ZMod 5238105468361) ^ 1746035156120 = 2446037299881 := by
        calc
          (7 : ZMod 5238105468361) ^ 1746035156120 = (7 : ZMod 5238105468361) ^ (873017578060 + 873017578060) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 873017578060 * (7 : ZMod 5238105468361) ^ 873017578060 := by rw [pow_add]
          _ = 2446037299881 := by rw [factor_1_39]; decide
      change (7 : ZMod 5238105468361) ^ 1746035156120 ≠ 1
      rw [factor_1_40]
      decide
    ·
      have factor_2_0 : (7 : ZMod 5238105468361) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 5238105468361) ^ 3 = 343 := by
        calc
          (7 : ZMod 5238105468361) ^ 3 = (7 : ZMod 5238105468361) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1 * (7 : ZMod 5238105468361) ^ 1) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 5238105468361) ^ 7 = 823543 := by
        calc
          (7 : ZMod 5238105468361) ^ 7 = (7 : ZMod 5238105468361) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 3 * (7 : ZMod 5238105468361) ^ 3) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 5238105468361) ^ 15 = 4747561509943 := by
        calc
          (7 : ZMod 5238105468361) ^ 15 = (7 : ZMod 5238105468361) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 7 * (7 : ZMod 5238105468361) ^ 7) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4747561509943 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 5238105468361) ^ 30 = 1175494660715 := by
        calc
          (7 : ZMod 5238105468361) ^ 30 = (7 : ZMod 5238105468361) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 15 * (7 : ZMod 5238105468361) ^ 15 := by rw [pow_add]
          _ = 1175494660715 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 5238105468361) ^ 60 = 2787624235217 := by
        calc
          (7 : ZMod 5238105468361) ^ 60 = (7 : ZMod 5238105468361) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 30 * (7 : ZMod 5238105468361) ^ 30 := by rw [pow_add]
          _ = 2787624235217 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 5238105468361) ^ 121 = 2504546950159 := by
        calc
          (7 : ZMod 5238105468361) ^ 121 = (7 : ZMod 5238105468361) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 60 * (7 : ZMod 5238105468361) ^ 60) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2504546950159 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 5238105468361) ^ 243 = 5030100205271 := by
        calc
          (7 : ZMod 5238105468361) ^ 243 = (7 : ZMod 5238105468361) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 121 * (7 : ZMod 5238105468361) ^ 121) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5030100205271 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 5238105468361) ^ 487 = 5217404785769 := by
        calc
          (7 : ZMod 5238105468361) ^ 487 = (7 : ZMod 5238105468361) ^ (243 + 243 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 243 * (7 : ZMod 5238105468361) ^ 243) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5217404785769 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 5238105468361) ^ 975 = 2390202109787 := by
        calc
          (7 : ZMod 5238105468361) ^ 975 = (7 : ZMod 5238105468361) ^ (487 + 487 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 487 * (7 : ZMod 5238105468361) ^ 487) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2390202109787 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 5238105468361) ^ 1951 = 3814832816104 := by
        calc
          (7 : ZMod 5238105468361) ^ 1951 = (7 : ZMod 5238105468361) ^ (975 + 975 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 975 * (7 : ZMod 5238105468361) ^ 975) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3814832816104 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 5238105468361) ^ 3902 = 3295922146838 := by
        calc
          (7 : ZMod 5238105468361) ^ 3902 = (7 : ZMod 5238105468361) ^ (1951 + 1951) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1951 * (7 : ZMod 5238105468361) ^ 1951 := by rw [pow_add]
          _ = 3295922146838 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 5238105468361) ^ 7805 = 3144943821609 := by
        calc
          (7 : ZMod 5238105468361) ^ 7805 = (7 : ZMod 5238105468361) ^ (3902 + 3902 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 3902 * (7 : ZMod 5238105468361) ^ 3902) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3144943821609 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 5238105468361) ^ 15610 = 3674004978264 := by
        calc
          (7 : ZMod 5238105468361) ^ 15610 = (7 : ZMod 5238105468361) ^ (7805 + 7805) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 7805 * (7 : ZMod 5238105468361) ^ 7805 := by rw [pow_add]
          _ = 3674004978264 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 5238105468361) ^ 31221 = 2395708981456 := by
        calc
          (7 : ZMod 5238105468361) ^ 31221 = (7 : ZMod 5238105468361) ^ (15610 + 15610 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 15610 * (7 : ZMod 5238105468361) ^ 15610) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2395708981456 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 5238105468361) ^ 62443 = 1542179251405 := by
        calc
          (7 : ZMod 5238105468361) ^ 62443 = (7 : ZMod 5238105468361) ^ (31221 + 31221 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 31221 * (7 : ZMod 5238105468361) ^ 31221) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1542179251405 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 5238105468361) ^ 124886 = 3028951273632 := by
        calc
          (7 : ZMod 5238105468361) ^ 124886 = (7 : ZMod 5238105468361) ^ (62443 + 62443) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 62443 * (7 : ZMod 5238105468361) ^ 62443 := by rw [pow_add]
          _ = 3028951273632 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 5238105468361) ^ 249772 = 1777941442769 := by
        calc
          (7 : ZMod 5238105468361) ^ 249772 = (7 : ZMod 5238105468361) ^ (124886 + 124886) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 124886 * (7 : ZMod 5238105468361) ^ 124886 := by rw [pow_add]
          _ = 1777941442769 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 5238105468361) ^ 499544 = 4774399914130 := by
        calc
          (7 : ZMod 5238105468361) ^ 499544 = (7 : ZMod 5238105468361) ^ (249772 + 249772) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 249772 * (7 : ZMod 5238105468361) ^ 249772 := by rw [pow_add]
          _ = 4774399914130 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 5238105468361) ^ 999089 = 2486520199280 := by
        calc
          (7 : ZMod 5238105468361) ^ 999089 = (7 : ZMod 5238105468361) ^ (499544 + 499544 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 499544 * (7 : ZMod 5238105468361) ^ 499544) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2486520199280 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 5238105468361) ^ 1998178 = 821957644460 := by
        calc
          (7 : ZMod 5238105468361) ^ 1998178 = (7 : ZMod 5238105468361) ^ (999089 + 999089) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 999089 * (7 : ZMod 5238105468361) ^ 999089 := by rw [pow_add]
          _ = 821957644460 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 5238105468361) ^ 3996357 = 1481324113142 := by
        calc
          (7 : ZMod 5238105468361) ^ 3996357 = (7 : ZMod 5238105468361) ^ (1998178 + 1998178 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1998178 * (7 : ZMod 5238105468361) ^ 1998178) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1481324113142 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 5238105468361) ^ 7992714 = 1902874549784 := by
        calc
          (7 : ZMod 5238105468361) ^ 7992714 = (7 : ZMod 5238105468361) ^ (3996357 + 3996357) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3996357 * (7 : ZMod 5238105468361) ^ 3996357 := by rw [pow_add]
          _ = 1902874549784 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 5238105468361) ^ 15985429 = 3161227872212 := by
        calc
          (7 : ZMod 5238105468361) ^ 15985429 = (7 : ZMod 5238105468361) ^ (7992714 + 7992714 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 7992714 * (7 : ZMod 5238105468361) ^ 7992714) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3161227872212 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 5238105468361) ^ 31970858 = 4826397454008 := by
        calc
          (7 : ZMod 5238105468361) ^ 31970858 = (7 : ZMod 5238105468361) ^ (15985429 + 15985429) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 15985429 * (7 : ZMod 5238105468361) ^ 15985429 := by rw [pow_add]
          _ = 4826397454008 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 5238105468361) ^ 63941717 = 3842796951418 := by
        calc
          (7 : ZMod 5238105468361) ^ 63941717 = (7 : ZMod 5238105468361) ^ (31970858 + 31970858 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 31970858 * (7 : ZMod 5238105468361) ^ 31970858) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3842796951418 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 5238105468361) ^ 127883434 = 1385662953804 := by
        calc
          (7 : ZMod 5238105468361) ^ 127883434 = (7 : ZMod 5238105468361) ^ (63941717 + 63941717) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 63941717 * (7 : ZMod 5238105468361) ^ 63941717 := by rw [pow_add]
          _ = 1385662953804 := by rw [factor_2_25]; decide
      have factor_2_27 : (7 : ZMod 5238105468361) ^ 255766868 = 4471888744520 := by
        calc
          (7 : ZMod 5238105468361) ^ 255766868 = (7 : ZMod 5238105468361) ^ (127883434 + 127883434) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 127883434 * (7 : ZMod 5238105468361) ^ 127883434 := by rw [pow_add]
          _ = 4471888744520 := by rw [factor_2_26]; decide
      have factor_2_28 : (7 : ZMod 5238105468361) ^ 511533737 = 2115549348660 := by
        calc
          (7 : ZMod 5238105468361) ^ 511533737 = (7 : ZMod 5238105468361) ^ (255766868 + 255766868 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 255766868 * (7 : ZMod 5238105468361) ^ 255766868) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2115549348660 := by rw [factor_2_27]; decide
      have factor_2_29 : (7 : ZMod 5238105468361) ^ 1023067474 = 1317797835720 := by
        calc
          (7 : ZMod 5238105468361) ^ 1023067474 = (7 : ZMod 5238105468361) ^ (511533737 + 511533737) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 511533737 * (7 : ZMod 5238105468361) ^ 511533737 := by rw [pow_add]
          _ = 1317797835720 := by rw [factor_2_28]; decide
      have factor_2_30 : (7 : ZMod 5238105468361) ^ 2046134948 = 534045853514 := by
        calc
          (7 : ZMod 5238105468361) ^ 2046134948 = (7 : ZMod 5238105468361) ^ (1023067474 + 1023067474) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1023067474 * (7 : ZMod 5238105468361) ^ 1023067474 := by rw [pow_add]
          _ = 534045853514 := by rw [factor_2_29]; decide
      have factor_2_31 : (7 : ZMod 5238105468361) ^ 4092269897 = 3796219985769 := by
        calc
          (7 : ZMod 5238105468361) ^ 4092269897 = (7 : ZMod 5238105468361) ^ (2046134948 + 2046134948 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 2046134948 * (7 : ZMod 5238105468361) ^ 2046134948) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3796219985769 := by rw [factor_2_30]; decide
      have factor_2_32 : (7 : ZMod 5238105468361) ^ 8184539794 = 537152795551 := by
        calc
          (7 : ZMod 5238105468361) ^ 8184539794 = (7 : ZMod 5238105468361) ^ (4092269897 + 4092269897) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 4092269897 * (7 : ZMod 5238105468361) ^ 4092269897 := by rw [pow_add]
          _ = 537152795551 := by rw [factor_2_31]; decide
      have factor_2_33 : (7 : ZMod 5238105468361) ^ 16369079588 = 3806960800285 := by
        calc
          (7 : ZMod 5238105468361) ^ 16369079588 = (7 : ZMod 5238105468361) ^ (8184539794 + 8184539794) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 8184539794 * (7 : ZMod 5238105468361) ^ 8184539794 := by rw [pow_add]
          _ = 3806960800285 := by rw [factor_2_32]; decide
      have factor_2_34 : (7 : ZMod 5238105468361) ^ 32738159177 = 1131735089313 := by
        calc
          (7 : ZMod 5238105468361) ^ 32738159177 = (7 : ZMod 5238105468361) ^ (16369079588 + 16369079588 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 16369079588 * (7 : ZMod 5238105468361) ^ 16369079588) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1131735089313 := by rw [factor_2_33]; decide
      have factor_2_35 : (7 : ZMod 5238105468361) ^ 65476318354 = 894642333639 := by
        calc
          (7 : ZMod 5238105468361) ^ 65476318354 = (7 : ZMod 5238105468361) ^ (32738159177 + 32738159177) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 32738159177 * (7 : ZMod 5238105468361) ^ 32738159177 := by rw [pow_add]
          _ = 894642333639 := by rw [factor_2_34]; decide
      have factor_2_36 : (7 : ZMod 5238105468361) ^ 130952636709 = 4513444707395 := by
        calc
          (7 : ZMod 5238105468361) ^ 130952636709 = (7 : ZMod 5238105468361) ^ (65476318354 + 65476318354 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 65476318354 * (7 : ZMod 5238105468361) ^ 65476318354) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4513444707395 := by rw [factor_2_35]; decide
      have factor_2_37 : (7 : ZMod 5238105468361) ^ 261905273418 = 3530024842328 := by
        calc
          (7 : ZMod 5238105468361) ^ 261905273418 = (7 : ZMod 5238105468361) ^ (130952636709 + 130952636709) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 130952636709 * (7 : ZMod 5238105468361) ^ 130952636709 := by rw [pow_add]
          _ = 3530024842328 := by rw [factor_2_36]; decide
      have factor_2_38 : (7 : ZMod 5238105468361) ^ 523810546836 = 1700962655423 := by
        calc
          (7 : ZMod 5238105468361) ^ 523810546836 = (7 : ZMod 5238105468361) ^ (261905273418 + 261905273418) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 261905273418 * (7 : ZMod 5238105468361) ^ 261905273418 := by rw [pow_add]
          _ = 1700962655423 := by rw [factor_2_37]; decide
      have factor_2_39 : (7 : ZMod 5238105468361) ^ 1047621093672 = 2442372978652 := by
        calc
          (7 : ZMod 5238105468361) ^ 1047621093672 = (7 : ZMod 5238105468361) ^ (523810546836 + 523810546836) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 523810546836 * (7 : ZMod 5238105468361) ^ 523810546836 := by rw [pow_add]
          _ = 2442372978652 := by rw [factor_2_38]; decide
      change (7 : ZMod 5238105468361) ^ 1047621093672 ≠ 1
      rw [factor_2_39]
      decide
    ·
      have factor_3_0 : (7 : ZMod 5238105468361) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 5238105468361) ^ 2 = 49 := by
        calc
          (7 : ZMod 5238105468361) ^ 2 = (7 : ZMod 5238105468361) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1 * (7 : ZMod 5238105468361) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 5238105468361) ^ 4 = 2401 := by
        calc
          (7 : ZMod 5238105468361) ^ 4 = (7 : ZMod 5238105468361) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 2 * (7 : ZMod 5238105468361) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 5238105468361) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 5238105468361) ^ 8 = (7 : ZMod 5238105468361) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 4 * (7 : ZMod 5238105468361) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 5238105468361) ^ 17 = 2153873379323 := by
        calc
          (7 : ZMod 5238105468361) ^ 17 = (7 : ZMod 5238105468361) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 8 * (7 : ZMod 5238105468361) ^ 8) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2153873379323 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 5238105468361) ^ 35 = 3643041447674 := by
        calc
          (7 : ZMod 5238105468361) ^ 35 = (7 : ZMod 5238105468361) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 17 * (7 : ZMod 5238105468361) ^ 17) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3643041447674 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 5238105468361) ^ 71 = 1591887011147 := by
        calc
          (7 : ZMod 5238105468361) ^ 71 = (7 : ZMod 5238105468361) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 35 * (7 : ZMod 5238105468361) ^ 35) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1591887011147 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 5238105468361) ^ 143 = 2840876604969 := by
        calc
          (7 : ZMod 5238105468361) ^ 143 = (7 : ZMod 5238105468361) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 71 * (7 : ZMod 5238105468361) ^ 71) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2840876604969 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 5238105468361) ^ 286 = 1846622541543 := by
        calc
          (7 : ZMod 5238105468361) ^ 286 = (7 : ZMod 5238105468361) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 143 * (7 : ZMod 5238105468361) ^ 143 := by rw [pow_add]
          _ = 1846622541543 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 5238105468361) ^ 573 = 588895045662 := by
        calc
          (7 : ZMod 5238105468361) ^ 573 = (7 : ZMod 5238105468361) ^ (286 + 286 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 286 * (7 : ZMod 5238105468361) ^ 286) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 588895045662 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 5238105468361) ^ 1147 = 3068458377207 := by
        calc
          (7 : ZMod 5238105468361) ^ 1147 = (7 : ZMod 5238105468361) ^ (573 + 573 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 573 * (7 : ZMod 5238105468361) ^ 573) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3068458377207 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 5238105468361) ^ 2295 = 1605254040226 := by
        calc
          (7 : ZMod 5238105468361) ^ 2295 = (7 : ZMod 5238105468361) ^ (1147 + 1147 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1147 * (7 : ZMod 5238105468361) ^ 1147) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1605254040226 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 5238105468361) ^ 4591 = 442552865103 := by
        calc
          (7 : ZMod 5238105468361) ^ 4591 = (7 : ZMod 5238105468361) ^ (2295 + 2295 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 2295 * (7 : ZMod 5238105468361) ^ 2295) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 442552865103 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 5238105468361) ^ 9182 = 700290931719 := by
        calc
          (7 : ZMod 5238105468361) ^ 9182 = (7 : ZMod 5238105468361) ^ (4591 + 4591) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 4591 * (7 : ZMod 5238105468361) ^ 4591 := by rw [pow_add]
          _ = 700290931719 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 5238105468361) ^ 18365 = 3611650140674 := by
        calc
          (7 : ZMod 5238105468361) ^ 18365 = (7 : ZMod 5238105468361) ^ (9182 + 9182 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 9182 * (7 : ZMod 5238105468361) ^ 9182) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3611650140674 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 5238105468361) ^ 36731 = 287452386542 := by
        calc
          (7 : ZMod 5238105468361) ^ 36731 = (7 : ZMod 5238105468361) ^ (18365 + 18365 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 18365 * (7 : ZMod 5238105468361) ^ 18365) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 287452386542 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 5238105468361) ^ 73462 = 3003277361654 := by
        calc
          (7 : ZMod 5238105468361) ^ 73462 = (7 : ZMod 5238105468361) ^ (36731 + 36731) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 36731 * (7 : ZMod 5238105468361) ^ 36731 := by rw [pow_add]
          _ = 3003277361654 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 5238105468361) ^ 146924 = 2231881765303 := by
        calc
          (7 : ZMod 5238105468361) ^ 146924 = (7 : ZMod 5238105468361) ^ (73462 + 73462) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 73462 * (7 : ZMod 5238105468361) ^ 73462 := by rw [pow_add]
          _ = 2231881765303 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 5238105468361) ^ 293849 = 4244703062096 := by
        calc
          (7 : ZMod 5238105468361) ^ 293849 = (7 : ZMod 5238105468361) ^ (146924 + 146924 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 146924 * (7 : ZMod 5238105468361) ^ 146924) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4244703062096 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 5238105468361) ^ 587699 = 3367850316776 := by
        calc
          (7 : ZMod 5238105468361) ^ 587699 = (7 : ZMod 5238105468361) ^ (293849 + 293849 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 293849 * (7 : ZMod 5238105468361) ^ 293849) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3367850316776 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 5238105468361) ^ 1175399 = 1400845724246 := by
        calc
          (7 : ZMod 5238105468361) ^ 1175399 = (7 : ZMod 5238105468361) ^ (587699 + 587699 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 587699 * (7 : ZMod 5238105468361) ^ 587699) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1400845724246 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 5238105468361) ^ 2350798 = 542919366333 := by
        calc
          (7 : ZMod 5238105468361) ^ 2350798 = (7 : ZMod 5238105468361) ^ (1175399 + 1175399) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1175399 * (7 : ZMod 5238105468361) ^ 1175399 := by rw [pow_add]
          _ = 542919366333 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 5238105468361) ^ 4701596 = 1744490041564 := by
        calc
          (7 : ZMod 5238105468361) ^ 4701596 = (7 : ZMod 5238105468361) ^ (2350798 + 2350798) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 2350798 * (7 : ZMod 5238105468361) ^ 2350798 := by rw [pow_add]
          _ = 1744490041564 := by rw [factor_3_21]; decide
      have factor_3_23 : (7 : ZMod 5238105468361) ^ 9403193 = 2423116577561 := by
        calc
          (7 : ZMod 5238105468361) ^ 9403193 = (7 : ZMod 5238105468361) ^ (4701596 + 4701596 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 4701596 * (7 : ZMod 5238105468361) ^ 4701596) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2423116577561 := by rw [factor_3_22]; decide
      have factor_3_24 : (7 : ZMod 5238105468361) ^ 18806387 = 5205029447336 := by
        calc
          (7 : ZMod 5238105468361) ^ 18806387 = (7 : ZMod 5238105468361) ^ (9403193 + 9403193 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 9403193 * (7 : ZMod 5238105468361) ^ 9403193) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5205029447336 := by rw [factor_3_23]; decide
      have factor_3_25 : (7 : ZMod 5238105468361) ^ 37612774 = 1596238030465 := by
        calc
          (7 : ZMod 5238105468361) ^ 37612774 = (7 : ZMod 5238105468361) ^ (18806387 + 18806387) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 18806387 * (7 : ZMod 5238105468361) ^ 18806387 := by rw [pow_add]
          _ = 1596238030465 := by rw [factor_3_24]; decide
      have factor_3_26 : (7 : ZMod 5238105468361) ^ 75225549 = 2834883448961 := by
        calc
          (7 : ZMod 5238105468361) ^ 75225549 = (7 : ZMod 5238105468361) ^ (37612774 + 37612774 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 37612774 * (7 : ZMod 5238105468361) ^ 37612774) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2834883448961 := by rw [factor_3_25]; decide
      have factor_3_27 : (7 : ZMod 5238105468361) ^ 150451099 = 3182385647034 := by
        calc
          (7 : ZMod 5238105468361) ^ 150451099 = (7 : ZMod 5238105468361) ^ (75225549 + 75225549 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 75225549 * (7 : ZMod 5238105468361) ^ 75225549) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3182385647034 := by rw [factor_3_26]; decide
      have factor_3_28 : (7 : ZMod 5238105468361) ^ 300902198 = 1224793016303 := by
        calc
          (7 : ZMod 5238105468361) ^ 300902198 = (7 : ZMod 5238105468361) ^ (150451099 + 150451099) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 150451099 * (7 : ZMod 5238105468361) ^ 150451099 := by rw [pow_add]
          _ = 1224793016303 := by rw [factor_3_27]; decide
      have factor_3_29 : (7 : ZMod 5238105468361) ^ 601804396 = 3889623560251 := by
        calc
          (7 : ZMod 5238105468361) ^ 601804396 = (7 : ZMod 5238105468361) ^ (300902198 + 300902198) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 300902198 * (7 : ZMod 5238105468361) ^ 300902198 := by rw [pow_add]
          _ = 3889623560251 := by rw [factor_3_28]; decide
      have factor_3_30 : (7 : ZMod 5238105468361) ^ 1203608793 = 1371100665034 := by
        calc
          (7 : ZMod 5238105468361) ^ 1203608793 = (7 : ZMod 5238105468361) ^ (601804396 + 601804396 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 601804396 * (7 : ZMod 5238105468361) ^ 601804396) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1371100665034 := by rw [factor_3_29]; decide
      have factor_3_31 : (7 : ZMod 5238105468361) ^ 2407217586 = 2881897538372 := by
        calc
          (7 : ZMod 5238105468361) ^ 2407217586 = (7 : ZMod 5238105468361) ^ (1203608793 + 1203608793) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1203608793 * (7 : ZMod 5238105468361) ^ 1203608793 := by rw [pow_add]
          _ = 2881897538372 := by rw [factor_3_30]; decide
      have factor_3_32 : (7 : ZMod 5238105468361) ^ 4814435173 = 74507354448 := by
        calc
          (7 : ZMod 5238105468361) ^ 4814435173 = (7 : ZMod 5238105468361) ^ (2407217586 + 2407217586 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 2407217586 * (7 : ZMod 5238105468361) ^ 2407217586) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 74507354448 := by rw [factor_3_31]; decide
      have factor_3_33 : (7 : ZMod 5238105468361) ^ 9628870346 = 4800956772462 := by
        calc
          (7 : ZMod 5238105468361) ^ 9628870346 = (7 : ZMod 5238105468361) ^ (4814435173 + 4814435173) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 4814435173 * (7 : ZMod 5238105468361) ^ 4814435173 := by rw [pow_add]
          _ = 4800956772462 := by rw [factor_3_32]; decide
      have factor_3_34 : (7 : ZMod 5238105468361) ^ 19257740692 = 2345732815144 := by
        calc
          (7 : ZMod 5238105468361) ^ 19257740692 = (7 : ZMod 5238105468361) ^ (9628870346 + 9628870346) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 9628870346 * (7 : ZMod 5238105468361) ^ 9628870346 := by rw [pow_add]
          _ = 2345732815144 := by rw [factor_3_33]; decide
      have factor_3_35 : (7 : ZMod 5238105468361) ^ 38515481385 = 4825650644264 := by
        calc
          (7 : ZMod 5238105468361) ^ 38515481385 = (7 : ZMod 5238105468361) ^ (19257740692 + 19257740692 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 19257740692 * (7 : ZMod 5238105468361) ^ 19257740692) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4825650644264 := by rw [factor_3_34]; decide
      have factor_3_36 : (7 : ZMod 5238105468361) ^ 77030962770 = 1485587496854 := by
        calc
          (7 : ZMod 5238105468361) ^ 77030962770 = (7 : ZMod 5238105468361) ^ (38515481385 + 38515481385) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 38515481385 * (7 : ZMod 5238105468361) ^ 38515481385 := by rw [pow_add]
          _ = 1485587496854 := by rw [factor_3_35]; decide
      have factor_3_37 : (7 : ZMod 5238105468361) ^ 154061925540 = 2080187060786 := by
        calc
          (7 : ZMod 5238105468361) ^ 154061925540 = (7 : ZMod 5238105468361) ^ (77030962770 + 77030962770) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 77030962770 * (7 : ZMod 5238105468361) ^ 77030962770 := by rw [pow_add]
          _ = 2080187060786 := by rw [factor_3_36]; decide
      have factor_3_38 : (7 : ZMod 5238105468361) ^ 308123851080 = 5132301481180 := by
        calc
          (7 : ZMod 5238105468361) ^ 308123851080 = (7 : ZMod 5238105468361) ^ (154061925540 + 154061925540) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 154061925540 * (7 : ZMod 5238105468361) ^ 154061925540 := by rw [pow_add]
          _ = 5132301481180 := by rw [factor_3_37]; decide
      change (7 : ZMod 5238105468361) ^ 308123851080 ≠ 1
      rw [factor_3_38]
      decide
    ·
      have factor_4_0 : (7 : ZMod 5238105468361) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 5238105468361) ^ 3 = 343 := by
        calc
          (7 : ZMod 5238105468361) ^ 3 = (7 : ZMod 5238105468361) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1 * (7 : ZMod 5238105468361) ^ 1) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 5238105468361) ^ 7 = 823543 := by
        calc
          (7 : ZMod 5238105468361) ^ 7 = (7 : ZMod 5238105468361) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 3 * (7 : ZMod 5238105468361) ^ 3) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 5238105468361) ^ 14 = 678223072849 := by
        calc
          (7 : ZMod 5238105468361) ^ 14 = (7 : ZMod 5238105468361) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 7 * (7 : ZMod 5238105468361) ^ 7 := by rw [pow_add]
          _ = 678223072849 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 5238105468361) ^ 29 = 916228589868 := by
        calc
          (7 : ZMod 5238105468361) ^ 29 = (7 : ZMod 5238105468361) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 14 * (7 : ZMod 5238105468361) ^ 14) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 916228589868 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 5238105468361) ^ 59 = 4888036720769 := by
        calc
          (7 : ZMod 5238105468361) ^ 59 = (7 : ZMod 5238105468361) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 29 * (7 : ZMod 5238105468361) ^ 29) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4888036720769 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 5238105468361) ^ 118 = 1244288891800 := by
        calc
          (7 : ZMod 5238105468361) ^ 118 = (7 : ZMod 5238105468361) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 59 * (7 : ZMod 5238105468361) ^ 59 := by rw [pow_add]
          _ = 1244288891800 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 5238105468361) ^ 237 = 4714333224355 := by
        calc
          (7 : ZMod 5238105468361) ^ 237 = (7 : ZMod 5238105468361) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 118 * (7 : ZMod 5238105468361) ^ 118) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4714333224355 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 5238105468361) ^ 475 = 3741791409589 := by
        calc
          (7 : ZMod 5238105468361) ^ 475 = (7 : ZMod 5238105468361) ^ (237 + 237 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 237 * (7 : ZMod 5238105468361) ^ 237) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3741791409589 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 5238105468361) ^ 951 = 3436402509557 := by
        calc
          (7 : ZMod 5238105468361) ^ 951 = (7 : ZMod 5238105468361) ^ (475 + 475 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 475 * (7 : ZMod 5238105468361) ^ 475) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3436402509557 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 5238105468361) ^ 1903 = 3149780792663 := by
        calc
          (7 : ZMod 5238105468361) ^ 1903 = (7 : ZMod 5238105468361) ^ (951 + 951 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 951 * (7 : ZMod 5238105468361) ^ 951) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3149780792663 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 5238105468361) ^ 3807 = 3770411174300 := by
        calc
          (7 : ZMod 5238105468361) ^ 3807 = (7 : ZMod 5238105468361) ^ (1903 + 1903 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1903 * (7 : ZMod 5238105468361) ^ 1903) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3770411174300 := by rw [factor_4_10]; decide
      have factor_4_12 : (7 : ZMod 5238105468361) ^ 7615 = 2573319534080 := by
        calc
          (7 : ZMod 5238105468361) ^ 7615 = (7 : ZMod 5238105468361) ^ (3807 + 3807 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 3807 * (7 : ZMod 5238105468361) ^ 3807) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2573319534080 := by rw [factor_4_11]; decide
      have factor_4_13 : (7 : ZMod 5238105468361) ^ 15230 = 989518491701 := by
        calc
          (7 : ZMod 5238105468361) ^ 15230 = (7 : ZMod 5238105468361) ^ (7615 + 7615) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 7615 * (7 : ZMod 5238105468361) ^ 7615 := by rw [pow_add]
          _ = 989518491701 := by rw [factor_4_12]; decide
      have factor_4_14 : (7 : ZMod 5238105468361) ^ 30460 = 394173819795 := by
        calc
          (7 : ZMod 5238105468361) ^ 30460 = (7 : ZMod 5238105468361) ^ (15230 + 15230) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 15230 * (7 : ZMod 5238105468361) ^ 15230 := by rw [pow_add]
          _ = 394173819795 := by rw [factor_4_13]; decide
      have factor_4_15 : (7 : ZMod 5238105468361) ^ 60920 = 3878464357335 := by
        calc
          (7 : ZMod 5238105468361) ^ 60920 = (7 : ZMod 5238105468361) ^ (30460 + 30460) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 30460 * (7 : ZMod 5238105468361) ^ 30460 := by rw [pow_add]
          _ = 3878464357335 := by rw [factor_4_14]; decide
      have factor_4_16 : (7 : ZMod 5238105468361) ^ 121840 = 4603466564466 := by
        calc
          (7 : ZMod 5238105468361) ^ 121840 = (7 : ZMod 5238105468361) ^ (60920 + 60920) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 60920 * (7 : ZMod 5238105468361) ^ 60920 := by rw [pow_add]
          _ = 4603466564466 := by rw [factor_4_15]; decide
      have factor_4_17 : (7 : ZMod 5238105468361) ^ 243680 = 1289555652276 := by
        calc
          (7 : ZMod 5238105468361) ^ 243680 = (7 : ZMod 5238105468361) ^ (121840 + 121840) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 121840 * (7 : ZMod 5238105468361) ^ 121840 := by rw [pow_add]
          _ = 1289555652276 := by rw [factor_4_16]; decide
      have factor_4_18 : (7 : ZMod 5238105468361) ^ 487360 = 2598765115552 := by
        calc
          (7 : ZMod 5238105468361) ^ 487360 = (7 : ZMod 5238105468361) ^ (243680 + 243680) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 243680 * (7 : ZMod 5238105468361) ^ 243680 := by rw [pow_add]
          _ = 2598765115552 := by rw [factor_4_17]; decide
      have factor_4_19 : (7 : ZMod 5238105468361) ^ 974721 = 3098838277643 := by
        calc
          (7 : ZMod 5238105468361) ^ 974721 = (7 : ZMod 5238105468361) ^ (487360 + 487360 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 487360 * (7 : ZMod 5238105468361) ^ 487360) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3098838277643 := by rw [factor_4_18]; decide
      have factor_4_20 : (7 : ZMod 5238105468361) ^ 1949442 = 527386034 := by
        calc
          (7 : ZMod 5238105468361) ^ 1949442 = (7 : ZMod 5238105468361) ^ (974721 + 974721) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 974721 * (7 : ZMod 5238105468361) ^ 974721 := by rw [pow_add]
          _ = 527386034 := by rw [factor_4_19]; decide
      have factor_4_21 : (7 : ZMod 5238105468361) ^ 3898885 = 780472644002 := by
        calc
          (7 : ZMod 5238105468361) ^ 3898885 = (7 : ZMod 5238105468361) ^ (1949442 + 1949442 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1949442 * (7 : ZMod 5238105468361) ^ 1949442) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 780472644002 := by rw [factor_4_20]; decide
      have factor_4_22 : (7 : ZMod 5238105468361) ^ 7797770 = 2211768526550 := by
        calc
          (7 : ZMod 5238105468361) ^ 7797770 = (7 : ZMod 5238105468361) ^ (3898885 + 3898885) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3898885 * (7 : ZMod 5238105468361) ^ 3898885 := by rw [pow_add]
          _ = 2211768526550 := by rw [factor_4_21]; decide
      have factor_4_23 : (7 : ZMod 5238105468361) ^ 15595540 = 4020676993044 := by
        calc
          (7 : ZMod 5238105468361) ^ 15595540 = (7 : ZMod 5238105468361) ^ (7797770 + 7797770) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 7797770 * (7 : ZMod 5238105468361) ^ 7797770 := by rw [pow_add]
          _ = 4020676993044 := by rw [factor_4_22]; decide
      have factor_4_24 : (7 : ZMod 5238105468361) ^ 31191081 = 268843830438 := by
        calc
          (7 : ZMod 5238105468361) ^ 31191081 = (7 : ZMod 5238105468361) ^ (15595540 + 15595540 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 15595540 * (7 : ZMod 5238105468361) ^ 15595540) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 268843830438 := by rw [factor_4_23]; decide
      have factor_4_25 : (7 : ZMod 5238105468361) ^ 62382163 = 3164938780303 := by
        calc
          (7 : ZMod 5238105468361) ^ 62382163 = (7 : ZMod 5238105468361) ^ (31191081 + 31191081 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 31191081 * (7 : ZMod 5238105468361) ^ 31191081) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3164938780303 := by rw [factor_4_24]; decide
      have factor_4_26 : (7 : ZMod 5238105468361) ^ 124764326 = 798616469515 := by
        calc
          (7 : ZMod 5238105468361) ^ 124764326 = (7 : ZMod 5238105468361) ^ (62382163 + 62382163) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 62382163 * (7 : ZMod 5238105468361) ^ 62382163 := by rw [pow_add]
          _ = 798616469515 := by rw [factor_4_25]; decide
      have factor_4_27 : (7 : ZMod 5238105468361) ^ 249528652 = 670549834851 := by
        calc
          (7 : ZMod 5238105468361) ^ 249528652 = (7 : ZMod 5238105468361) ^ (124764326 + 124764326) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 124764326 * (7 : ZMod 5238105468361) ^ 124764326 := by rw [pow_add]
          _ = 670549834851 := by rw [factor_4_26]; decide
      have factor_4_28 : (7 : ZMod 5238105468361) ^ 499057304 = 672005375754 := by
        calc
          (7 : ZMod 5238105468361) ^ 499057304 = (7 : ZMod 5238105468361) ^ (249528652 + 249528652) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 249528652 * (7 : ZMod 5238105468361) ^ 249528652 := by rw [pow_add]
          _ = 672005375754 := by rw [factor_4_27]; decide
      have factor_4_29 : (7 : ZMod 5238105468361) ^ 998114609 = 4911124949890 := by
        calc
          (7 : ZMod 5238105468361) ^ 998114609 = (7 : ZMod 5238105468361) ^ (499057304 + 499057304 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 499057304 * (7 : ZMod 5238105468361) ^ 499057304) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4911124949890 := by rw [factor_4_28]; decide
      have factor_4_30 : (7 : ZMod 5238105468361) ^ 1996229218 = 3283009384289 := by
        calc
          (7 : ZMod 5238105468361) ^ 1996229218 = (7 : ZMod 5238105468361) ^ (998114609 + 998114609) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 998114609 * (7 : ZMod 5238105468361) ^ 998114609 := by rw [pow_add]
          _ = 3283009384289 := by rw [factor_4_29]; decide
      have factor_4_31 : (7 : ZMod 5238105468361) ^ 3992458436 = 3370295198727 := by
        calc
          (7 : ZMod 5238105468361) ^ 3992458436 = (7 : ZMod 5238105468361) ^ (1996229218 + 1996229218) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1996229218 * (7 : ZMod 5238105468361) ^ 1996229218 := by rw [pow_add]
          _ = 3370295198727 := by rw [factor_4_30]; decide
      have factor_4_32 : (7 : ZMod 5238105468361) ^ 7984916872 = 2412942008387 := by
        calc
          (7 : ZMod 5238105468361) ^ 7984916872 = (7 : ZMod 5238105468361) ^ (3992458436 + 3992458436) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3992458436 * (7 : ZMod 5238105468361) ^ 3992458436 := by rw [pow_add]
          _ = 2412942008387 := by rw [factor_4_31]; decide
      have factor_4_33 : (7 : ZMod 5238105468361) ^ 15969833745 = 2743137251157 := by
        calc
          (7 : ZMod 5238105468361) ^ 15969833745 = (7 : ZMod 5238105468361) ^ (7984916872 + 7984916872 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 7984916872 * (7 : ZMod 5238105468361) ^ 7984916872) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2743137251157 := by rw [factor_4_32]; decide
      have factor_4_34 : (7 : ZMod 5238105468361) ^ 31939667490 = 505906479523 := by
        calc
          (7 : ZMod 5238105468361) ^ 31939667490 = (7 : ZMod 5238105468361) ^ (15969833745 + 15969833745) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 15969833745 * (7 : ZMod 5238105468361) ^ 15969833745 := by rw [pow_add]
          _ = 505906479523 := by rw [factor_4_33]; decide
      have factor_4_35 : (7 : ZMod 5238105468361) ^ 63879334980 = 3572795847205 := by
        calc
          (7 : ZMod 5238105468361) ^ 63879334980 = (7 : ZMod 5238105468361) ^ (31939667490 + 31939667490) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 31939667490 * (7 : ZMod 5238105468361) ^ 31939667490 := by rw [pow_add]
          _ = 3572795847205 := by rw [factor_4_34]; decide
      have factor_4_36 : (7 : ZMod 5238105468361) ^ 127758669960 = 1573781112857 := by
        calc
          (7 : ZMod 5238105468361) ^ 127758669960 = (7 : ZMod 5238105468361) ^ (63879334980 + 63879334980) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 63879334980 * (7 : ZMod 5238105468361) ^ 63879334980 := by rw [pow_add]
          _ = 1573781112857 := by rw [factor_4_35]; decide
      change (7 : ZMod 5238105468361) ^ 127758669960 ≠ 1
      rw [factor_4_36]
      decide
    ·
      have factor_5_0 : (7 : ZMod 5238105468361) ^ 1 = 7 := by norm_num
      have factor_5_1 : (7 : ZMod 5238105468361) ^ 3 = 343 := by
        calc
          (7 : ZMod 5238105468361) ^ 3 = (7 : ZMod 5238105468361) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1 * (7 : ZMod 5238105468361) ^ 1) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_5_0]; decide
      have factor_5_2 : (7 : ZMod 5238105468361) ^ 6 = 117649 := by
        calc
          (7 : ZMod 5238105468361) ^ 6 = (7 : ZMod 5238105468361) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3 * (7 : ZMod 5238105468361) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_5_1]; decide
      have factor_5_3 : (7 : ZMod 5238105468361) ^ 12 = 13841287201 := by
        calc
          (7 : ZMod 5238105468361) ^ 12 = (7 : ZMod 5238105468361) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 6 * (7 : ZMod 5238105468361) ^ 6 := by rw [pow_add]
          _ = 13841287201 := by rw [factor_5_2]; decide
      have factor_5_4 : (7 : ZMod 5238105468361) ^ 25 = 17834682356 := by
        calc
          (7 : ZMod 5238105468361) ^ 25 = (7 : ZMod 5238105468361) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 12 * (7 : ZMod 5238105468361) ^ 12) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 17834682356 := by rw [factor_5_3]; decide
      have factor_5_5 : (7 : ZMod 5238105468361) ^ 51 = 846371616483 := by
        calc
          (7 : ZMod 5238105468361) ^ 51 = (7 : ZMod 5238105468361) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 25 * (7 : ZMod 5238105468361) ^ 25) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 846371616483 := by rw [factor_5_4]; decide
      have factor_5_6 : (7 : ZMod 5238105468361) ^ 102 = 3771059190268 := by
        calc
          (7 : ZMod 5238105468361) ^ 102 = (7 : ZMod 5238105468361) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 51 * (7 : ZMod 5238105468361) ^ 51 := by rw [pow_add]
          _ = 3771059190268 := by rw [factor_5_5]; decide
      have factor_5_7 : (7 : ZMod 5238105468361) ^ 204 = 4347434551300 := by
        calc
          (7 : ZMod 5238105468361) ^ 204 = (7 : ZMod 5238105468361) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 102 * (7 : ZMod 5238105468361) ^ 102 := by rw [pow_add]
          _ = 4347434551300 := by rw [factor_5_6]; decide
      have factor_5_8 : (7 : ZMod 5238105468361) ^ 408 = 1782975991846 := by
        calc
          (7 : ZMod 5238105468361) ^ 408 = (7 : ZMod 5238105468361) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 204 * (7 : ZMod 5238105468361) ^ 204 := by rw [pow_add]
          _ = 1782975991846 := by rw [factor_5_7]; decide
      have factor_5_9 : (7 : ZMod 5238105468361) ^ 817 = 3697567803100 := by
        calc
          (7 : ZMod 5238105468361) ^ 817 = (7 : ZMod 5238105468361) ^ (408 + 408 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 408 * (7 : ZMod 5238105468361) ^ 408) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3697567803100 := by rw [factor_5_8]; decide
      have factor_5_10 : (7 : ZMod 5238105468361) ^ 1634 = 714399542758 := by
        calc
          (7 : ZMod 5238105468361) ^ 1634 = (7 : ZMod 5238105468361) ^ (817 + 817) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 817 * (7 : ZMod 5238105468361) ^ 817 := by rw [pow_add]
          _ = 714399542758 := by rw [factor_5_9]; decide
      have factor_5_11 : (7 : ZMod 5238105468361) ^ 3269 = 3282957278641 := by
        calc
          (7 : ZMod 5238105468361) ^ 3269 = (7 : ZMod 5238105468361) ^ (1634 + 1634 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1634 * (7 : ZMod 5238105468361) ^ 1634) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3282957278641 := by rw [factor_5_10]; decide
      have factor_5_12 : (7 : ZMod 5238105468361) ^ 6538 = 1931288276371 := by
        calc
          (7 : ZMod 5238105468361) ^ 6538 = (7 : ZMod 5238105468361) ^ (3269 + 3269) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3269 * (7 : ZMod 5238105468361) ^ 3269 := by rw [pow_add]
          _ = 1931288276371 := by rw [factor_5_11]; decide
      have factor_5_13 : (7 : ZMod 5238105468361) ^ 13077 = 3612863316968 := by
        calc
          (7 : ZMod 5238105468361) ^ 13077 = (7 : ZMod 5238105468361) ^ (6538 + 6538 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 6538 * (7 : ZMod 5238105468361) ^ 6538) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3612863316968 := by rw [factor_5_12]; decide
      have factor_5_14 : (7 : ZMod 5238105468361) ^ 26154 = 2871948683443 := by
        calc
          (7 : ZMod 5238105468361) ^ 26154 = (7 : ZMod 5238105468361) ^ (13077 + 13077) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 13077 * (7 : ZMod 5238105468361) ^ 13077 := by rw [pow_add]
          _ = 2871948683443 := by rw [factor_5_13]; decide
      have factor_5_15 : (7 : ZMod 5238105468361) ^ 52308 = 5154312785418 := by
        calc
          (7 : ZMod 5238105468361) ^ 52308 = (7 : ZMod 5238105468361) ^ (26154 + 26154) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 26154 * (7 : ZMod 5238105468361) ^ 26154 := by rw [pow_add]
          _ = 5154312785418 := by rw [factor_5_14]; decide
      have factor_5_16 : (7 : ZMod 5238105468361) ^ 104616 = 2502484391100 := by
        calc
          (7 : ZMod 5238105468361) ^ 104616 = (7 : ZMod 5238105468361) ^ (52308 + 52308) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 52308 * (7 : ZMod 5238105468361) ^ 52308 := by rw [pow_add]
          _ = 2502484391100 := by rw [factor_5_15]; decide
      have factor_5_17 : (7 : ZMod 5238105468361) ^ 209233 = 1160174812820 := by
        calc
          (7 : ZMod 5238105468361) ^ 209233 = (7 : ZMod 5238105468361) ^ (104616 + 104616 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 104616 * (7 : ZMod 5238105468361) ^ 104616) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1160174812820 := by rw [factor_5_16]; decide
      have factor_5_18 : (7 : ZMod 5238105468361) ^ 418466 = 2216189399276 := by
        calc
          (7 : ZMod 5238105468361) ^ 418466 = (7 : ZMod 5238105468361) ^ (209233 + 209233) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 209233 * (7 : ZMod 5238105468361) ^ 209233 := by rw [pow_add]
          _ = 2216189399276 := by rw [factor_5_17]; decide
      have factor_5_19 : (7 : ZMod 5238105468361) ^ 836933 = 2347532716928 := by
        calc
          (7 : ZMod 5238105468361) ^ 836933 = (7 : ZMod 5238105468361) ^ (418466 + 418466 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 418466 * (7 : ZMod 5238105468361) ^ 418466) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2347532716928 := by rw [factor_5_18]; decide
      have factor_5_20 : (7 : ZMod 5238105468361) ^ 1673866 = 4204811452781 := by
        calc
          (7 : ZMod 5238105468361) ^ 1673866 = (7 : ZMod 5238105468361) ^ (836933 + 836933) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 836933 * (7 : ZMod 5238105468361) ^ 836933 := by rw [pow_add]
          _ = 4204811452781 := by rw [factor_5_19]; decide
      have factor_5_21 : (7 : ZMod 5238105468361) ^ 3347733 = 3762950359589 := by
        calc
          (7 : ZMod 5238105468361) ^ 3347733 = (7 : ZMod 5238105468361) ^ (1673866 + 1673866 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1673866 * (7 : ZMod 5238105468361) ^ 1673866) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 3762950359589 := by rw [factor_5_20]; decide
      have factor_5_22 : (7 : ZMod 5238105468361) ^ 6695467 = 2544019227506 := by
        calc
          (7 : ZMod 5238105468361) ^ 6695467 = (7 : ZMod 5238105468361) ^ (3347733 + 3347733 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 3347733 * (7 : ZMod 5238105468361) ^ 3347733) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2544019227506 := by rw [factor_5_21]; decide
      have factor_5_23 : (7 : ZMod 5238105468361) ^ 13390935 = 369924815556 := by
        calc
          (7 : ZMod 5238105468361) ^ 13390935 = (7 : ZMod 5238105468361) ^ (6695467 + 6695467 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 6695467 * (7 : ZMod 5238105468361) ^ 6695467) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 369924815556 := by rw [factor_5_22]; decide
      have factor_5_24 : (7 : ZMod 5238105468361) ^ 26781871 = 4666457415522 := by
        calc
          (7 : ZMod 5238105468361) ^ 26781871 = (7 : ZMod 5238105468361) ^ (13390935 + 13390935 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 13390935 * (7 : ZMod 5238105468361) ^ 13390935) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4666457415522 := by rw [factor_5_23]; decide
      have factor_5_25 : (7 : ZMod 5238105468361) ^ 53563742 = 2167465307176 := by
        calc
          (7 : ZMod 5238105468361) ^ 53563742 = (7 : ZMod 5238105468361) ^ (26781871 + 26781871) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 26781871 * (7 : ZMod 5238105468361) ^ 26781871 := by rw [pow_add]
          _ = 2167465307176 := by rw [factor_5_24]; decide
      have factor_5_26 : (7 : ZMod 5238105468361) ^ 107127484 = 1929146753960 := by
        calc
          (7 : ZMod 5238105468361) ^ 107127484 = (7 : ZMod 5238105468361) ^ (53563742 + 53563742) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 53563742 * (7 : ZMod 5238105468361) ^ 53563742 := by rw [pow_add]
          _ = 1929146753960 := by rw [factor_5_25]; decide
      have factor_5_27 : (7 : ZMod 5238105468361) ^ 214254968 = 1397542218387 := by
        calc
          (7 : ZMod 5238105468361) ^ 214254968 = (7 : ZMod 5238105468361) ^ (107127484 + 107127484) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 107127484 * (7 : ZMod 5238105468361) ^ 107127484 := by rw [pow_add]
          _ = 1397542218387 := by rw [factor_5_26]; decide
      have factor_5_28 : (7 : ZMod 5238105468361) ^ 428509936 = 272089336345 := by
        calc
          (7 : ZMod 5238105468361) ^ 428509936 = (7 : ZMod 5238105468361) ^ (214254968 + 214254968) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 214254968 * (7 : ZMod 5238105468361) ^ 214254968 := by rw [pow_add]
          _ = 272089336345 := by rw [factor_5_27]; decide
      have factor_5_29 : (7 : ZMod 5238105468361) ^ 857019873 = 266114917882 := by
        calc
          (7 : ZMod 5238105468361) ^ 857019873 = (7 : ZMod 5238105468361) ^ (428509936 + 428509936 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 428509936 * (7 : ZMod 5238105468361) ^ 428509936) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 266114917882 := by rw [factor_5_28]; decide
      have factor_5_30 : (7 : ZMod 5238105468361) ^ 1714039747 = 893988224731 := by
        calc
          (7 : ZMod 5238105468361) ^ 1714039747 = (7 : ZMod 5238105468361) ^ (857019873 + 857019873 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 857019873 * (7 : ZMod 5238105468361) ^ 857019873) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 893988224731 := by rw [factor_5_29]; decide
      have factor_5_31 : (7 : ZMod 5238105468361) ^ 3428079495 = 2334821838247 := by
        calc
          (7 : ZMod 5238105468361) ^ 3428079495 = (7 : ZMod 5238105468361) ^ (1714039747 + 1714039747 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1714039747 * (7 : ZMod 5238105468361) ^ 1714039747) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2334821838247 := by rw [factor_5_30]; decide
      have factor_5_32 : (7 : ZMod 5238105468361) ^ 6856158990 = 3034944377605 := by
        calc
          (7 : ZMod 5238105468361) ^ 6856158990 = (7 : ZMod 5238105468361) ^ (3428079495 + 3428079495) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3428079495 * (7 : ZMod 5238105468361) ^ 3428079495 := by rw [pow_add]
          _ = 3034944377605 := by rw [factor_5_31]; decide
      have factor_5_33 : (7 : ZMod 5238105468361) ^ 13712317980 = 488030981768 := by
        calc
          (7 : ZMod 5238105468361) ^ 13712317980 = (7 : ZMod 5238105468361) ^ (6856158990 + 6856158990) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 6856158990 * (7 : ZMod 5238105468361) ^ 6856158990 := by rw [pow_add]
          _ = 488030981768 := by rw [factor_5_32]; decide
      have factor_5_34 : (7 : ZMod 5238105468361) ^ 27424635960 = 3782786449232 := by
        calc
          (7 : ZMod 5238105468361) ^ 27424635960 = (7 : ZMod 5238105468361) ^ (13712317980 + 13712317980) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 13712317980 * (7 : ZMod 5238105468361) ^ 13712317980 := by rw [pow_add]
          _ = 3782786449232 := by rw [factor_5_33]; decide
      change (7 : ZMod 5238105468361) ^ 27424635960 ≠ 1
      rw [factor_5_34]
      decide
    ·
      have factor_6_0 : (7 : ZMod 5238105468361) ^ 1 = 7 := by norm_num
      have factor_6_1 : (7 : ZMod 5238105468361) ^ 3 = 343 := by
        calc
          (7 : ZMod 5238105468361) ^ 3 = (7 : ZMod 5238105468361) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 1 * (7 : ZMod 5238105468361) ^ 1) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_6_0]; decide
      have factor_6_2 : (7 : ZMod 5238105468361) ^ 7 = 823543 := by
        calc
          (7 : ZMod 5238105468361) ^ 7 = (7 : ZMod 5238105468361) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 3 * (7 : ZMod 5238105468361) ^ 3) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_6_1]; decide
      have factor_6_3 : (7 : ZMod 5238105468361) ^ 15 = 4747561509943 := by
        calc
          (7 : ZMod 5238105468361) ^ 15 = (7 : ZMod 5238105468361) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 7 * (7 : ZMod 5238105468361) ^ 7) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4747561509943 := by rw [factor_6_2]; decide
      have factor_6_4 : (7 : ZMod 5238105468361) ^ 30 = 1175494660715 := by
        calc
          (7 : ZMod 5238105468361) ^ 30 = (7 : ZMod 5238105468361) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 15 * (7 : ZMod 5238105468361) ^ 15 := by rw [pow_add]
          _ = 1175494660715 := by rw [factor_6_3]; decide
      have factor_6_5 : (7 : ZMod 5238105468361) ^ 60 = 2787624235217 := by
        calc
          (7 : ZMod 5238105468361) ^ 60 = (7 : ZMod 5238105468361) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 30 * (7 : ZMod 5238105468361) ^ 30 := by rw [pow_add]
          _ = 2787624235217 := by rw [factor_6_4]; decide
      have factor_6_6 : (7 : ZMod 5238105468361) ^ 121 = 2504546950159 := by
        calc
          (7 : ZMod 5238105468361) ^ 121 = (7 : ZMod 5238105468361) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 60 * (7 : ZMod 5238105468361) ^ 60) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2504546950159 := by rw [factor_6_5]; decide
      have factor_6_7 : (7 : ZMod 5238105468361) ^ 243 = 5030100205271 := by
        calc
          (7 : ZMod 5238105468361) ^ 243 = (7 : ZMod 5238105468361) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 121 * (7 : ZMod 5238105468361) ^ 121) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5030100205271 := by rw [factor_6_6]; decide
      have factor_6_8 : (7 : ZMod 5238105468361) ^ 487 = 5217404785769 := by
        calc
          (7 : ZMod 5238105468361) ^ 487 = (7 : ZMod 5238105468361) ^ (243 + 243 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 243 * (7 : ZMod 5238105468361) ^ 243) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5217404785769 := by rw [factor_6_7]; decide
      have factor_6_9 : (7 : ZMod 5238105468361) ^ 975 = 2390202109787 := by
        calc
          (7 : ZMod 5238105468361) ^ 975 = (7 : ZMod 5238105468361) ^ (487 + 487 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 487 * (7 : ZMod 5238105468361) ^ 487) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 2390202109787 := by rw [factor_6_8]; decide
      have factor_6_10 : (7 : ZMod 5238105468361) ^ 1950 = 3538179241364 := by
        calc
          (7 : ZMod 5238105468361) ^ 1950 = (7 : ZMod 5238105468361) ^ (975 + 975) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 975 * (7 : ZMod 5238105468361) ^ 975 := by rw [pow_add]
          _ = 3538179241364 := by rw [factor_6_9]; decide
      have factor_6_11 : (7 : ZMod 5238105468361) ^ 3900 = 5091568962445 := by
        calc
          (7 : ZMod 5238105468361) ^ 3900 = (7 : ZMod 5238105468361) ^ (1950 + 1950) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1950 * (7 : ZMod 5238105468361) ^ 1950 := by rw [pow_add]
          _ = 5091568962445 := by rw [factor_6_10]; decide
      have factor_6_12 : (7 : ZMod 5238105468361) ^ 7800 = 3633855929044 := by
        calc
          (7 : ZMod 5238105468361) ^ 7800 = (7 : ZMod 5238105468361) ^ (3900 + 3900) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3900 * (7 : ZMod 5238105468361) ^ 3900 := by rw [pow_add]
          _ = 3633855929044 := by rw [factor_6_11]; decide
      have factor_6_13 : (7 : ZMod 5238105468361) ^ 15600 = 4382071554838 := by
        calc
          (7 : ZMod 5238105468361) ^ 15600 = (7 : ZMod 5238105468361) ^ (7800 + 7800) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 7800 * (7 : ZMod 5238105468361) ^ 7800 := by rw [pow_add]
          _ = 4382071554838 := by rw [factor_6_12]; decide
      have factor_6_14 : (7 : ZMod 5238105468361) ^ 31201 = 4127791813883 := by
        calc
          (7 : ZMod 5238105468361) ^ 31201 = (7 : ZMod 5238105468361) ^ (15600 + 15600 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 15600 * (7 : ZMod 5238105468361) ^ 15600) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 4127791813883 := by rw [factor_6_13]; decide
      have factor_6_15 : (7 : ZMod 5238105468361) ^ 62403 = 5004282835116 := by
        calc
          (7 : ZMod 5238105468361) ^ 62403 = (7 : ZMod 5238105468361) ^ (31201 + 31201 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 31201 * (7 : ZMod 5238105468361) ^ 31201) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5004282835116 := by rw [factor_6_14]; decide
      have factor_6_16 : (7 : ZMod 5238105468361) ^ 124806 = 1025852141096 := by
        calc
          (7 : ZMod 5238105468361) ^ 124806 = (7 : ZMod 5238105468361) ^ (62403 + 62403) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 62403 * (7 : ZMod 5238105468361) ^ 62403 := by rw [pow_add]
          _ = 1025852141096 := by rw [factor_6_15]; decide
      have factor_6_17 : (7 : ZMod 5238105468361) ^ 249613 = 1813609993311 := by
        calc
          (7 : ZMod 5238105468361) ^ 249613 = (7 : ZMod 5238105468361) ^ (124806 + 124806 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 124806 * (7 : ZMod 5238105468361) ^ 124806) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 1813609993311 := by rw [factor_6_16]; decide
      have factor_6_18 : (7 : ZMod 5238105468361) ^ 499226 = 4196486237564 := by
        calc
          (7 : ZMod 5238105468361) ^ 499226 = (7 : ZMod 5238105468361) ^ (249613 + 249613) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 249613 * (7 : ZMod 5238105468361) ^ 249613 := by rw [pow_add]
          _ = 4196486237564 := by rw [factor_6_17]; decide
      have factor_6_19 : (7 : ZMod 5238105468361) ^ 998452 = 2838401812883 := by
        calc
          (7 : ZMod 5238105468361) ^ 998452 = (7 : ZMod 5238105468361) ^ (499226 + 499226) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 499226 * (7 : ZMod 5238105468361) ^ 499226 := by rw [pow_add]
          _ = 2838401812883 := by rw [factor_6_18]; decide
      have factor_6_20 : (7 : ZMod 5238105468361) ^ 1996905 = 5067663423319 := by
        calc
          (7 : ZMod 5238105468361) ^ 1996905 = (7 : ZMod 5238105468361) ^ (998452 + 998452 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = ((7 : ZMod 5238105468361) ^ 998452 * (7 : ZMod 5238105468361) ^ 998452) * (7 : ZMod 5238105468361) := by rw [pow_succ, pow_add]
          _ = 5067663423319 := by rw [factor_6_19]; decide
      have factor_6_21 : (7 : ZMod 5238105468361) ^ 3993810 = 4461020303063 := by
        calc
          (7 : ZMod 5238105468361) ^ 3993810 = (7 : ZMod 5238105468361) ^ (1996905 + 1996905) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 1996905 * (7 : ZMod 5238105468361) ^ 1996905 := by rw [pow_add]
          _ = 4461020303063 := by rw [factor_6_20]; decide
      have factor_6_22 : (7 : ZMod 5238105468361) ^ 7987620 = 5232453048526 := by
        calc
          (7 : ZMod 5238105468361) ^ 7987620 = (7 : ZMod 5238105468361) ^ (3993810 + 3993810) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 3993810 * (7 : ZMod 5238105468361) ^ 3993810 := by rw [pow_add]
          _ = 5232453048526 := by rw [factor_6_21]; decide
      have factor_6_23 : (7 : ZMod 5238105468361) ^ 15975240 = 4734411634281 := by
        calc
          (7 : ZMod 5238105468361) ^ 15975240 = (7 : ZMod 5238105468361) ^ (7987620 + 7987620) :=
            congrArg (fun n : ℕ => (7 : ZMod 5238105468361) ^ n) (by norm_num)
          _ = (7 : ZMod 5238105468361) ^ 7987620 * (7 : ZMod 5238105468361) ^ 7987620 := by rw [pow_add]
          _ = 4734411634281 := by rw [factor_6_22]; decide
      change (7 : ZMod 5238105468361) ^ 15975240 ≠ 1
      rw [factor_6_23]
      decide

#print axioms prime_lucas_5238105468361

end TotientTailPeriodKiller
end Erdos249257
